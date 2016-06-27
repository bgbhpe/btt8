/*
 * Copyright (C) 2016 Hewlett Packard Enterprise Development LP
 * 
 * Based on concepts used in the Linux kernel (drivers/nvdimm/btt*)
 * and the NVML's libpmemblk (http://pmem.io/).
 * 
 * This program is free software; you can redistribute it and/or
 * modify it under the terms of the GNU General Public License,
 * version 2 as published by the Free Software Foundation.
 * 
 * This program is distributed in the hope that it will be useful,
 * but WITHOUT ANY WARRANTY; without even the implied warranty of
 * MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
 * GNU General Public License for more details.
 * 
 * You should have received a copy of the GNU General Public
 * License along with this program; if not, write to the Free
 * Software Foundation, Inc., 59 Temple Place, Suite 330,
 * Boston, MA 02111-1307 USA
 */


#include <linux/init.h>
#include <linux/module.h>
#include <linux/fs.h>
#include <linux/genhd.h>
#include <linux/blkdev.h>
#include <linux/bio.h>
#include <linux/vmalloc.h>
#include <linux/pmem.h>




typedef u64   btt8_u64_t;


typedef struct btt8   btt8_t;
struct kbtt8_disk {
	struct block_device*    d_bdev;
	struct gendisk*         d_gd;
	struct request_queue*   d_queue;
	spinlock_t              d_spinlock;
	u64                     d_refcount;

	int                     d_id;
	char                    d_name[8];
	btt8_t*                 d_btt;
	u64                     d_bsize;
	u64                     d_nlanes;
	u64*                    d_lanes;
};


#define btt8_malloc(_c, _len)  vmalloc(_len)
#define btt8_free(_c, _addr)   vfree(_addr)

#define btt8_bzero(_addr, _len)        memset((_addr), 0, (_len))
#define btt8_memcpy(_dst, _src, _len)  memcpy((_dst), (_src), (_len))
#define btt8_memcmp(_a, _b, _len)      memcmp((_a), (_b), (_len))


#define PRIu64 "llu"
#define btt8_printf(_fmt, ...)  \
	printk(KERN_NOTICE "btt8: " _fmt "\n", ##__VA_ARGS__)


static inline void*
btt8_pmem_map(
	void*    c,
	uint64_t off,
	uint64_t len
)
{
	struct kbtt8_disk*   d     = c;
	uint64_t             pgoff = off & (PAGE_SIZE - 1);
	struct blk_dax_ctl   dax = {
		.size   = len,
		.sector = (off - pgoff) / 512,
	};
	long                 avail;

	avail = bdev_direct_access(d->d_bdev, &dax);
	if (avail < len)
		return NULL;

	return dax.addr + pgoff;

}  /* btt8_pmem_map() */


#define btt8_pmem_memcpy_persist(_dst, _src, _len)  \
	memcpy_to_pmem(_dst, _src, _len)

#define btt8_pmem_persist(_addr, _len)  \
	arch_wb_cache_pmem(_addr, _len)


/*
 * lane management
 *
 * "lanes" are used to manage access to the list of free blocks.
 * the goal is to assign to each thread or CPU its own free block
 * slot so that it need not compete with others for the slot.
 */

/*
 * stride length for lane assignment
 *
 * should be mutually prime with the number of free blocks and just
 * large enough that each successive lane assignment is in another
 * cache line.  each lane is currently 16 bytes in size.
 */
#define LANE_STRIDE   (5)

/*
 * lane acquisition
 *
 * we use the current cpu number to determine our "home" lane.
 * if, at the time of acquisition, this home lane is in use, we try the
 * next lane and so on.
 */
static uint64_t
btt8_lane_acquire(
	void* c
)
{
	struct kbtt8_disk*  d   = c;
	unsigned int        cpu;
	uint64_t            l;        /* a lane */

	cpu = get_cpu();
	l = (cpu * LANE_STRIDE) % d->d_nlanes;

	if (d->d_nlanes < nr_cpu_ids) {
		while (0 != __sync_val_compare_and_swap(&(d->d_lanes[l]), 0, 1))
			if (++l >= d->d_nlanes)
				l = 0;
	}

	return l;

}  /* btt8_lane_acquire() */


static void
btt8_lane_release(
	void*    c,
	uint64_t l
)
{
	struct kbtt8_disk*   d = c;

	/* just clear the lane */
	d->d_lanes[l] = 0;

	put_cpu();

	return;

}  /* btt8_lane_release() */



#define btt8_yieldcpu(_c)   cond_resched()


typedef uint64_t   btt8_atomic64_t;
#define btt8_atomic64_inc(_pa)       __sync_add_and_fetch((_pa), 1)
#define btt8_atomic64_dec(_pa)       __sync_add_and_fetch((_pa), (-1))
#define btt8_atomic64_set(_pa, _v)  (*(_pa)) = (_v)
#define btt8_atomic64_read(_pa)     (*((volatile uint64_t*)(_pa)))


union btt8_atomic128 {
	__int128   s;
	struct {
		uint64_t   lo;
		uint64_t   hi;
	}          e;
};
typedef union btt8_atomic128  btt8_atomic128_t;

/* atomic reads for each half */
#define btt8_atomic128_read_lo(_pa)  (_pa)->e.lo
#define btt8_atomic128_read_hi(_pa)  (_pa)->e.hi
#define btt8_atomic128_read_lo_volatile(_pa)  \
	((volatile btt8_atomic128_t*)(_pa))->e.lo

/* address of */
#define btt8_atomic128_addr_lo(_pa)  (&((_pa)->e.lo))
#define btt8_atomic128_addr_hi(_pa)  (&((_pa)->e.hi))

/* sequential read of each half.  each half must be itself read
 * atomically, but the full 128-bit read need not be.
 * if the 128-bit read is not atomic, then lo must be read before hi.
 */
#define btt8_atomic128_na_read_lo2hi(_pa, _l, _h)  do {  \
	(_l) = (_pa)->e.lo;                                  \
	barrier();                                           \
	(_h) = (_pa)->e.hi;                                  \
} while(0)

/* non-atomic set */
#define btt8_atomic128_na_set(_pa, _l, _h)  do {  \
	(_pa)->e.lo = (_l);                           \
	(_pa)->e.hi = (_h);                           \
} while(0)

/* atomic compare-and-swap; returns non-zero if swap succeeds */
#define btt8_atomic128_cas(_pa, _old, _new)  \
	__sync_bool_compare_and_swap(&((_pa)->s), (_old)->s, (_new)->s)



#define BTT8_NO_SET_ZERO
#include "btt8core.c"



static int kbtt8_major = 0;

static struct kbtt8_disk* kbtt8_devs[26] = { NULL };

static int
kbtt8_open(
	struct block_device* bdev,
	fmode_t              mode
)
{
	struct kbtt8_disk*   d = bdev->bd_disk->private_data;
	bool                 r = false;

	spin_lock_irq(&d->d_spinlock);
	if ((-1) == d->d_refcount)
		r = true;
	else
		d->d_refcount++;
	spin_unlock_irq(&d->d_spinlock);

	if (r)
		return -ENOENT;

	return 0;

}  /* kbtt8_open() */

static void
kbtt8_release(
	struct gendisk* disk,
	fmode_t         mode
)
{
	struct kbtt8_disk*   d = disk->private_data;

	spin_lock_irq(&d->d_spinlock);
	d->d_refcount--;
	spin_unlock_irq(&d->d_spinlock);

	return;

}  /* kbtt8_release() */

static blk_qc_t
kbtt8_make_request(
	struct request_queue* q,
	struct bio*           bio
)
{
	struct kbtt8_disk*   d      = q->queuedata;
	u64                  bsize  = d->d_bsize;
	struct bio_vec       bvec;
	struct bvec_iter     iter;
	int (*blkop)(struct btt8*, void*, u64) = (void*)btt8_write;

	if (WRITE != bio_data_dir(bio))
		blkop = btt8_read;

	bio_for_each_segment(bvec, bio, iter) {
		unsigned long   irqflags;
		unsigned long   off;
		unsigned long   seglen;
		char*           kmap;
		char*           buf;

		kmap = bvec_kmap_irq(&bvec, &irqflags);

		off    = (iter.bi_sector << 9) / bsize;
		seglen = bvec.bv_len;
		buf    = kmap;
		while (seglen >= bsize) {
			if (blkop(d->d_btt, buf, off)) {
				bvec_kunmap_irq(kmap, &irqflags);
				bio_io_error(bio);
				return BLK_QC_T_NONE;
			}
			off++;
			buf += bsize;
			seglen -= bsize;
		}

		bvec_kunmap_irq(kmap, &irqflags);
	}

	bio_endio(bio);
	return BLK_QC_T_NONE;

}  /* kbtt8_make_request() */

static const struct block_device_operations kbtt8_fops = {
	.owner   = THIS_MODULE,
	.open    = kbtt8_open,
	.release = kbtt8_release,
};

static int
kbtt8_ctl_detach(
	struct kbtt8_disk* d
)
{
	if (NULL != d) {
		spin_lock_irq(&d->d_spinlock);
		if (0 != d->d_refcount) {
			spin_unlock_irq(&d->d_spinlock);
			if ((-1) == d->d_refcount)
				return -ENOENT;
			else
				return -EBUSY;
		}
		d->d_refcount = (-1);
		spin_unlock_irq(&d->d_spinlock);

		if (NULL != d->d_gd) {
			del_gendisk(d->d_gd);
			put_disk(d->d_gd);
		}
		if (NULL != d->d_queue)
			blk_cleanup_queue(d->d_queue);
		if (NULL != d->d_lanes)
			vfree(d->d_lanes);
		if (NULL != d->d_btt)
			btt8_close(d->d_btt);
		if (NULL != d->d_bdev)
			blkdev_put(d->d_bdev, (FMODE_READ | FMODE_WRITE | FMODE_EXCL));

		__sync_bool_compare_and_swap(&(kbtt8_devs[d->d_id]), d, 0);

		vfree(d);

		return 0;
	}

	return -ENOENT;

}  /* kbtt8_ctl_detach() */

static int
kbtt8_ctl_attach(
	const char*         bdev,
	int                 idslot,
	struct kbtt8_disk** pdisk
)
{
	int                  rc  = 0;
	struct kbtt8_disk*   d;

	d = vmalloc(sizeof(*d));
	if (NULL == d) {
		printk(KERN_NOTICE "btt8: vmalloc failed\n");
		rc = -ENOMEM;
		goto error;
	}
	memset(d, 0, sizeof(*d));
	spin_lock_init(&d->d_spinlock);

	/* reserve the device id */
	if (!__sync_bool_compare_and_swap(&(kbtt8_devs[idslot]), 0, d)) {
		printk(KERN_NOTICE "btt8: device %c already in use\n",
			'a' + idslot);
		rc = -EBUSY;
		goto error;
	}
	d->d_id = idslot;

	/* assign name */
	snprintf(d->d_name, 8, "btt8%c", 'a' + d->d_id);

	/*
	 * create our disk object
	 */

	/* btt8 */
	d->d_bdev = blkdev_get_by_path(bdev,
		(FMODE_READ | FMODE_WRITE | FMODE_EXCL), d);
	if (IS_ERR(d->d_bdev)) {
		printk(KERN_NOTICE "btt8: unable to open %s\n", bdev);
		rc = PTR_ERR(d->d_bdev);
		d->d_bdev = NULL;
		goto error;
	}
	d->d_btt = btt8_open(d);
	if (NULL == d->d_btt) {
		printk(KERN_NOTICE "btt8: attach failed\n");
		rc = -EIO;
		goto error;
	}
	d->d_bsize  = btt8_get_bsize(d->d_btt);
	d->d_nlanes = btt8_get_nlanes(d->d_btt);

	/* allocate lanes */
	d->d_lanes  = vmalloc(d->d_nlanes * sizeof(d->d_lanes[0]));
	if (NULL == d->d_lanes) {
		printk(KERN_NOTICE "btt8: unable to create lanes\n");
		rc = -ENOMEM;
		goto error;
	}
	memset(d->d_lanes, 0, (d->d_nlanes * sizeof(d->d_lanes[0])));

	/* queue */
	d->d_queue = blk_alloc_queue(GFP_KERNEL);
	if (NULL == d->d_queue) {
		printk(KERN_NOTICE "btt8: blk_alloc_queue failed\n");
		rc = -ENOMEM;
		goto error;
	}
	blk_queue_make_request(d->d_queue, kbtt8_make_request);
	blk_queue_logical_block_size(d->d_queue, d->d_bsize);
	d->d_queue->queuedata = d;

	/* disk init */
	d->d_gd = alloc_disk(8);
	if (NULL == d->d_gd) {
		printk(KERN_NOTICE "btt8: alloc_disk failed\n");
		rc = -ENOMEM;
		goto error;
	}
	d->d_gd->major        = kbtt8_major;
	d->d_gd->first_minor  = d->d_id * 8;
	d->d_gd->fops         = &kbtt8_fops;
	d->d_gd->queue        = d->d_queue;
	d->d_gd->private_data = d;
	strncpy(d->d_gd->disk_name, d->d_name, sizeof(d->d_gd->disk_name));
	set_capacity(d->d_gd,
		(btt8_get_nblocks(d->d_btt) * btt8_get_bsize(d->d_btt)) >> 9);

	add_disk(d->d_gd);

	(*pdisk) = d;
	return 0;

error:
	kbtt8_ctl_detach(d);

	(*pdisk) = NULL;
	return rc;

}  /* kbtt8_ctl_attach() */

static int
kbtt8_ctl_format(
	const char* bdev,
	u64         bsize
)
{
	int                  rc  = 0;
	struct kbtt8_disk*   d;

	/*
	 * we just need enough context for the core to be able to
	 * map it
	 */
	d = vmalloc(sizeof(*d));
	if (NULL == d) {
		printk(KERN_NOTICE "btt8: vmalloc failed\n");
		rc = -ENOMEM;
		goto out;
	}
	memset(d, 0, sizeof(*d));

	d->d_bdev = blkdev_get_by_path(bdev,
		(FMODE_READ | FMODE_WRITE | FMODE_EXCL), d);
	if (IS_ERR(d->d_bdev)) {
		printk(KERN_NOTICE "btt8: unable to open %s\n", bdev);
		rc = PTR_ERR(d->d_bdev);
		d->d_bdev = NULL;
		goto out;
	}

	if (0 != btt8_create(d, bsize,
		i_size_read(d->d_bdev->bd_inode), BTT8_NFREE)) {
		printk(KERN_NOTICE "btt8: create failed\n");
		rc = -EIO;
		goto out;
	}

	d->d_btt = btt8_open(d);
	if (NULL == d->d_btt) {
		printk(KERN_NOTICE "btt8: open failed\n");
		rc = -EIO;
		goto out;
	}

	printk(KERN_NOTICE "btt8: formatted %s with %llu %llu-byte blocks\n",
		bdev, btt8_get_nblocks(d->d_btt), btt8_get_bsize(d->d_btt));

	rc = 0;

out:
	if (d) {
		if (NULL != d->d_btt)
			btt8_close(d->d_btt);
		if (NULL != d->d_bdev)
			blkdev_put(d->d_bdev, (FMODE_READ | FMODE_WRITE | FMODE_EXCL));
		vfree(d);
	}

	return rc;

}  /* kbtt8_ctl_format() */

static
int
kbtt8_id2slot(
	char* id
)
{
	if (('a' <= id[0]) && (id[0] <= 'z') && (0 == id[1]))
		return id[0] - 'a';
	else
		return (-1);

}  /* kbtt8_id2slot() */

static ssize_t
kbtt8_ctl(
	struct bus_type* bus,
	const char*      buf,
	size_t           count
)
{
	int     rc;
	char*   bufcopy = kstrdup(buf, GFP_KERNEL);
	char*   s       = bufcopy;
	char*   cmd;

	cmd = strsep(&s, " \n");
	if (0 == strcmp(cmd, "format")) {
		char*           bdev;
		unsigned long   bsize;

		bdev  = strsep(&s, " \n");
		bsize = simple_strtoul(strsep(&s, " \n"), NULL, 10);
		rc = kbtt8_ctl_format(bdev, bsize);
		if (0 == rc)
			rc = count;
		else
			printk(KERN_WARNING "btt8: ctl: format failed\n");
	} else if (0 == strcmp(cmd, "attach")) {
		char*                bdev;
		char*                id;
		struct kbtt8_disk*   d;
		int                  idslot;

		bdev = strsep(&s, " \n");
		id   = strsep(&s, " \n");
		idslot = kbtt8_id2slot(id);
		if (0 <= idslot) {
			rc = kbtt8_ctl_attach(bdev, idslot, &d);
			if (0 == rc) {
				printk(KERN_NOTICE "btt8: ctl: attached %s as %s\n",
					bdev, d->d_name);
				rc = count;
			}
			else
				printk(KERN_WARNING "btt8: ctl: attach failed\n");
		}
		else {
			printk(KERN_WARNING "btt8: ctl: bad id '%s'\n", id);
			rc = -EINVAL;
		}
	}
	else if (0 == strcmp(cmd, "detach")) {
		char*   id;
		int     idslot;

		id = strsep(&s, " \n");
		idslot = kbtt8_id2slot(id);
		if (0 <= idslot) {
			rc = kbtt8_ctl_detach(kbtt8_devs[idslot]);
			if (0 == rc) {
				printk(KERN_NOTICE "btt8: ctl: detached btt8%c\n",
					idslot + 'a');
				rc = count;
			}
			else
				printk(KERN_WARNING "btt8: ctl: detach failed\n");
		}
		else {
			printk(KERN_WARNING "btt8: ctl: bad id '%s'\n", id);
			rc = -EINVAL;
		}
	}
	else {
		printk(KERN_WARNING "btt8: ctl: unrecognized command '%s'\n", cmd);
		rc = -EINVAL;
	}

	kfree(bufcopy);

	return rc;

}  /* kbtt8_ctl() */

static BUS_ATTR(ctl, S_IWUSR, NULL, kbtt8_ctl);

static struct attribute* kbtt8_bus_attrs[] = {
	&bus_attr_ctl.attr,
	NULL,
};

static const struct attribute_group kbtt8_bus_group = {
	.attrs = kbtt8_bus_attrs,
};
__ATTRIBUTE_GROUPS(kbtt8_bus);

struct bus_type kbtt8_bus_type = {
	.name       = "btt8",
	.bus_groups = kbtt8_bus_groups,
};

static int
kbtt8_init(void)
{
	int   rc;

	kbtt8_major = register_blkdev(0, "btt8");
	if (kbtt8_major <= 0) {
		printk(KERN_NOTICE "btt8: unable to get major number\n");
		return -EBUSY;
	}

	rc = bus_register(&kbtt8_bus_type);
	if (rc)
		unregister_blkdev(kbtt8_major, "btt8");

	return rc;

}  /* kbtt8_init() */

static void
kbtt8_exit(void)
{
	bus_unregister(&kbtt8_bus_type);
	unregister_blkdev(kbtt8_major, "btt8");

}  /* kbtt8_exit() */

MODULE_LICENSE("GPL v2");
module_init(kbtt8_init);
module_exit(kbtt8_exit);

