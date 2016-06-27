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


#include <stdlib.h>
#include <string.h>
#include <inttypes.h>
#include <stdio.h>
#include <sched.h>
#include <libpmem.h>


typedef uint64_t   btt8_u64_t;


typedef struct btt8   btt8_t;
struct pmemblk {
	void*       p_pmem;
	uint64_t    p_msize;
	int         p_fd;
	btt8_t*     p_btt;
	uint64_t    p_nlanes;
	uint64_t*   p_lanes;
};


#define btt8_malloc(_c, _len)  malloc(_len)
#define btt8_free(_c, _addr)   free(_addr)

#define btt8_bzero(_addr, _len)        memset((_addr), 0, (_len))
#define btt8_memcpy(_dst, _src, _len)  memcpy((_dst), (_src), (_len))
#define btt8_memcmp(_a, _b, _len)      memcmp((_a), (_b), (_len))


#define btt8_printf(_fmt, ...)  \
	fprintf(stderr, "libpmemblk: " _fmt "\n", ##__VA_ARGS__)


static inline void*
btt8_pmem_map(
	void*    c,
	uint64_t off,
	uint64_t len
)
{
	struct pmemblk*   p = c;

	if (p->p_msize < (off + len))
		return NULL;

	return p->p_pmem + off;

}  /* btt8_pmem_map() */


#define btt8_pmem_memcpy_persist(_dst, _src, _len)  \
	pmem_memcpy_persist(_dst, _src, _len)

#define btt8_pmem_persist(_addr, _len)  \
	pmem_persist(_addr, _len)


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
 * we assign each thread its own id and then use this id to determine
 * the thread's "home" lane.  if, at the time of acquisition, this home
 * lane is in use, we try the next lane and so on.
 */
static uint64_t
btt8_lane_acquire(
	void* c
)
{
	struct pmemblk*   p = c;
	uint64_t          l;      /* a lane */

	/*
	 * determine a starting lane
	 *
	 * if we haven't aleady, assign this thread an id and then use
	 * this id to pick a starting lane for our free lane search.
	 * scale the thread id by the lane stride hoping to avoid cache
	 * line contention within the lane array.
	 */
	{
		static uint64_t            tcount = 0;
		static __thread uint64_t   tid    = 0;
		if (0 == tid)
			tid = __sync_add_and_fetch(&tcount, 1);

		l = (tid * LANE_STRIDE) % p->p_nlanes;
	}

	/*
	 * search for a free lane starting with lane l, attempting to
	 * claim a lane using atomic compare-and-swap.
	 */
	while (0 != __sync_val_compare_and_swap(&(p->p_lanes[l]), 0, 1))
		if (++l >= p->p_nlanes)
			l = 0;

	return l;

}  /* btt8_lane_acquire() */


static void
btt8_lane_release(
	void*    c,
	uint64_t l
)
{
	struct pmemblk*   p = c;

	/* just clear the lane */
	p->p_lanes[l] = 0;

	return;

}  /* btt8_lane_release() */



#define btt8_yieldcpu(_c)   sched_yield()


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
	asm volatile ("" ::: "memory");                      \
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



#include "btt8core.c"



#include <unistd.h>
#include <fcntl.h>
#include <errno.h>
#include <sys/mman.h>
#include <stdio.h>

#include <libpmemblk.h>


static PMEMblkpool*
ctxt_open(
	int      fd,
	uint64_t msize
)
{
	PMEMblkpool*   p;

	p = malloc(sizeof(*p));
	if (NULL == p)
		return NULL;
	memset(p, 0, sizeof(*p));

	p->p_fd    = fd;
	p->p_msize = msize;

	p->p_pmem  = pmem_map(fd);
	if (NULL == p->p_pmem) {
		int   rc = errno;
		free(p);
		errno = rc;
		return NULL;
	}

	if (!pmem_is_pmem(p->p_pmem, p->p_msize)) {
		munmap(p->p_pmem, p->p_msize);
		free(p);
		errno = ENODEV;
		return NULL;
	}

	return p;

}  /* ctxt_open() */


static int
ctxt_attach(
	PMEMblkpool* p
)
{
	/* open the btt8 device */
	p->p_btt = btt8_open(p);
	if (NULL == p->p_btt)
		return (-1);

	/* create lanes */
	p->p_nlanes = btt8_get_nlanes(p->p_btt);
	p->p_lanes  = malloc(p->p_nlanes * sizeof(p->p_lanes[0]));
	if (NULL == p->p_lanes) {
		btt8_close(p->p_btt);
		p->p_btt = NULL;
		return (-1);
	}
	memset(p->p_lanes, 0, (p->p_nlanes * sizeof(p->p_lanes[0])));

	return 0;

}  /* ctxt_attach() */


static void
ctxt_close(
	PMEMblkpool* p
)
{
	if (NULL != p->p_btt)
		btt8_close(p->p_btt);
	if (NULL != p->p_lanes)
		free(p->p_lanes);
	if (NULL != p->p_pmem)
		munmap(p->p_pmem, p->p_msize);
	if (0 >= p->p_fd)
		close(p->p_fd);
	free(p);

	return;

}  /* ctxt_close() */


PMEMblkpool*
pmemblk_open(
	const char* path,
	size_t      bsize
)
{
	int            rc;
	int            fd    = (-1);
	size_t         msize;
	PMEMblkpool*   p     = NULL;

	fd = open(path, O_RDWR);
	if (0 > fd) {
		rc = errno;
		goto error;
	}

	msize = lseek(fd, 0, SEEK_END);
	(void)lseek(fd, 0, SEEK_SET);
	if (BTT8_MIN_POOL > msize) {
		rc = EINVAL;
		goto error;
	}

	rc = EIO;
	p = ctxt_open(fd, msize);
	if (NULL == p)
		goto error;
	fd = (-1);
	if (0 != ctxt_attach(p))
		goto error;

	/* if given, bsize must match */
	if ((0 != bsize) && (bsize != btt8_get_bsize(p->p_btt))) {
		rc = EINVAL;
		goto error;
	}

	return p;

error:
	if (NULL != p)
		ctxt_close(p);
	if (0 <= fd)
		close(fd);
	errno = rc;
	return NULL;

}  /* pmemblk_open() */


PMEMblkpool*
pmemblk_create(
	const char* path,
	size_t      bsize,
	size_t      poolsize,
	mode_t      mode
)
{
	int            rc;
	int            fd = (-1);
	PMEMblkpool*   p  = NULL;

	fd = open(path, O_RDWR | O_CREAT | O_EXCL, mode);
	if (0 > fd) {
		rc = errno;
		goto error;
	}

	rc = posix_fallocate(fd, 0, poolsize);
	if (0 != rc)
		goto error;

	/* XXX probably insufficient: the parent dir may also need sync */
	rc = fsync(fd);
	if (0 != rc)
		goto error;

	/* lay down the metadata */
	p = ctxt_open(fd, poolsize);
	if (NULL == p) {
		rc = EIO;
		goto error;
	}
	fd = (-1);
	if (0 != btt8_create(p, bsize, poolsize, BTT8_NFREE)) {
		rc = EINVAL;
		goto error;
	}

	/* complete the open */
	if (0 != ctxt_attach(p)) {
		rc = EIO;
		goto error;
	}

	return p;

error:
	if (NULL != p) {
		ctxt_close(p);
		(void)unlink(path);
	}
	if (0 <= fd) {
		close(fd);
		(void)unlink(path);
	}
	errno = rc;
	return NULL;

}  /* pmemblk_create() */


void
pmemblk_close(
	PMEMblkpool* p
)
{
	ctxt_close(p);
	return;

}  /* pmemblk_close() */


size_t
pmemblk_nblock(
	PMEMblkpool* p
)
{
	return btt8_get_nblocks(p->p_btt);

}  /* pmemblk_nblock() */


size_t
pmemblk_bsize(
	PMEMblkpool *p
)
{
	return btt8_get_bsize(p->p_btt);

}  /* pmemblk_bsize() */


int
pmemblk_read(
	PMEMblkpool* bp,
	void*        buf,
	off_t        blockno
)
{
	int   rc;
	
	rc = btt8_read(bp->p_btt, buf, blockno);
	if (0 != rc)
		errno = EIO;

	return rc;

}  /* pmemblk_read() */


int
pmemblk_write(
	PMEMblkpool* bp,
	const void*  buf,
	off_t        blockno
)
{
	int   rc;
	
	rc = btt8_write(bp->p_btt, buf, blockno);
	if (0 != rc)
		errno = EIO;

	return rc;

}  /* pmemblk_write() */


int
pmemblk_set_zero(
	PMEMblkpool* bp,
	off_t        blockno
)
{
	return btt8_set_zero(bp->p_btt, blockno);

}  /* pmemblk_set_zero() */

