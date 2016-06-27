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


/*
 * This module is intended to be included in a wrapper module, such
 * as one implementing the NVML's libpmemblk interface or a kernel
 * driver module.
 *
 * Such a wrapper module must provide the following types and support
 * interfaces.  See libpmemblk.c for an example.
 *
 * A 64-bit unsigned integer:
 *   btt8_u64_t
 * 
 * Typical memory allocation and manipulation routines:
 *   btt8_malloc()
 *   btt8_free()
 *   btt8_bzero()
 *   btt8_memcpy()
 *   btt8_memcmp()
 *
 * Debug print:
 *   btt8_printf()
 * 
 * Persistent memory access routines:
 *   btt8_pmem_map()
 *   btt8_pmem_memcpy_persist()
 *   btt8_pmem_persist()
 * 
 * Lane management:
 *   btt8_lane_acquire()
 *   btt8_lane_release()
 * 
 * Yield the CPU:
 *   btt8_yieldcpu()
 * 
 * 64-bit unsigned integer with atomic access interfaces:
 *   btt8_atomic64_t
 *   btt8_atomic64_inc()
 *   btt8_atomic64_dec()
 *   btt8_atomic64_set()
 *   btt8_atomic64_read()
 * 
 * 128-bit unsigned integer with atomic access interfaces:
 *   btt8_atomic128_t
 *   btt8_atomic128_read_lo()
 *   btt8_atomic128_read_lo_volatile()
 *   btt8_atomic128_read_hi()
 *   btt8_atomic128_addr_lo()
 *   btt8_atomic128_addr_hi()
 *   btt8_atomic128_na_read_lo2hi()
 *   btt8_atomic128_na_set()
 *   btt8_atomic128_cas()
 *
 *
 * The wrapper module may use the following interfaces that are defined
 * here.  The wrapper should not call any of the other functions
 * defined here.
 *   btt8_open()
 *   btt8_close()
 *   btt8_create()
 *   btt8_get_bsize()
 *   btt8_get_nblocks()
 *   btt8_get_nlanes()
 *   btt8_read()
 *   btt8_write()
 *   btt8_set_zero()
 */


/*
 * a few parameters
 */
#define BTT8_MIN_POOL  ((btt8_u64_t)(16 << 20))
#define BTT8_MIN_BLK   ((btt8_u64_t)512)

/*
 * number of free blocks to reserve
 */
#define BTT8_NFREE_SHIFT  (12)  /* 2^12 == 4096 */
#define BTT8_NFREE        (1 << BTT8_NFREE_SHIFT)

/*
 * the translation table entry
 *
 * lo will be our cycle count, hi will be the translation
 */
typedef btt8_atomic128_t   bt_tte;
#define TTE_READ_CYCLE(_t)  btt8_atomic128_read_lo(_t)
#define TTE_READ_CYCLE_VOLATILE(_t)  btt8_atomic128_read_lo_volatile(_t)
#define TTE_READ_PBA(_t)    btt8_atomic128_read_hi(_t)
#define TTE_ADDR_PBA(_t)    btt8_atomic128_addr_hi(_t)
#define TTE_PBA_SZ          (8)
#define TTE_READ_CYCLETHENPBA(_t, _cycle, _pba)  \
	btt8_atomic128_na_read_lo2hi(_t, _cycle, _pba)
#define TTE_SET_CYCLEPBA(_t, _cycle, _pba)  \
	btt8_atomic128_na_set(_t, _cycle, _pba)

/* tranlation cycles are composed of two parts: a lane id and
 * a lane-specific cycle count:
 */
#define MKCYCLE(_l, _c)  (((_c) << BTT8_NFREE_SHIFT) | (_l))
#define CYCLE_LANE(_c)   ((_c) & (BTT8_NFREE - 1))
#define CYCLE_CYCLE(_c)  (((_c) & ~(BTT8_NFREE - 1)) << BTT8_NFREE_SHIFT)

#define XLATION_FLAG_MASK    (0xc000000000000000ULL)
#define XLATION_PBA_MASK     (~XLATION_FLAG_MASK)

#define XLATION_FLAG_ZERO    (0x8000000000000000ULL)
#define XLATION_FLAG_UNUSED  (0x4000000000000000ULL)


struct bt_super {
	char         s_sig[8];
	btt8_u64_t   s_bsize;     /* block size */
	btt8_u64_t   s_nblocks;   /* number of blocks available to user */
	btt8_u64_t   s_nfree;     /* number of free blocks */
	btt8_u64_t   s_ttoff;     /* byte offset to xlation table */
	btt8_u64_t   s_dataoff;   /* byte offset to data */
};


struct bt_lane {
	btt8_u64_t   l_freepba;  /* free PBA for this lane */
	btt8_u64_t   l_cycle;    /* cycle count for this lane */
};


struct btt8 {
	void*             b_ctxt;
	struct bt_super   b_super;  /* copy of super block (volatile) */
	bt_tte*           b_tt;     /* translation table (persistent) */
	char*             b_data;   /* data blocks (persistent) */
	struct bt_lane*   b_lanes;  /* lane data (volatile) */
	btt8_atomic64_t   b_hungry; /* > 0 if a reader is starved */
};

#define BTT8_SIG   "PMBLKBB"



static int
btt8_recover(
	struct btt8* bp
)
{
	uint64_t    tblocks    = bp->b_super.s_nblocks + bp->b_super.s_nfree;
	uint64_t    nbitchunks;
	uint64_t*   bmap;
	uint64_t    b;
	uint64_t    f;
	uint64_t    i;

#define CHUNKSHIFT         (6)  /* 64-bit chunks */
#define BITSPERCHUNK       (1ULL << CHUNKSHIFT)
#define CHUNKMASK          (BITSPERCHUNK - 1)
#define CHUNKSZ            (BITSPERCHUNK >> 3)
#define BLKTOCHUNK(_b)     ((_b) >> CHUNKSHIFT)
#define BLKTOBIT(_b)       ((_b) & CHUNKMASK)
#define MAPTOBLK(_b, _i)   (((_b) << CHUNKSHIFT) + (_i))

	nbitchunks = BLKTOCHUNK(tblocks-1) + 1;
	bmap = btt8_malloc(bp->b_ctxt, (nbitchunks * CHUNKSZ));
	if (NULL == bmap)
		return -1;

	/* zero the bit map */
	for (b = 0; b < nbitchunks; b++)
		bmap[b] = 0;
	/* set the unused bits in the last chunk so that we do not
	 * count them as free
	 */
	if (BLKTOBIT(tblocks-1) != (BITSPERCHUNK - 1))
		bmap[b-1] = ~((1ULL << BLKTOBIT(tblocks)) - 1);

	/* for each mapped block, set its corresponding bit in the map */
	for (b = 0; b < bp->b_super.s_nblocks; b++) {
		btt8_u64_t   t = TTE_READ_PBA(&(bp->b_tt[b])) & XLATION_PBA_MASK;
		btt8_u64_t   c = TTE_READ_CYCLE(&(bp->b_tt[b]));

		if (t >= tblocks) {
			btt8_printf("lba %"PRIu64" mapped to %"PRIu64" out-of-range, "
				"max pba %"PRIu64, b, t, (tblocks - 1));
			goto error;
		}
		if (bmap[BLKTOCHUNK(t)] & (1ULL << BLKTOBIT(t))) {
			btt8_printf("lba %"PRIu64" mapped to %"PRIu64", already used",
				b, t);
			goto error;
		}

		bmap[BLKTOCHUNK(t)] |= (1ULL << BLKTOBIT(t));
		/* update lane cycle count */
		if (CYCLE_CYCLE(c) > bp->b_lanes[CYCLE_LANE(c)].l_cycle)
			bp->b_lanes[CYCLE_LANE(c)].l_cycle = CYCLE_CYCLE(c);
	}

	/* search for all unset bits */
	for (b = 0, f = 0; b < nbitchunks; b++) {
		if (bmap[b] == ~(0ULL))
			continue;
		for (i = 0; i < BITSPERCHUNK; i++)
			if (0 == ((1ULL << i) & bmap[b])) {
				if (f >= bp->b_super.s_nfree) {
					btt8_printf("too many free blocks");
					goto error;
				}
				/* and record the corresponding block as free */
				bp->b_lanes[f++].l_freepba = MAPTOBLK(b, i);
			}
	}

	btt8_free(bp->b_ctxt, bmap);

	if (f != bp->b_super.s_nfree) {
		btt8_printf("found %"PRIu64" free blocks, expected %"PRIu64,
			f, bp->b_super.s_nfree);
		return -1;
	}

	return 0;

error:
	btt8_free(bp->b_ctxt, bmap);
	return -1;

#undef CHUNKSHIFT
#undef BITSPERCHUNK
#undef CHUNKMASK
#undef CHUNKSZ
#undef BLKTOCHUNK
#undef BLKTOBIT
#undef MAPTOBLK

}  /* btt8_recover() */


static struct btt8*
btt8_open_map(
	void*            ctxt,
	struct bt_super* super
)
{
	struct btt8*   bp = NULL;

	bp = (struct btt8*)btt8_malloc(ctxt, sizeof(*bp));
	if (NULL == bp)
		return NULL;
	btt8_bzero(bp, sizeof(*bp));

	/* save the context and a copy of our super block */
	bp->b_ctxt = ctxt;
	btt8_memcpy(&(bp->b_super), super, sizeof(*super));

	/* map in our translation table and data blocks */
	bp->b_tt   = btt8_pmem_map(ctxt, super->s_ttoff,
		(super->s_nblocks * sizeof(bp->b_tt[0])));
	bp->b_data = btt8_pmem_map(ctxt, super->s_dataoff,
		((super->s_nblocks + super->s_nfree) * super->s_bsize));

	if ((NULL == bp->b_tt) || (NULL == bp->b_data)) {
		btt8_free(ctxt, bp);
		return NULL;
	}

	return bp;

}  /* btt8_open_map() */


static void
btt8_close_map(
	struct btt8* bp
)
{
	btt8_free(bp->b_ctxt, bp);
	return;

}  /* btt8_close_map() */


static struct btt8*
btt8_open(
	void* ctxt
)
{
	struct bt_super*   super;
	struct btt8*       bp    = NULL;

	/* fetch the super block */
	super = btt8_pmem_map(ctxt, 0, sizeof(*super));
	if (NULL == super)
		return NULL;

	/* check the signature */
	if (0 != btt8_memcmp(super->s_sig, BTT8_SIG, 8)) {
		btt8_printf("bad signature");
		return NULL;
	}

	/* map it in */
	bp = btt8_open_map(ctxt, super);
	if (NULL == bp)
		return NULL;

	/* allocate lane data */
	bp->b_lanes = btt8_malloc(ctxt,
		bp->b_super.s_nfree * sizeof(*bp->b_lanes));
	if (NULL == bp->b_lanes) {
		goto error;
	}
	btt8_bzero(bp->b_lanes, bp->b_super.s_nfree * sizeof(*bp->b_lanes));

	/* recover the free list */
	if (0 != btt8_recover(bp)) {
		goto error;
	}

	return bp;

error:
	if (NULL != bp) {
		if (NULL != bp->b_lanes)
			btt8_free(ctxt, bp->b_lanes);
		btt8_close_map(bp);
	}
	return NULL;

}  /* btt8_open() */


static void
btt8_close(
	struct btt8* bp
)
{
	if (NULL != bp->b_lanes)
		btt8_free(bp->b_ctxt, bp->b_lanes);
	btt8_close_map(bp);
	return;

}  /* btt8_close() */


static int
btt8_create(
	void*      ctxt,
	btt8_u64_t bsize,
	btt8_u64_t poolsize,
	btt8_u64_t nfree
)
{
	struct bt_super   super;
	struct btt8*      bp;
	btt8_u64_t        i;
	void*             pmem;

	if ((BTT8_MIN_POOL > poolsize) ||
	    (BTT8_MIN_BLK > bsize) ||
	    (BTT8_NFREE != nfree)) {
		return (-1);
	}

	/*
	 * construct a super block
	 */
	btt8_bzero(&super, sizeof(super));
	/*
	 * space allocation:
	 *
	 * block  0             : super block
	 * blocks 1     - (1+T) : translation table
	 * blocks (T+2) -     B : data
	 *
	 * B = total blocks
	 * T = num blocks for xlation table
	 * D = num blocks for data
	 * K = spare
	 *
	 * K = B - 1
	 * T + D = K
	 * T = D / bsize / sizeof(bt_tte)
	 *
	 *           D + ((D * sizeof(bt_tte)) / bsize) = K
	 * ((D * bsize) + (D * sizeof(bt_tte))) / bsize = K
	 *    D * (bsize + sizeof(bt_tte)) = K * bsize
	 *                               D = (K * bsize) / (bsize + sizeof(bt_tte))
	 */
	{
		btt8_u64_t   B;
		btt8_u64_t   T;
		btt8_u64_t   D;
		btt8_u64_t   K;

		B = poolsize / bsize;
		K = B - 1;
		D = (K * bsize) / (bsize + sizeof(bt_tte));
		T = K - D;

		if ((poolsize < ((T + D + 1) * bsize)) ||
		    ((T * bsize / sizeof(bt_tte)) < D) ||
		    (BTT8_NFREE >= D)) {
			return (-1);
		}

		super.s_bsize    = bsize;
		super.s_nblocks  = D - BTT8_NFREE;
		super.s_ttoff    = 1 * bsize;
		super.s_dataoff  = (T + 1) * bsize;
		super.s_nfree    = BTT8_NFREE;
	}

	/* map the device */
	bp = btt8_open_map(ctxt, &super);
	if (NULL == bp)
		return (-1);

	/*
	 * initialize the translation table
	 * the first s_nfree PBAs will be our first free blocks
	 */
	for (i = 0; i < bp->b_super.s_nblocks; i++) {
		TTE_SET_CYCLEPBA(&(bp->b_tt[i]),
		                 0,
		                 (i + bp->b_super.s_nfree) | XLATION_FLAG_ZERO);
	}

	/* write out the unsigned super block */
	pmem = btt8_pmem_map(ctxt, 0, super.s_dataoff);
	if (NULL == pmem) {
		btt8_close_map(bp);
		return (-1);
	}
	btt8_memcpy(pmem, &super, sizeof(super));

	/* persist our metadata so far */
	btt8_pmem_persist(pmem, super.s_dataoff);

	/* finally, write out the signature */
	btt8_memcpy(bp->b_super.s_sig, BTT8_SIG, 8);
	btt8_pmem_memcpy_persist(pmem,
		&(bp->b_super.s_sig), sizeof(bp->b_super.s_sig));

	btt8_close_map(bp);

	return 0;

}  /* btt8_create() */


static btt8_u64_t
btt8_get_nblocks(
	struct btt8* bp
)
{
	return bp->b_super.s_nblocks;

}  /* btt8_get_nblock() */


static btt8_u64_t
btt8_get_bsize(
	struct btt8* bp
)
{
	return bp->b_super.s_bsize;

}  /* btt8_get_bsize() */


static btt8_u64_t
btt8_get_nlanes(
	struct btt8* bp
)
{
	return bp->b_super.s_nfree;

}  /* btt8_get_nlanes() */


static inline int
btt8_try_one_read(
	void*                    dst,
	btt8_u64_t               bsize,
	volatile bt_tte*         ptte,
	volatile struct bt_lane* lanes,
	char*                    src
)
{
	btt8_u64_t   precycle;
	btt8_u64_t   pba;
	btt8_u64_t   off;

	/* 
	 * All concurrent writes to the entry are atomic, but since our
	 * entry is 16 bytes in size, we can't read it atomically with a
	 * single load.  However, we can read it in two parts and use
	 * the cycle to detect apparent atomicity.
	 *
	 * To do this, we need to absolutely read the cycle first.  That
	 * is, the PBA we read should match the cycle we read or it
	 * should match a future cycle.  It should never match a previous
	 * cycle.
	 *
	 * PlusCal: RloadPreCycle
	 * PlusCal: RloadPBA
	 */
	TTE_READ_CYCLETHENPBA(ptte, precycle, pba);

	/*
	 * Ensure that the translation table entry is persistent.  If the
	 * entry cycle count is 1 greater than the lane cycle count, then
	 * there is a chance that the entry is not persistent.
	 *
	 * PlusCal: RloadLaneCycle   (b_lanes access)
	 * PlusCal: RpersistMapping  (comparison)
	 */
	if ((lanes[CYCLE_LANE(precycle)].l_cycle + 1) == CYCLE_CYCLE(precycle)) {
		/*
		 * Only the PBA needs to be persistent.
		 *
		 * PlusCal: RpersistMapping  (persist)
		 */
		btt8_pmem_persist((void*)TTE_ADDR_PBA(ptte), TTE_PBA_SZ);
		/*
		 * REVISIT: If a lane is in a "dry-spell" with no writes, then
		 *          its cycle count may not change for a while.  Readers
		 *          would be forced to continually persist.  We could
		 *          set the translation's cycle to the current lane cycle.
		 */
	}

	/* special case: metadata-zeroed block */
	if (pba & XLATION_FLAG_ZERO) {
		/* PlusCal: RcopyBlock */
		btt8_bzero(dst, bsize);
		/* note that even though zeroing a block here is
		 * always atomic, we still need to pass through
		 * the re-translaton check below in order to
		 * guarantee persistence.
		 */
	}
	else {
		/*
		 * Copy the block data
		 *
		 * PlusCal: RcopyBlock
		 */
		off = (pba & XLATION_PBA_MASK) * bsize;
		btt8_memcpy(dst, src + off, bsize);
	}

	/*
	 * Our read was atomic if the cycle after the read matches the
	 * cycle before the read.
	 *
	 * PlusCal: RcheckAtomicity
	 */
	return precycle == TTE_READ_CYCLE_VOLATILE(ptte);

}  /* btt8_try_one_read() */


static int
btt8_read(
	struct btt8* bp,
	void*        buf,
	btt8_u64_t   blockno
)
{
	volatile bt_tte*         ptte;
	volatile struct bt_lane* lanes;
	char*                    data;
	btt8_u64_t               bsize;
	btt8_u64_t               tries;

	if ((NULL == bp) ||
	    (0 > blockno) ||
	    (bp->b_super.s_nblocks <= blockno)) {
		return (-1);
	}

	ptte  = &(bp->b_tt[blockno]);
	lanes = bp->b_lanes;
	data  = bp->b_data;
	bsize = bp->b_super.s_bsize;

	/* try the read once */
	if (btt8_try_one_read(buf, bsize, ptte, lanes, data))
		return 0;

	/*
	 * read the block until the xlation is stable
	 */
	tries = 3;
	do {

		if (tries > 0)
			if (--tries == 0)
				btt8_atomic64_inc(&(bp->b_hungry));

	} while(!btt8_try_one_read(buf, bsize, ptte, lanes, data));

	if (tries == 0)
		btt8_atomic64_dec(&(bp->b_hungry));

	return 0;

}  /* btt8_read() */


static btt8_u64_t
btt8_try_swap_xlation(
	struct btt8* bp,
	btt8_u64_t   lba,
	btt8_u64_t   newpba,
	btt8_u64_t   lane
)
{
	bt_tte*   ptte;
	bt_tte    newt;
	bt_tte    oldt;

	/*
	 * Read the current (old) entry.  Our read is not atomic, but
	 * this is okay: the CAS below will detect a "torn" read here.
	 *
	 * PlusCal: WloadOldCycle / WloadOldPBA
	 */
	ptte = &(bp->b_tt[lba]);
	TTE_SET_CYCLEPBA(&oldt, TTE_READ_CYCLE(ptte), TTE_READ_PBA(ptte));

	/* Construct our new entry, with incremented cycle count */
	TTE_SET_CYCLEPBA(&newt,
		MKCYCLE(lane, bp->b_lanes[lane].l_cycle + 1),
		newpba);

	/*
	 * Swap in new translation.
	 *
	 * PlusCal: WswapMapping
	 */
	if (btt8_atomic128_cas(ptte, &oldt, &newt)) {
		/*
		 * Persist the translation
		 *
		 * Note that we cannot persist the entire 16-byte entry
		 * atomically.  Fortunately, this is not a problem: we only
		 * need the PBA to be persisted.
		 *
		 * PlusCal: WpersistMapping
		 */
		btt8_pmem_persist((void*)TTE_ADDR_PBA(ptte), TTE_PBA_SZ);

		/*
		 * Update the lane cycle
		 *
		 * This is not atomic with our CAS/persist above;
		 * any inconsistency in the shadow will be fixed the
		 * next time the block is read or written.
		 *
		 * PlusCal: WupdateCycle
		 */
		bp->b_lanes[lane].l_cycle++;

		/* Return the old translation with any error/zero flags
		 * cleared.
		 */
		return TTE_READ_PBA(&oldt) & XLATION_PBA_MASK;
	}
	
	/* CAS failed, so return the new translation */
	return TTE_READ_PBA(&newt) & XLATION_PBA_MASK;

}  /* btt8_try_swap_xlation() */


int
btt8_write(
	struct btt8* bp,
	const void*  buf,
	btt8_u64_t   blockno
)
{
	btt8_u64_t    bsize;
	btt8_u64_t    lane;
	btt8_u64_t*   pfreet;
	btt8_u64_t    freet;
	btt8_u64_t    off;

	if ((NULL == bp) ||
	    (0 > blockno) ||
	    (bp->b_super.s_nblocks <= blockno)) {
		return (-1);
	}

	/* wait here until there are no hungry readers */
	while (btt8_atomic64_read(&(bp->b_hungry)) > 0)
		btt8_yieldcpu(bp->b_ctxt);

	bsize = bp->b_super.s_bsize;

	/*
	 * Claim a lane and identify our free block.
	 *
	 * PlusCal: Wstart
	 */
	lane   = btt8_lane_acquire(bp->b_ctxt);
	pfreet = &(bp->b_lanes[lane].l_freepba);
	freet  = *pfreet;

	/*
	 * Write data to new block.
	 *
	 * PlusCal: WwriteBlock
	 */
	off = freet * bsize;
	btt8_pmem_memcpy_persist(bp->b_data + off, buf, bsize);

	/*
	 * swap in our new translation, saving the old translation
	 * as our new free block
	 *
	 * PlusCal: WputFreeBlock  (our assignment here)
	 */
	*pfreet = btt8_try_swap_xlation(bp, blockno, freet, lane);

	/* PlusCal: WputFreeBlock */
	btt8_lane_release(bp->b_ctxt, lane);

	return 0;

}  /* btt8_write() */


#ifndef BTT8_NO_SET_ZERO
static int
btt8_set_zero(
	struct btt8* bp,
	btt8_u64_t   blockno
)
{
	btt8_u64_t    lane;
	btt8_u64_t*   pfreet;
	btt8_u64_t    freet;

	if ((NULL == bp) ||
	    (0 > blockno) ||
	    (bp->b_super.s_nblocks <= blockno)) {
		return (-1);
	}

	/* wait here until there are no hungry readers */
	while (btt8_atomic64_read(&(bp->b_hungry)) > 0)
		btt8_yieldcpu(bp->b_ctxt);

	/*
	 * Claim a lane and identify our free block.
	 *
	 * PlusCal: Wstart
	 */
	lane   = btt8_lane_acquire(bp->b_ctxt);
	pfreet = &(bp->b_lanes[lane].l_freepba);
	freet  = *pfreet;

	/*
	 * swap in our new zeroed translation, saving the old
	 * translation as our new free block
	 */
	freet |= XLATION_FLAG_ZERO;
	/* PlusCal: WputFreeBlock */
	*pfreet = btt8_try_swap_xlation(bp, blockno, freet, lane);

	btt8_lane_release(bp->b_ctxt, lane);

	return 0;

}  /* btt8_set_zero() */
#endif


