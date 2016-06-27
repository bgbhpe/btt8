# BTT8
An alternative Block Translation Table implementation

## Overview

BTT8 is a prototype implementation of an alternative block translation table
algorithm, providing atomic sector/block access to byte-addressable
persistent memory.  The goal was to provide improved performance over the
original BTT as implemented in the Linux kernel and libpmemblk (NVML).

As presented here, the prototype consists of:

- BTT8-nocheck.tla, the (minimized) formal specification of the algorithm in
PlusCal.  The assertions and invariants needed for the model checker have been
removed, (perhaps) enhancing readability.

- btt8core.c, the core implementation of the algorithm.  This file cannot be
used stand-alone, it must be wrapped in another framework that provides certain
low-level primitives.

- libpmemblk.c, a partial implementation of the NVML's libpmemblk interfaces;
wraps around btt8core.c.

- btt8kdrv.c, a Linux kernel block driver; wraps around btt8core.c.

- starve.c, a small program that can be used to measure the effects of
reader starvation.

- recoveryperf.c, a small program that can be used to measure the performance
of free list recovery.

- BTT8.tla, the full formal specification of the algorithm in PlusCal,
including the constructions needed for assertion and invariant checking.

btt8core.c and its inclusion by libpmemblk.c and btt8kdrv.c may be a little
unusual, but it made it very easy to take changes from testing and debugging
in user land over to the kernel module.


## libpmemblk

The BTT8 libpmemblk is intended as a partial drop-in replacement for the
NVML's libpmemblk (the APIs are similar, but the on-disk format is
incompatible).  This prototype supports the following interfaces:

- pmemblk_open()
- pmemblk_create()
- pmemblk_close()
- pmemblk_bsize()
- pmemblk_nblock()
- pmemblk_read()
- pmemblk_write()
- pmemblk_set_zero()

To build libpmemblk.so:
`$ make lib`


## btt8 Linux kernel module

NOTE: This is my first attempt at a Linux kernel module, and I've taken
some liberties.  In particular (and beyond the inevitable rookie errors),
I use gcc intrinsics for atomic operations, my use of sysfs would
probably be considered abusive, and then there's the whole "#include btt8core.c"
thing.

### To build:
`$ make`

### To use:

If not loaded already, load the driver:
`# insmod ./btt8.ko`

The driver offers a control point at /sys/bus/btt8/ctl.  You control the
driver by writing simple commands to this control point.

To format a pmem device for use with btt8:
`# echo "format /dev/pmem0 4096" > /sys/bus/btt8/ctl`

This will lay down the BTT8 metadata on /dev/pmem0 with a sector size of
4096 bytes.

To attach btt8 to a pmem device, after formatting:
`# echo "attach /dev/pmem0 a" > /sys/bus/btt8/ctl`

This will create /dev/btt8a.  Note that /dev/pmem0 will still exist in the
/dev/ namespace, unlike when the BTT is bound to a pmem device.  When btt8
is attached, use the /dev/btt8[a-z] device; do not use the /dev/pmemN device
directly.

To detach btt8 from a pmem device:
`# echo "detach a" > /sys/bus/btt8/ctl`

This will remove /dev/btt8a.  Metadata is left intact, so the pmem device
can be re-attached.

