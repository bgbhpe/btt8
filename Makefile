#
# Copyright (C) 2016 Hewlett Packard Enterprise Development LP
# 
# This program is free software; you can redistribute it and/or
# modify it under the terms of the GNU General Public License,
# version 2 as published by the Free Software Foundation.
# 
# This program is distributed in the hope that it will be useful,
# but WITHOUT ANY WARRANTY; without even the implied warranty of
# MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the
# GNU General Public License for more details.
# 
# You should have received a copy of the GNU General Public
# License along with this program; if not, write to the Free
# Software Foundation, Inc., 59 Temple Place, Suite 330,
# Boston, MA 02111-1307 USA
#

ifeq ($(BTT8BUILDLIB),)



# kernel module build
#

ifneq ($(KERNELRELEASE),)
    obj-m := btt8.o
    btt8-y := btt8kdrv.o
    CFLAGS_btt8kdrv.o := -mcx16

btt8kdrv.o: btt8core.c

else

    KERNELDIR ?= /lib/modules/$(shell uname -r)/build
    PWD := $(shell pwd)

default:
	$(MAKE) -C $(KERNELDIR) M=$(PWD) modules

clean:
	rm -f btt8.mod.o btt8.o btt8kdrv.o
	rm -f .btt8.ko.cmd .btt8.mod.o.cmd .btt8.o.cmd .btt8kdrv.o.cmd
	rm -Rf .tmp_versions
	rm -f Module.symvers btt8.ko btt8.mod.c modules.order


# jump to lib build
lib:
	$(MAKE) BTT8BUILDLIB=1 all

# jump to lib build
libclean:
	$(MAKE) BTT8BUILDLIB=1 clean

endif



else



# user library build
#

CC      = gcc
CFLAGS  = -Wall -m64 -mcx16 -fPIC -O2 $($(@)_CFLAGS)
LDFLAGS = -lpmem $($(@)_LDFLAGS)


all: libpmemblk.so rperf starve

libpmemblk.so: libpmemblk.o
	gcc -shared -o $@ $^ $(LDFLAGS)

libpmemblk.o: btt8core.c

rperf: recoveryperf.o libpmemblk.o
	gcc -Wall -pthread -o $@ $^ $(LDFLAGS)

starve: starve.o libpmemblk.o
	gcc -Wall -pthread -o $@ $^ $(LDFLAGS)

clean:
	rm -f libpmemblk.so libpmemblk.o rperf recoveryperf.o starve starve.o



endif

