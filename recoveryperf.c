/*
 * Copyright (C) 2016 Hewlett Packard Enterprise Development LP
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


#include <stdio.h>
#include <errno.h>
#include <stdlib.h>
#include <inttypes.h>

#include <libpmemblk.h>

int
main(
	int   argc,
	char* argv[]
)
{
	char*          path;
	uint64_t       bsize;
	uint64_t       psize;
	uint64_t       nloops;
	PMEMblkpool*   bp;

	if (argc != 5) {
		fprintf(stderr, "ERROR: usage: recoveryperf PATH BSIZE PSIZEMB LOOPS\n");
		exit(1);
	}
	path   = argv[1];
	bsize  = strtoul(argv[2], NULL, 10);
	psize  = strtoul(argv[3], NULL, 10) << 20;
	nloops = strtoul(argv[4], NULL, 10);

	bp = pmemblk_open(path, bsize);
	if (NULL == bp && ENOENT == errno) {
		bp = pmemblk_create(path, bsize, psize, 0644);
		if (NULL == bp) {
			perror(path);
			exit(1);
		}
		fprintf(stderr, "INFO: created; run again to time recovery\n");
		pmemblk_close(bp);
		exit(0);
	}
	else if (NULL == bp) {
		perror(path);
		exit(1);
	}

	for (; nloops > 0; nloops--) {
		pmemblk_close(bp);
		bp = pmemblk_open(path, bsize);
	}
	fprintf(stderr, "INFO: nblocks = %lu\n", pmemblk_nblock(bp));
	pmemblk_close(bp);

	return 0;

}  /* main() */


