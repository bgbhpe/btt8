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
#include <pthread.h>
#include <unistd.h>

#include <libpmemblk.h>


uint64_t NTHREADS = 0;

uint64_t NWRITES  = 0;
uint64_t WTTIMENS = 0;
uint64_t WLATLO   = 0xffffffffffffffffULL;
uint64_t WLATHI   = 0;

uint64_t NREADS   = 0;
uint64_t RTTIMENS = 0;
uint64_t RLATLO   = 0xffffffffffffffffULL;
uint64_t RLATHI   = 0;

pthread_mutex_t   STATLOCK = PTHREAD_MUTEX_INITIALIZER;


static __thread struct timespec   stopwatch;

void
stopwatch_reset(void)
{
	clock_gettime(CLOCK_MONOTONIC_RAW, &stopwatch);

}  /* stopwatch_reset() */

uint64_t
stopwatch_split(void)
{
	struct timespec   tnow;

	clock_gettime(CLOCK_MONOTONIC_RAW, &tnow);

	tnow.tv_sec -= stopwatch.tv_sec;
	if (tnow.tv_nsec > stopwatch.tv_nsec) {
		tnow.tv_nsec -= stopwatch.tv_nsec;
	} else {
		tnow.tv_sec -= 1;
		tnow.tv_nsec = 1000000000 + tnow.tv_nsec - stopwatch.tv_nsec;
	}

	return ((uint64_t)tnow.tv_sec * 1000000000) + (uint64_t)tnow.tv_nsec;

}  /* stopwatch_split() */


void*
writer(
	void* pta
)
{
	PMEMblkpool** volatile   pbp     = pta;
	PMEMblkpool*             bp;
	size_t                   bsize   = pmemblk_bsize(*pbp);
	void*                    buf     = malloc(bsize);

	uint64_t                 nwrites = 0;
	uint64_t                 ttimens = 0;
	uint64_t                 latlo   = 0xffffffffffffffffULL;
	uint64_t                 lathi   = 0;
	uint64_t                 lat;

	while ((bp = *pbp)) {

		stopwatch_reset();
		pmemblk_write(bp, buf, 0);
		lat = stopwatch_split();

		if (lat > lathi)
			lathi = lat;
		if (lat < latlo)
			latlo = lat;

		ttimens += lat;

		nwrites++;
	}

	pthread_mutex_lock(&STATLOCK);
	NWRITES  += nwrites;
	WTTIMENS += ttimens;
	if (lathi > WLATHI)
		WLATHI = lathi;
	if (latlo < WLATLO)
		WLATLO = latlo;
	pthread_mutex_unlock(&STATLOCK);

	return NULL;

}  /* writer() */


void*
reader(
	void* pta
)
{
	PMEMblkpool** volatile   pbp     = pta;
	PMEMblkpool*             bp;
	size_t                   bsize   = pmemblk_bsize(*pbp);
	void*                    buf     = malloc(bsize);

	uint64_t                 nreads  = 0;
	uint64_t                 ttimens = 0;
	uint64_t                 latlo   = 0xffffffffffffffffULL;
	uint64_t                 lathi   = 0;
	uint64_t                 lat;

	while ((bp = *pbp)) {

		stopwatch_reset();
		pmemblk_read(bp, buf, 0);
		lat = stopwatch_split();

		if (lat > lathi)
			lathi = lat;
		if (lat < latlo)
			latlo = lat;

		ttimens += lat;

		nreads++;
	}

	pthread_mutex_lock(&STATLOCK);
	NREADS   += nreads;
	RTTIMENS += ttimens;
	if (lathi > RLATHI)
		RLATHI = lathi;
	if (latlo < RLATLO)
		RLATLO = latlo;
	pthread_mutex_unlock(&STATLOCK);

	return NULL;

}  /* reader() */


int
main(
	int   argc,
	char* argv[]
)
{
	char*                   path;
	uint64_t                bsize;
	uint64_t                psize;
	uint64_t                runtime;
	uint64_t                nthreads;

	PMEMblkpool*            bp;
	volatile PMEMblkpool*   tbp;
	pthread_t*              threads;

	if (argc < 6) {
		fprintf(stderr, "ERROR: usage: starve PATH BSIZE PSIZEMB RUNTIMESECS NTHREADS1 [NTHREADS2 ...]\n");
		exit(1);
	}
	path    = argv[1];
	bsize   = strtoul(argv[2], NULL, 10);
	psize   = strtoul(argv[3], NULL, 10) << 20;
	runtime = strtoul(argv[4], NULL, 10);
	argc -= 5;
	argv += 5;

	bp = pmemblk_open(path, bsize);
	if (NULL == bp && ENOENT == errno) {
		bp = pmemblk_create(path, bsize, psize, 0644);
		if (NULL == bp) {
			perror(path);
			exit(1);
		}
		fprintf(stderr, "INFO: created\n");
	}
	else if (NULL == bp) {
		perror(path);
		exit(1);
	}

	/* XXX we do not reset the stats on each loop.  this was convenient
	 *     for my testing, but doesn't really mesh well with the purported
	 *     tool interface, which allows you to change the number of
	 *     writers mid-run, which would make the printed stats less useful.
	 */
	fprintf(stderr, "WARN: stats are cumulative, even if thread count is varied\n");

	printf("rorw nwriters avglatns minlatns maxlatns\n");
	while (argc-- > 0) {
		nthreads = NTHREADS = strtoul(*argv++, NULL, 10);

		threads = malloc((nthreads + 2) * sizeof(*threads));
		threads[nthreads + 1] = 0;

		tbp = bp;
		for (; nthreads > 0; nthreads--) {
			pthread_create(&threads[nthreads], NULL, writer, &tbp);
		}

		pthread_create(&threads[0], NULL, reader, &tbp);

		usleep(runtime * 1000 * 1000);
		tbp = NULL;

		while (*threads)
			pthread_join(*threads++, NULL);

		free(threads - (NTHREADS + 1));

		if (NREADS)
			printf("R %lu %lu %lu %lu\n",
			       NTHREADS, (RTTIMENS / NREADS), RLATLO, RLATHI);
		if (NWRITES)
			printf("W %lu %lu %lu %lu\n",
			       NTHREADS, (WTTIMENS / NWRITES), WLATLO, WLATHI);
	}

	return 0;

}  /* main() */


