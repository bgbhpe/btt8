-------------------------------- MODULE BTT8 --------------------------------

(*
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
 *)

(* BTT8: A PlusCal model of a block translation table algorithm for use with
         NVDIMMs.
           
   A Block Translation Table (BTT) is a layer on top of byte-addressable
   persistent memory that provides block read/write atomicity.  Presented
   here is a BTT algorithm modelled in PlusCal.

   Our general approach to atomic block access is to use a translation table
   to map logical block addresses to physical block addresses, and to
   maintain a small pool of free physical blocks with which writes can be
   completed and persisted before being atomically published in the
   translation table.
   
   Regarding our model:
   
   -  As concurrent accesses to two different logical block addresses are
      independent of each other, we have modelled only concurrent access to a
      single logical block address.  (Not entirely true since the switch to
      a per-lane cycle count, but currently this is okay because there are
      no concurrent updates to the same per-lane cycle count)
      
   -  In our algorithm, the actual writing of user data to free physical
      blocks requires no interaction among processes, so the details are
      omitted here.  Instead, we model only the updates to the translation
      table entry as this is where readers and writers interact with each
      other.
      
   -  For the purposes of this model, the details of lane acquisition are
      omitted, and we instead use an abstract notion of a list of free lanes.
      
   -  We model the persistent memory that backs our translation table entry
      as follows:  We have a shared variable visibleEntry that contains the
      value of the translation entry that is visible in the cache coherency
      domain.  We allow that such a value may, at times, not be the same as
      the value stored on the NVDIMM itself.  In addition to visibleEntry, we
      assume that the environment provides an operation PersistEntry() that
      "persists" the value in visibleEntry by atomically delivering it to the
      NVDIMM.
      
   -  We assume that the environment provides an atomic compare-and-swap
      operation on visibleEntry.
      
   -  In this model, the reader can livelock in the face of continuous
      writes.  However, this is addressed in the actual implementation.
      
   We require the following of our BTT model:
   
   -  Persistence: reads return only data that is (or was at some point)
      persisted.  As the translation table entry controls which data is
      visible, we concern ourselves primarily with the persistence of the
      translation entry.
   
   -  Block atomicity: reads return only that data that was written by a
      single write; "torn" blocks are not returned.
      
   -  Serializability: any set of read/write operation executions allowed by
      the system has a valid total ordering.  I intend that this means that
      the BTT8 provides an "atomic register" as defined by Lamport (though I'm 
      not entirely sure that I have achieved this).  See the LamportAtomic
      invariant following the translation below.
      
   This model has been checked for termination, our assertions, and the
   LamportAtomic invariant.
   
   It has not been checked for liveness.  The writer has nothing to prevent
   its progress other than the availability of a free block; if NFREE > 0
   and if the free block assignment is fair, then writers will make progress.
   In the model given here, the reader, however, can fail to make progress
   in the face of continuous writes.  This has been addressed in the actual
   implementation.
 *)

EXTENDS Naturals, Sequences, FiniteSets, TLC

 (* Let NFREE      be the number of free blocks,
        NREADERS   be the number of readers,
        NCCREADERS be the number of concurrent readers,
        NWRITERS   be the number of writers,
        NPWRRESETS be the number of allowed power resets (0 or 1)
        
   NREADERS is the total number of reader processes while NCCREADERS is the
   number of reader processes allowed to be running at any given time.
   Using NREADERS and NCCREADERS enables you to force some number of
   serialized reads in order to verify such scenarios with shorter checker
   runtimes.  A similar effect can be achieved for writers using NFREE.
   
   NPWRRESETS is the number of power resets to simulate, either 0 or 1.  In
   this model, when a power reset occurs, all writers are terminated and
   all but one reader are terminated.  The remaining reader is reset back to
   its initial state.  The idea is to do a just single read after the reset
   to verify that LamportAtomic holds after an unexpected reset.
  *)
CONSTANTS NFREE, NREADERS, NWRITERS, NCCREADERS, NPWRRESETS

(* PlusCal options (-termination) *)

(* --algorithm BTT8Alg

     variables
       (* The globally visible value of the "persistent" table entry;
          the current value is not guaranteed to be persistent.  A real
          implementation would have an array of table entries, but since
          each table entry is independent, we only model one entry here
          for checking purposes.  Our initial mapping is for physical block
          address (PBA) 0, ostensibly written by lane 1 at cycle 0.*)
       visibleEntry = tentry(0, 1, 0) ;
       
       (* Our lanes.  Each lane has a free block and a cycle count.  In our
          model, PBA 0 is in use as the initial mapping, so our set of free
          blocks initially contains blocks 1 up to NFREE. *)
       lanes = [ l \in 1 .. NFREE |-> [ freepba |-> l, cycle |-> 0 ] ] ;
       
       (* List of free lanes *)
       freeLanes = DOMAIN lanes ;
               
       (* All of the following variables are needed only for our invariants
          and assertions while using TLC to check our model: *)
          
       (* Just a way to limit the number of concurrent readers *)
       readerSema = NCCREADERS ;
       
       (* Accumulated number of power resets: *)
       powerResets = 0 ;
          
       (* The history of persisted values from the persistent table
          entry.  The history is initialized to contain only our initial
          mapping.  entryHistory[Len(entryHistory)] is the current value that
          is persistent. *)
       entryHistory = << visibleEntry >> ;
     
       (* The set of PBAs that are "writable"; these blocks can be written
          to at any time and reading from one of these blocks will not
          be atomic.  This set is initialized to all of the PBAs in the
          free list. *)
       writableBlocks = { lanes[l].freepba : l \in DOMAIN lanes } ;
               
       (* A monotonically increasing clock value for timestamping our read
          and write events. *)
       clock = 0 ;
       
       (* The time the write started for the visibleEntry *)
       visibleEntryStartTime = clock ;
               
       (* For the purposes of deciding our LamportAtomic invariant, we keep
          track of all of our "register" access events.  An access event (be
          it read or write) is a record that contains the clock value at the
          time the access operation started, the clock value at the time the
          access operation finished, and the value read or written.
                  
          Our set of read events is initially empty and our set of write
          events initially contains only our initial persisted value. *)
        readEvents = { } ;
        writeEvents = { accessEvent(clock, clock, entryHistory[1]) } ;
               
     define
       (* A shortcut for defining a table entry.  A translation table entry
          consists of a physical block address, a lane identifier, and a
          lane-specific cycle count.  The cycle counter is incremented each
          time a free block is consumed which helps the reader distinguish
          between different writes to the same physical block address.  We
          model the entry as a record: *)
       tentry(b, l, c) == [ pba |-> b, lane |-> l, cycle |-> c ]
       
       (* All of the following definitions are needed only for our invariants
          and assertions while using TLC to check our model: *)
       
       (* Evaluates to TRUE if the given entry value is or was persistent.
          That is, if it appears in our history of persisted entry values. *)
       waspersistent(t) == \E i \in 1 .. Len(entryHistory) : entryHistory[i] = t
       
       (* A shortcut for defining a register access event.  See readEvents
          and writeEvents above. *)
       accessEvent(s, f, v) == [ start |-> s , finish |-> f , value |-> v ]
       
       (* The precedes and affects relations from Lamport. *)
       precedes(a, b) == a.finish < b.start
       affects(a, b) == a.start < b.finish
       
       (* phi(w) is the index of written value w in the persisted write
          history.  *)
       phi(w) == CHOOSE o \in 1 .. Len(entryHistory) : entryHistory[o] = w
       
       (* The set of writes unaffected by r (I_R in Lamport): *)
       unaffectedWrites(W, r) == { x.value : x \in { w \in W : ~affects(r, w) } }
       
       (* The set of writes that affect r (J_R in Lamport): *)
       affectedByWrites(W, r) == { x.value : x \in {w \in W : affects(w, r) } }
       
       (* The most recent/youngest/last write from W (a set of access
          events): *)
       youngest(W) == CHOOSE w \in W : \A x \in W : phi(w) >= phi(x)
       
       (* The set of writes "seen" by read event r: *)
       seen(W, r) ==      (affectedByWrites(W, r) \ unaffectedWrites(W, r))
                     \cup { youngest(unaffectedWrites(W, r)) }
       
       (* TRUE if the set of operation executions R \cup W is regular
          (Lamport: Axiom B4) *)
       isRegular(R, W) == \A r \in R : r.value \in seen(W, r)
       
       (* TRUE if the set of read executions R is serializable
          (Lamport: Proposition 5, requirement 3) *)
       isAtomic(R) == \A r \in R : \A s \in R : precedes(r, s) => phi(r.value) <= phi(s.value)
       
     end define ;
     
     (* Adds an access event to the set of read events with start time s,
        finish time f, and value v: *)
     macro RecordRead(s, f, v) begin
       readEvents :=      readEvents
                     \cup { accessEvent(s, f, v) } ;
     end macro ;
     
     (* Adds an access event to the set of write events with start time s,
        finish time f, and value v: *)
     macro RecordWrite(s, f, v) begin
       writeEvents :=      writeEvents
                      \cup { accessEvent(s, f, v) } ;
     end macro ;
     
     (* PersistEntry() is an abstraction of the operations needed to ensure
        that the currently visible value of the persistent translation table
        entry has been persisted to the backing store.  To enable our
        assertion checking, we add the current visible value to the end of
        the persisted history list if it is not there already.
        
        Note that in the real implementation, we use a 8 bytes for each of
        the cycle count and PBA components of the entry.  We cannot persist
        all 16 bytes atomically.  Fortunately, we only need the PBA to be
        persistent.  In our modelling here, however, we record the cycle
        count as well to enable our assertion checking (including our
        LamportAtomic invariant). *)
     macro PersistEntry() begin
       if entryHistory[Len(entryHistory)] /= visibleEntry
       then
         entryHistory := Append(entryHistory, visibleEntry) ;
         clock := clock + 1 ;
         RecordWrite(visibleEntryStartTime, clock, visibleEntry) ;
       end if ;
     end macro ;
     
     (* The remaining macros below are only used for our invariant and
        assertion checking: *)
     
     (* Stores the next clock value in t: *)
     macro GetTime(t) begin
       clock := clock + 1 ;
       t := clock ;
     end macro ;
     
     (* Our reader process: *)     
     process Reader \in 1 .. NREADERS
       variables
         preCycle = 0 ;  (* value of translation cycle before we copy data *)
         preLane = 0 ;   (* value of translation lane ID before we copy data *)
         pba = 0 ;       (* the PBA we're reading from *)
         laneCycle = 0 ; (* the current cycle count for the lane *)
         postCycle = 0 ; (* translation cycle after the data copy *)
         postLane = 0 ;  (* translation lane ID after the data copy *)
         waswritable = TRUE ;  (* TRUE if the PBA was writable while we were copying *)
         startTime = 0 ;
         endTime = 0 ;
       begin
         Rstart: await readerSema > 0 ;
                 readerSema := readerSema - 1 ;
                 GetTime(startTime) ;
                 
         (* Load the translation cycle count.  In our real implementation, the
            lane ID will be read atomically with the cycle count, so we load it
            here also: *)
         RloadPreCycle: preCycle := visibleEntry.cycle ;
                        preLane := visibleEntry.lane ;
         
         (* Load the PBA: *)
         RloadPBA: pba := visibleEntry.pba ;
         
         (* Load the lane cycle: *)
         RloadLaneCycle: laneCycle := lanes[preLane].cycle ;
         
         (* If the pre-cycle is one ahead of the lane cycle, then the translation
            entry value may not have been persisted yet; persist it now: *)
         RpersistMapping: if (laneCycle + 1) = preCycle then PersistEntry() ; end if ;
         
         (* Copy the data block.  This is an abstract step, we don't actually
            model it here, but we do record whether or not the PBA is
            writable at this time, which enables our assertion below. *)
         RcopyBlock: waswritable := pba \in writableBlocks ;
         
         (* Load the entry cycle again; if it changed, then we raced a write
            and we must restart: *)
         RcheckAtomicity: postCycle := visibleEntry.cycle ;
                          postLane := visibleEntry.lane ;
                          if postCycle /= preCycle \/ postLane /= preLane
                          then
                            goto RloadPreCycle ;
                          end if ;
                           
         (* Ensure that: 1. the translation entry was persistent, and 2. the
            PBA we read from was not writable while we were reading it: *)
         Rassertions: assert waspersistent(tentry(pba, preLane, preCycle)) ;
                      assert ~waswritable ;
                      (* Record the read for invariant analysis: *)
                      GetTime(endTime) ;
                      RecordRead(startTime, endTime, tentry(pba, preLane, preCycle)) ;
                      readerSema := readerSema + 1 ;
     end process
     
     (* Our writer process: *)
     process Writer \in (NREADERS + 1) .. (NREADERS + NWRITERS)
       variables
         oldcycle = 0 ;    (* the old translation cycle *)
         oldlane = 0 ;     (* the old lane ID *)
         oldpba = 0 ;      (* the old translation PBA *)
         mylane = 0 ;
         newcycle = 0 ;    (* the new cycle value *)
         newpba = 0 ;      (* the new PBA *)
         swapped = FALSE ; (* TRUE if our atomic CAS happened *)
         startTime = 0 ;
       begin
         (* Claim a lane.  This is an abstract notion here,
            we don't model the details of lane acquisition: *)
         Wstart: await \E l \in freeLanes : TRUE;
                 mylane := CHOOSE l \in freeLanes : TRUE ;
                 freeLanes := freeLanes \ { mylane } ;
                 newpba := lanes[mylane].freepba ;
                 GetTime(startTime) ;
                       
         (* Write the data to the block at newpba and persist it.
            Similar to the read case, this is an abstract step in this
            model.  Instead, we assert that this physical block is
            writable: *)
         WwriteBlock: assert newpba \in writableBlocks ;
         
         (* Snapshot the cycle and PBA of the current translation value.
            We read the two values in separate non-atomic steps.  This is
            okay: if our atomic compare-and-swap below succeeds, then we know
            these two reads were effectively atomic. *)
         WloadOldCycle: oldcycle := visibleEntry.cycle ;
                        oldlane := visibleEntry.lane ;
                        newcycle := lanes[mylane].cycle + 1 ;
         WloadOldPBA: oldpba := visibleEntry.pba ;
         
         (* Atomically swap our new translation in for the old translation.
            Also, at this point, if our swap is successful, then the block at
            newpba is no longer writable: *)
         WswapMapping: if tentry(oldpba, oldlane, oldcycle) = visibleEntry
                       then
                         visibleEntry := tentry(newpba, mylane, newcycle) ;
                         visibleEntryStartTime := startTime ;
                         swapped := TRUE ;
                         writableBlocks := writableBlocks \ { newpba } ;
                       end if ;
                      
         (* Persist the updated translation entry... *)
         WpersistMapping: if swapped
                          then
                            PersistEntry() ;
                          end if ;
         
         (* ...and then, if we swapped, update our cycle count: *)
         WupdateCycle: if swapped
                       then
                         lanes := [lanes EXCEPT ![mylane] = [freepba |-> lanes[mylane].freepba, cycle |-> newcycle]] ;
                       end if ;
         
         (* If we swapped, then put the old PBA on the free list and mark if
            writable.  If not, return the new PBA to the free pool. *)
         WputFreeBlock: if swapped
                        then
                          lanes := [lanes EXCEPT ![mylane] = [freepba |-> oldpba, cycle |-> newcycle]] ;
                          assert oldpba \notin writableBlocks ;
                          writableBlocks := writableBlocks \cup { oldpba };
                        else
                          assert newpba = lanes[mylane].freepba ;
                          assert newpba \in writableBlocks ;
                        end if ;
                        assert mylane \notin freeLanes ;
                        freeLanes := freeLanes \cup { mylane } ;
     end process
     
   end algorithm *)
\* BEGIN TRANSLATION
\* Process variable startTime of process Reader at line 248 col 10 changed to startTime_
VARIABLES visibleEntry, lanes, freeLanes, readerSema, powerResets, 
          entryHistory, writableBlocks, clock, visibleEntryStartTime, 
          readEvents, writeEvents, pc

(* define statement *)
tentry(b, l, c) == [ pba |-> b, lane |-> l, cycle |-> c ]






waspersistent(t) == \E i \in 1 .. Len(entryHistory) : entryHistory[i] = t



accessEvent(s, f, v) == [ start |-> s , finish |-> f , value |-> v ]


precedes(a, b) == a.finish < b.start
affects(a, b) == a.start < b.finish



phi(w) == CHOOSE o \in 1 .. Len(entryHistory) : entryHistory[o] = w


unaffectedWrites(W, r) == { x.value : x \in { w \in W : ~affects(r, w) } }


affectedByWrites(W, r) == { x.value : x \in {w \in W : affects(w, r) } }



youngest(W) == CHOOSE w \in W : \A x \in W : phi(w) >= phi(x)


seen(W, r) ==      (affectedByWrites(W, r) \ unaffectedWrites(W, r))
              \cup { youngest(unaffectedWrites(W, r)) }



isRegular(R, W) == \A r \in R : r.value \in seen(W, r)



isAtomic(R) == \A r \in R : \A s \in R : precedes(r, s) => phi(r.value) <= phi(s.value)

VARIABLES preCycle, preLane, pba, laneCycle, postCycle, postLane, waswritable, 
          startTime_, endTime, oldcycle, oldlane, oldpba, mylane, newcycle, 
          newpba, swapped, startTime

vars == << visibleEntry, lanes, freeLanes, readerSema, powerResets, 
           entryHistory, writableBlocks, clock, visibleEntryStartTime, 
           readEvents, writeEvents, pc, preCycle, preLane, pba, laneCycle, 
           postCycle, postLane, waswritable, startTime_, endTime, oldcycle, 
           oldlane, oldpba, mylane, newcycle, newpba, swapped, startTime >>

ProcSet == (1 .. NREADERS) \cup ((NREADERS + 1) .. (NREADERS + NWRITERS))

Init == (* Global variables *)
        /\ visibleEntry = tentry(0, 1, 0)
        /\ lanes = [ l \in 1 .. NFREE |-> [ freepba |-> l, cycle |-> 0 ] ]
        /\ freeLanes = DOMAIN lanes
        /\ readerSema = NCCREADERS
        /\ powerResets = 0
        /\ entryHistory = << visibleEntry >>
        /\ writableBlocks = { lanes[l].freepba : l \in DOMAIN lanes }
        /\ clock = 0
        /\ visibleEntryStartTime = clock
        /\ readEvents = { }
        /\ writeEvents = { accessEvent(clock, clock, entryHistory[1]) }
        (* Process Reader *)
        /\ preCycle = [self \in 1 .. NREADERS |-> 0]
        /\ preLane = [self \in 1 .. NREADERS |-> 0]
        /\ pba = [self \in 1 .. NREADERS |-> 0]
        /\ laneCycle = [self \in 1 .. NREADERS |-> 0]
        /\ postCycle = [self \in 1 .. NREADERS |-> 0]
        /\ postLane = [self \in 1 .. NREADERS |-> 0]
        /\ waswritable = [self \in 1 .. NREADERS |-> TRUE]
        /\ startTime_ = [self \in 1 .. NREADERS |-> 0]
        /\ endTime = [self \in 1 .. NREADERS |-> 0]
        (* Process Writer *)
        /\ oldcycle = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ oldlane = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ oldpba = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ mylane = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ newcycle = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ newpba = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ swapped = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> FALSE]
        /\ startTime = [self \in (NREADERS + 1) .. (NREADERS + NWRITERS) |-> 0]
        /\ pc = [self \in ProcSet |-> CASE self \in 1 .. NREADERS -> "Rstart"
                                        [] self \in (NREADERS + 1) .. (NREADERS + NWRITERS) -> "Wstart"]

Rstart(self) == /\ pc[self] = "Rstart"
                /\ readerSema > 0
                /\ readerSema' = readerSema - 1
                /\ clock' = clock + 1
                /\ startTime_' = [startTime_ EXCEPT ![self] = clock']
                /\ pc' = [pc EXCEPT ![self] = "RloadPreCycle"]
                /\ UNCHANGED << visibleEntry, lanes, freeLanes, powerResets, 
                                entryHistory, writableBlocks, 
                                visibleEntryStartTime, readEvents, writeEvents, 
                                preCycle, preLane, pba, laneCycle, postCycle, 
                                postLane, waswritable, endTime, oldcycle, 
                                oldlane, oldpba, mylane, newcycle, newpba, 
                                swapped, startTime >>

RloadPreCycle(self) == /\ pc[self] = "RloadPreCycle"
                       /\ preCycle' = [preCycle EXCEPT ![self] = visibleEntry.cycle]
                       /\ preLane' = [preLane EXCEPT ![self] = visibleEntry.lane]
                       /\ pc' = [pc EXCEPT ![self] = "RloadPBA"]
                       /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                       readerSema, powerResets, entryHistory, 
                                       writableBlocks, clock, 
                                       visibleEntryStartTime, readEvents, 
                                       writeEvents, pba, laneCycle, postCycle, 
                                       postLane, waswritable, startTime_, 
                                       endTime, oldcycle, oldlane, oldpba, 
                                       mylane, newcycle, newpba, swapped, 
                                       startTime >>

RloadPBA(self) == /\ pc[self] = "RloadPBA"
                  /\ pba' = [pba EXCEPT ![self] = visibleEntry.pba]
                  /\ pc' = [pc EXCEPT ![self] = "RloadLaneCycle"]
                  /\ UNCHANGED << visibleEntry, lanes, freeLanes, readerSema, 
                                  powerResets, entryHistory, writableBlocks, 
                                  clock, visibleEntryStartTime, readEvents, 
                                  writeEvents, preCycle, preLane, laneCycle, 
                                  postCycle, postLane, waswritable, startTime_, 
                                  endTime, oldcycle, oldlane, oldpba, mylane, 
                                  newcycle, newpba, swapped, startTime >>

RloadLaneCycle(self) == /\ pc[self] = "RloadLaneCycle"
                        /\ laneCycle' = [laneCycle EXCEPT ![self] = lanes[preLane[self]].cycle]
                        /\ pc' = [pc EXCEPT ![self] = "RpersistMapping"]
                        /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                        readerSema, powerResets, entryHistory, 
                                        writableBlocks, clock, 
                                        visibleEntryStartTime, readEvents, 
                                        writeEvents, preCycle, preLane, pba, 
                                        postCycle, postLane, waswritable, 
                                        startTime_, endTime, oldcycle, oldlane, 
                                        oldpba, mylane, newcycle, newpba, 
                                        swapped, startTime >>

RpersistMapping(self) == /\ pc[self] = "RpersistMapping"
                         /\ IF (laneCycle[self] + 1) = preCycle[self]
                               THEN /\ IF entryHistory[Len(entryHistory)] /= visibleEntry
                                          THEN /\ entryHistory' = Append(entryHistory, visibleEntry)
                                               /\ clock' = clock + 1
                                               /\ writeEvents' =      writeEvents
                                                                 \cup { accessEvent(visibleEntryStartTime, clock', visibleEntry) }
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << entryHistory, 
                                                               clock, 
                                                               writeEvents >>
                               ELSE /\ TRUE
                                    /\ UNCHANGED << entryHistory, clock, 
                                                    writeEvents >>
                         /\ pc' = [pc EXCEPT ![self] = "RcopyBlock"]
                         /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                         readerSema, powerResets, 
                                         writableBlocks, visibleEntryStartTime, 
                                         readEvents, preCycle, preLane, pba, 
                                         laneCycle, postCycle, postLane, 
                                         waswritable, startTime_, endTime, 
                                         oldcycle, oldlane, oldpba, mylane, 
                                         newcycle, newpba, swapped, startTime >>

RcopyBlock(self) == /\ pc[self] = "RcopyBlock"
                    /\ waswritable' = [waswritable EXCEPT ![self] = pba[self] \in writableBlocks]
                    /\ pc' = [pc EXCEPT ![self] = "RcheckAtomicity"]
                    /\ UNCHANGED << visibleEntry, lanes, freeLanes, readerSema, 
                                    powerResets, entryHistory, writableBlocks, 
                                    clock, visibleEntryStartTime, readEvents, 
                                    writeEvents, preCycle, preLane, pba, 
                                    laneCycle, postCycle, postLane, startTime_, 
                                    endTime, oldcycle, oldlane, oldpba, mylane, 
                                    newcycle, newpba, swapped, startTime >>

RcheckAtomicity(self) == /\ pc[self] = "RcheckAtomicity"
                         /\ postCycle' = [postCycle EXCEPT ![self] = visibleEntry.cycle]
                         /\ postLane' = [postLane EXCEPT ![self] = visibleEntry.lane]
                         /\ IF postCycle'[self] /= preCycle[self] \/ postLane'[self] /= preLane[self]
                               THEN /\ pc' = [pc EXCEPT ![self] = "RloadPreCycle"]
                               ELSE /\ pc' = [pc EXCEPT ![self] = "Rassertions"]
                         /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                         readerSema, powerResets, entryHistory, 
                                         writableBlocks, clock, 
                                         visibleEntryStartTime, readEvents, 
                                         writeEvents, preCycle, preLane, pba, 
                                         laneCycle, waswritable, startTime_, 
                                         endTime, oldcycle, oldlane, oldpba, 
                                         mylane, newcycle, newpba, swapped, 
                                         startTime >>

Rassertions(self) == /\ pc[self] = "Rassertions"
                     /\ Assert(waspersistent(tentry(pba[self], preLane[self], preCycle[self])), 
                               "Failure of assertion at line 287, column 23.")
                     /\ Assert(~waswritable[self], 
                               "Failure of assertion at line 288, column 23.")
                     /\ clock' = clock + 1
                     /\ endTime' = [endTime EXCEPT ![self] = clock']
                     /\ readEvents' =      readEvents
                                      \cup { accessEvent(startTime_[self], endTime'[self], (tentry(pba[self], preLane[self], preCycle[self]))) }
                     /\ readerSema' = readerSema + 1
                     /\ pc' = [pc EXCEPT ![self] = "Done"]
                     /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                     powerResets, entryHistory, writableBlocks, 
                                     visibleEntryStartTime, writeEvents, 
                                     preCycle, preLane, pba, laneCycle, 
                                     postCycle, postLane, waswritable, 
                                     startTime_, oldcycle, oldlane, oldpba, 
                                     mylane, newcycle, newpba, swapped, 
                                     startTime >>

Reader(self) == Rstart(self) \/ RloadPreCycle(self) \/ RloadPBA(self)
                   \/ RloadLaneCycle(self) \/ RpersistMapping(self)
                   \/ RcopyBlock(self) \/ RcheckAtomicity(self)
                   \/ Rassertions(self)

Wstart(self) == /\ pc[self] = "Wstart"
                /\ \E l \in freeLanes : TRUE
                /\ mylane' = [mylane EXCEPT ![self] = CHOOSE l \in freeLanes : TRUE]
                /\ freeLanes' = freeLanes \ { mylane'[self] }
                /\ newpba' = [newpba EXCEPT ![self] = lanes[mylane'[self]].freepba]
                /\ clock' = clock + 1
                /\ startTime' = [startTime EXCEPT ![self] = clock']
                /\ pc' = [pc EXCEPT ![self] = "WwriteBlock"]
                /\ UNCHANGED << visibleEntry, lanes, readerSema, powerResets, 
                                entryHistory, writableBlocks, 
                                visibleEntryStartTime, readEvents, writeEvents, 
                                preCycle, preLane, pba, laneCycle, postCycle, 
                                postLane, waswritable, startTime_, endTime, 
                                oldcycle, oldlane, oldpba, newcycle, swapped >>

WwriteBlock(self) == /\ pc[self] = "WwriteBlock"
                     /\ Assert(newpba[self] \in writableBlocks, 
                               "Failure of assertion at line 319, column 23.")
                     /\ pc' = [pc EXCEPT ![self] = "WloadOldCycle"]
                     /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                     readerSema, powerResets, entryHistory, 
                                     writableBlocks, clock, 
                                     visibleEntryStartTime, readEvents, 
                                     writeEvents, preCycle, preLane, pba, 
                                     laneCycle, postCycle, postLane, 
                                     waswritable, startTime_, endTime, 
                                     oldcycle, oldlane, oldpba, mylane, 
                                     newcycle, newpba, swapped, startTime >>

WloadOldCycle(self) == /\ pc[self] = "WloadOldCycle"
                       /\ oldcycle' = [oldcycle EXCEPT ![self] = visibleEntry.cycle]
                       /\ oldlane' = [oldlane EXCEPT ![self] = visibleEntry.lane]
                       /\ newcycle' = [newcycle EXCEPT ![self] = lanes[mylane[self]].cycle + 1]
                       /\ pc' = [pc EXCEPT ![self] = "WloadOldPBA"]
                       /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                       readerSema, powerResets, entryHistory, 
                                       writableBlocks, clock, 
                                       visibleEntryStartTime, readEvents, 
                                       writeEvents, preCycle, preLane, pba, 
                                       laneCycle, postCycle, postLane, 
                                       waswritable, startTime_, endTime, 
                                       oldpba, mylane, newpba, swapped, 
                                       startTime >>

WloadOldPBA(self) == /\ pc[self] = "WloadOldPBA"
                     /\ oldpba' = [oldpba EXCEPT ![self] = visibleEntry.pba]
                     /\ pc' = [pc EXCEPT ![self] = "WswapMapping"]
                     /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                     readerSema, powerResets, entryHistory, 
                                     writableBlocks, clock, 
                                     visibleEntryStartTime, readEvents, 
                                     writeEvents, preCycle, preLane, pba, 
                                     laneCycle, postCycle, postLane, 
                                     waswritable, startTime_, endTime, 
                                     oldcycle, oldlane, mylane, newcycle, 
                                     newpba, swapped, startTime >>

WswapMapping(self) == /\ pc[self] = "WswapMapping"
                      /\ IF tentry(oldpba[self], oldlane[self], oldcycle[self]) = visibleEntry
                            THEN /\ visibleEntry' = tentry(newpba[self], mylane[self], newcycle[self])
                                 /\ visibleEntryStartTime' = startTime[self]
                                 /\ swapped' = [swapped EXCEPT ![self] = TRUE]
                                 /\ writableBlocks' = writableBlocks \ { newpba[self] }
                            ELSE /\ TRUE
                                 /\ UNCHANGED << visibleEntry, writableBlocks, 
                                                 visibleEntryStartTime, 
                                                 swapped >>
                      /\ pc' = [pc EXCEPT ![self] = "WpersistMapping"]
                      /\ UNCHANGED << lanes, freeLanes, readerSema, 
                                      powerResets, entryHistory, clock, 
                                      readEvents, writeEvents, preCycle, 
                                      preLane, pba, laneCycle, postCycle, 
                                      postLane, waswritable, startTime_, 
                                      endTime, oldcycle, oldlane, oldpba, 
                                      mylane, newcycle, newpba, startTime >>

WpersistMapping(self) == /\ pc[self] = "WpersistMapping"
                         /\ IF swapped[self]
                               THEN /\ IF entryHistory[Len(entryHistory)] /= visibleEntry
                                          THEN /\ entryHistory' = Append(entryHistory, visibleEntry)
                                               /\ clock' = clock + 1
                                               /\ writeEvents' =      writeEvents
                                                                 \cup { accessEvent(visibleEntryStartTime, clock', visibleEntry) }
                                          ELSE /\ TRUE
                                               /\ UNCHANGED << entryHistory, 
                                                               clock, 
                                                               writeEvents >>
                               ELSE /\ TRUE
                                    /\ UNCHANGED << entryHistory, clock, 
                                                    writeEvents >>
                         /\ pc' = [pc EXCEPT ![self] = "WupdateCycle"]
                         /\ UNCHANGED << visibleEntry, lanes, freeLanes, 
                                         readerSema, powerResets, 
                                         writableBlocks, visibleEntryStartTime, 
                                         readEvents, preCycle, preLane, pba, 
                                         laneCycle, postCycle, postLane, 
                                         waswritable, startTime_, endTime, 
                                         oldcycle, oldlane, oldpba, mylane, 
                                         newcycle, newpba, swapped, startTime >>

WupdateCycle(self) == /\ pc[self] = "WupdateCycle"
                      /\ IF swapped[self]
                            THEN /\ lanes' = [lanes EXCEPT ![mylane[self]] = [freepba |-> lanes[mylane[self]].freepba, cycle |-> newcycle[self]]]
                            ELSE /\ TRUE
                                 /\ lanes' = lanes
                      /\ pc' = [pc EXCEPT ![self] = "WputFreeBlock"]
                      /\ UNCHANGED << visibleEntry, freeLanes, readerSema, 
                                      powerResets, entryHistory, 
                                      writableBlocks, clock, 
                                      visibleEntryStartTime, readEvents, 
                                      writeEvents, preCycle, preLane, pba, 
                                      laneCycle, postCycle, postLane, 
                                      waswritable, startTime_, endTime, 
                                      oldcycle, oldlane, oldpba, mylane, 
                                      newcycle, newpba, swapped, startTime >>

WputFreeBlock(self) == /\ pc[self] = "WputFreeBlock"
                       /\ IF swapped[self]
                             THEN /\ lanes' = [lanes EXCEPT ![mylane[self]] = [freepba |-> oldpba[self], cycle |-> newcycle[self]]]
                                  /\ Assert(oldpba[self] \notin writableBlocks, 
                                            "Failure of assertion at line 359, column 27.")
                                  /\ writableBlocks' = (writableBlocks \cup { oldpba[self] })
                             ELSE /\ Assert(newpba[self] = lanes[mylane[self]].freepba, 
                                            "Failure of assertion at line 362, column 27.")
                                  /\ Assert(newpba[self] \in writableBlocks, 
                                            "Failure of assertion at line 363, column 27.")
                                  /\ UNCHANGED << lanes, writableBlocks >>
                       /\ Assert(mylane[self] \notin freeLanes, 
                                 "Failure of assertion at line 365, column 25.")
                       /\ freeLanes' = (freeLanes \cup { mylane[self] })
                       /\ pc' = [pc EXCEPT ![self] = "Done"]
                       /\ UNCHANGED << visibleEntry, readerSema, powerResets, 
                                       entryHistory, clock, 
                                       visibleEntryStartTime, readEvents, 
                                       writeEvents, preCycle, preLane, pba, 
                                       laneCycle, postCycle, postLane, 
                                       waswritable, startTime_, endTime, 
                                       oldcycle, oldlane, oldpba, mylane, 
                                       newcycle, newpba, swapped, startTime >>

Writer(self) == Wstart(self) \/ WwriteBlock(self) \/ WloadOldCycle(self)
                   \/ WloadOldPBA(self) \/ WswapMapping(self)
                   \/ WpersistMapping(self) \/ WupdateCycle(self)
                   \/ WputFreeBlock(self)

Next == (\E self \in 1 .. NREADERS: Reader(self))
           \/ (\E self \in (NREADERS + 1) .. (NREADERS + NWRITERS): Writer(self))
           \/ (* Disjunct to prevent deadlock on termination *)
              ((\A self \in ProcSet: pc[self] = "Done") /\ UNCHANGED vars)
              
PowerReset == /\ powerResets' = powerResets + 1
              (* recovery of volatile global state: *)
              /\ visibleEntry' = entryHistory[Len(entryHistory)]
              /\ visibleEntryStartTime' = clock
              /\ readerSema' = NCCREADERS
              /\ writableBlocks' = 0 .. NFREE \ { visibleEntry'.pba }
              /\ LET blocks == CHOOSE s \in [1 .. Cardinality(writableBlocks') -> writableBlocks'] : TRUE
                  IN lanes' = [ l \in 1 .. NFREE |->
                                    CASE l /= visibleEntry'.lane -> [freepba |-> blocks[l], cycle |-> 0]
                                      [] l = visibleEntry'.lane -> [freepba |-> blocks[l], cycle |-> visibleEntry'.cycle] ]
              /\ freeLanes' = DOMAIN lanes'
              (* Only need to reset one reader, but easier to hit them all: *)
              /\ preCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ preLane' = [self \in 1 .. NREADERS |-> 0]
              /\ pba' = [self \in 1 .. NREADERS |-> 0]
              /\ laneCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ postCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ postLane' = [self \in 1 .. NREADERS |-> 0]
              /\ waswritable' = [self \in 1 .. NREADERS |-> TRUE]
              /\ startTime_' = [self \in 1 .. NREADERS |-> 0]
              /\ endTime' = [self \in 1 .. NREADERS |-> 0]
              (* Reset one reader, terminate all other processes.  This should be
                 enough to test our LamportAtomic invariant. *)
              /\ pc' = [self \in ProcSet |-> CASE self \in 1 .. 1 -> "Rstart"
                                               [] self \notin 1 .. 1 -> "Done"]
              /\ UNCHANGED << entryHistory, clock, readEvents, writeEvents,
                              (* writers are terminated; no need to alter state *)
                              oldcycle, oldlane, oldpba, mylane, newcycle, newpba,
                              swapped, startTime >>
              
PowerNext == Next \/ ((powerResets < NPWRRESETS) /\ PowerReset)

Spec == /\ Init /\ [][PowerNext]_vars
        /\ \A self \in 1 .. NREADERS : WF_vars(Reader(self))
        /\ \A self \in (NREADERS + 1) .. (NREADERS + NWRITERS) : WF_vars(Writer(self))

Termination == <>(\A self \in ProcSet: pc[self] = "Done")

\* END TRANSLATION

(* Additional TLA for our flaky power supply.  This needs to be manually
   added to the translation above.
   
PowerReset == /\ powerResets' = powerResets + 1
              (* recovery of volatile global state: *)
              /\ visibleEntry' = entryHistory[Len(entryHistory)]
              /\ visibleEntryStartTime' = clock
              /\ readerSema' = NCCREADERS
              /\ writableBlocks' = 0 .. NFREE \ { visibleEntry'.pba }
              /\ LET blocks == CHOOSE s \in [1 .. Cardinality(writableBlocks') -> writableBlocks'] : TRUE
                  IN lanes' = [ l \in 1 .. NFREE |->
                                    CASE l /= visibleEntry'.lane -> [freepba |-> blocks[l], cycle |-> 0]
                                      [] l = visibleEntry'.lane -> [freepba |-> blocks[l], cycle |-> visibleEntry'.cycle] ]
              /\ freeLanes' = DOMAIN lanes'
              (* Only need to reset one reader, but easier to hit them all: *)
              /\ preCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ preLane' = [self \in 1 .. NREADERS |-> 0]
              /\ pba' = [self \in 1 .. NREADERS |-> 0]
              /\ laneCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ postCycle' = [self \in 1 .. NREADERS |-> 0]
              /\ postLane' = [self \in 1 .. NREADERS |-> 0]
              /\ waswritable' = [self \in 1 .. NREADERS |-> TRUE]
              /\ startTime_' = [self \in 1 .. NREADERS |-> 0]
              /\ endTime' = [self \in 1 .. NREADERS |-> 0]
              (* Reset one reader, terminate all other processes.  This should be
                 enough to test our LamportAtomic invariant. *)
              /\ pc' = [self \in ProcSet |-> CASE self \in 1 .. 1 -> "Rstart"
                                               [] self \notin 1 .. 1 -> "Done"]
              /\ UNCHANGED << entryHistory, clock, readEvents, writeEvents,
                              (* writers are terminated; no need to alter state *)
                              oldcycle, oldlane, oldpba, mylane, newcycle, newpba,
                              swapped, startTime >>
              
PowerNext == Next \/ ((powerResets < NPWRRESETS) /\ PowerReset)

 *)

(* Invariant LamportAtomic: TRUE if the "register" is "atomic" as provided by
   (Lamport: Proposition 5).  We check this only once we have terminated as 
   there are intermediate states that do not satisfy it.
   
   I am not entirely sure that I have interpreted Lamport's paper correctly.
   
   (Lamport: Proposition 5) requires that there be only one writer and that
   the "register" be "regular".  I think that we satisfy these as follows:
   
   -  I believe that entryHistory provides a total ordering of write operations
      even with multiple concurrent writers, in which case the writes are
      serializable and appear to readers to have been executed by a single
      writer.
   
   -  I think that requirements (1) and (2) of (Lamport: Prop 5) imply that
      the register is "regular", and we include these requirements in our
      invariant.
 *)
Terminated == \A self \in ProcSet: pc[self] = "Done"
LamportAtomic == Terminated =>    isRegular(readEvents, writeEvents)
                               /\ isAtomic(readEvents)

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 12:42:43 EDT 2016 by BoylstonB
\* Created Mon Feb 29 10:03:24 EST 2016 by BoylstonB
