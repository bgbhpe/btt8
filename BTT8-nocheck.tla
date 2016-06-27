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

(* NOTE:  This file contains just the BTT8 algorithm itself.  It does not
   contain any of the assertions or invariants that would be needed for
   verification.  See BTT8.tla for assertions and invariants.
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
      not entirely sure that I have achieved this).
      
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
        NWRITERS   be the number of writers,
  *)
CONSTANTS NFREE, NREADERS, NWRITERS

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
               
     define
       (* A shortcut for defining a table entry.  A translation table entry
          consists of a physical block address, a lane identifier, and a
          lane-specific cycle count.  The cycle counter is incremented each
          time a free block is consumed which helps the reader distinguish
          between different writes to the same physical block address.  We
          model the entry as a record: *)
       tentry(b, l, c) == [ pba |-> b, lane |-> l, cycle |-> c ]
       
     end define ;
     
     (* PersistEntry() is an abstraction of the operations needed to ensure
        that the currently visible value of the persistent translation table
        entry has been persisted to the backing store. *)
     macro PersistEntry() begin
       skip ;
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
       begin
         (* Load the translation cycle count.  In our real implementation, the
            lane ID will be read atomically with the cycle count, so we load it
            here also: *)
         RloadPreCycle: preCycle := visibleEntry.cycle ;
                        preLane := visibleEntry.lane ;
         
         (* Load the PBA: *)
         RloadPBA: pba := visibleEntry.pba ;
         
         (* Load the lane cycle: *)
         RloadLaneCycle: laneCycle := lanes[preLane].cycle ;
         
         (* If the pre-cycle is one ahead of the lane cycle, then the
            translation entry value may not have been persisted yet;
            persist it now: *)
         RpersistMapping: if (laneCycle + 1) = preCycle then PersistEntry() ; end if ;
         
         (* Copy the data block.  This is an abstract step, we don't actually
            model it here. *)
         RcopyBlock: skip ;
         
         (* Load the entry cycle again; if it changed, then we raced a write
            and we must restart: *)
         RcheckAtomicity: postCycle := visibleEntry.cycle ;
                          postLane := visibleEntry.lane ;
                          if postCycle /= preCycle \/ postLane /= preLane
                          then
                            goto RloadPreCycle ;
                          end if ;
                           
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
       begin
         (* Claim a lane.  This is an abstract notion here,
            we don't model the details of lane acquisition: *)
         Wstart: await \E l \in freeLanes : TRUE;
                 mylane := CHOOSE l \in freeLanes : TRUE ;
                 freeLanes := freeLanes \ { mylane } ;
                 newpba := lanes[mylane].freepba ;
                       
         (* Write the data to the block at newpba and persist it.
            Similar to the read case, this is an abstract step in this
            model. *)
         WwriteBlock: skip ;
         
         (* Snapshot the cycle and PBA of the current translation value.
            We read the two values in separate non-atomic steps.  This is
            okay: if our atomic compare-and-swap below succeeds, then we know
            these two reads were effectively atomic. *)
         WloadOldCycle: oldcycle := visibleEntry.cycle ;
                        oldlane := visibleEntry.lane ;
                        newcycle := lanes[mylane].cycle + 1 ;
         WloadOldPBA: oldpba := visibleEntry.pba ;
         
         (* Atomically swap our new translation in for the old translation. *)
         WswapMapping: if tentry(oldpba, oldlane, oldcycle) = visibleEntry
                       then
                         visibleEntry := tentry(newpba, mylane, newcycle) ;
                         swapped := TRUE ;
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
                        end if ;
                        freeLanes := freeLanes \cup { mylane } ;
     end process
     
   end algorithm *)
\* BEGIN TRANSLATION
\* END TRANSLATION

=============================================================================
\* Modification History
\* Last modified Fri Jun 24 12:42:43 EDT 2016 by BoylstonB
\* Created Mon Feb 29 10:03:24 EST 2016 by BoylstonB
