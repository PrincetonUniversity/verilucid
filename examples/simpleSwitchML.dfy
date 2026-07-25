/*
    Minimal implementation of switchML's switch-side in-network aggregator.

    Verified properties that: 
        1. aggregation loop increments to correct values
        2. generate an aggregate chunk send when an offset is complete

    The interesting thing here is that the memory layout on the 
    switch is reversed of how you would intuitively implement. 
    Verification helps us reason that the behavior is the same 
    as a simpler reference model.
    We can illustrate this more clearly in the program, and this might be 
    a nice program to use as an example in a slide deck.
*/

include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)


    const nWorkers := 8
    const nParams := 32 // number of arrays // TRANSLATION NOTE: this translates to a size in Lucid, not a const.
    const nSlots := 256 // size of all arrays

    // type paramList = s : seq<uint32> | |s| == nParams witness *


    datatype {:lucid_event} Event = 
        | ParametersChunk(worker : uint32,  offset : uint32, slot : uint32, params : seq32<uint32>) 
            // a worker sends a chunk of parameters for a slot at a particular offset
        | SendAggChunk(offset : uint32, slot : uint32, params : seq32<uint32>) 
            // broadcast out to all workers when aggregation is complete

    class {:lucid_program} Program {
        const base : Switch<Event>
        const counts : VarArray<uint32>  // |slot|
        const pool : seq32<VarArray<uint32>> // param x slot
        ghost var allObjects : set<object>
        ghost predicate validObjects()
            reads this, allObjects
        {
            // Repr contents
            allObjects == toSet(pool) + {counts}
            // Non-aliasing
            && UniqueSeqLen(pool, nParams) // USING DAFNY NOTE: we need this for updater loops
            && |allObjects| == |pool| + 1 // Need this for aliasing across variables
            // Array sizes
            &&  |counts.cells| == nSlots
            &&  |pool| == nParams && (forall j | 0 <= j < nParams :: |pool[j].cells| == nSlots)
            // USING DAFNY NOTE: the forall below doesn't verify here! 
            // &&  (forall arr :: arr in pool ==> |arr.cells| == nSlots)    
        }

        constructor ()
            ensures base.New()
            ensures validObjects()
            ensures fresh(base)
            ensures fresh(this) && fresh(allObjects)
        {
            var poolTmp : seq<VarArray<uint32>> := [];
            for i := 0 to nParams 
                invariant UniqueSeqLen (poolTmp, i) 
                invariant |poolTmp| == i
                invariant fresh(poolTmp)
                invariant (forall j | 0 <= j < i :: |poolTmp[j].cells| == nSlots)
            {
                var tmp := new VarArray.Create(nSlots, 0 as uint32);
                AppendIsDistributive(poolTmp, tmp);
                poolTmp := poolTmp + [tmp];
            }
            pool := poolTmp;
            counts := new VarArray.Create(nSlots, 0 as uint32);
            allObjects := (set p | p in poolTmp) + {counts};
            base := new Switch(true);
        }

        function incr (mv: uint32, incrBy: uint32) : uint32 { 
            (mv + incrBy) % max32
        }
        function memval (mv: uint32, unused: uint32) : uint32 { mv }


        twostate predicate SlotIncremented(slot : uint32, params : seq32<uint32>)
            // The appropriate memory areas have been incremented for the slot
            reads allObjects, this
            requires validObjects () && old(validObjects())
            requires slot < nSlots
        {   
                && forall i :: 0 <= i < nParams ==> 
                    pool[i].cells[slot] == (old(pool[i].cells[slot]) + params[i]) % max32
        }

        // Handle one chunk of the parameter update from one worker for one slot (which is at a particular offset).
        // Generate an aggregate chunk at that offset after receiving updates from all workers.
        // Note: assumption is that workers manage offset to slot mapping
        method parametersChunk(worker : uint32,  offset : uint32, slot : uint32, params : seq32<uint32>)
            modifies allObjects, base`outputQueue
            requires validObjects() && base.baseInvariant()
            requires slot < nSlots
            ensures  validObjects() && base.baseInvariant()
            // The slot gets incremented correctly
            ensures  SlotIncremented(slot, params)
            // We generate an event to send an aggregate chunk to all the workers
            ensures  (counts.cells[slot] == nWorkers) ==> 
                base.generatedPredicate((e : Event)=> e.SendAggChunk?)
        {
            var aggParams_tmp : seq<uint32> := [];
            for i := 0 to nParams
                invariant |aggParams_tmp| == i
                invariant validObjects () && base.baseInvariant()
                invariant forall j :: 0 <= j < i ==> // updated param cells
                    pool[j].cells[slot] == (old(pool[j].cells[slot]) + params[j]) % max32
                invariant forall j :: i <= j < nParams ==> // param cells yet to be updated
                    pool[j].cells[slot] == old(pool[j].cells[slot])
                // output parameter vector
                invariant forall j :: 0 <= j < |aggParams_tmp| ==> aggParams_tmp[j] ==  pool[j].cells[slot]
                invariant forall j :: i <= j < |aggParams_tmp| ==> aggParams_tmp[j] == 0
                invariant base.outputQueue == old(base.outputQueue) // no event generations inside loop
            {
                var v := pool[i].GetSet(slot, incr, params[i], incr, params[i]);
                aggParams_tmp := aggParams_tmp + [v];
            }
            var aggParams : seq32<uint32> := aggParams_tmp;
            
            var ct : uint32 := counts.GetSet(slot, incr, 1, incr, 1);
            if (ct == nWorkers) {
                base.generateOutput({1}, SendAggChunk(offset, slot, aggParams));
            } 
        }
    }
