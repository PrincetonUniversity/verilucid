include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)

    const nFlows : nat := 1024
    type  flowIdx_t = f : nat | f < 1024
    type  flowKey_t = (uint32, uint32)
    const maxPktLen : uint32 := 2048
    class ExactStore {
        ghost var flows : map<flowKey_t, nat>
        ghost constructor () 
            ensures fresh(this)
            ensures flows == map[]
        {
            flows := map[];
        }
        ghost method Update(key : flowKey_t, len : uint32)
            modifies this`flows
            ensures flows.Keys == old(flows).Keys + {key} // all old flows are still here, and the new flow too
            // all counters besides for key stay the same
            ensures forall k | k in old(flows) :: k in flows && (k != key ==> old(flows)[k] == flows[k])
            // flows[key] is incremented appropriately
            ensures if key in old(flows)
                        then key in flows && flows[key] == old(flows)[key] + len
                        else flows[key] == len
            
        {
            flows := 
                if (key in flows) then
                    flows[key := flows[key] + len]
                else
                    flows[key := len];
        }
    }
    function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
        (oldVal + incrBy) % max32
    }


    datatype {:lucid_event} Event = 
        | Packet(src : uint32, dst : uint32, len : uint32)
        | FlowRecord(src : uint32, dst : uint32, len : uint32)
    class {:lucid_program} Program {
        const base : Switch<Event>
        const seed : nat := 7
        const collectorPort : nat := 0
        const srcs : VarArray<uint32>
        const dsts : VarArray<uint32>
        const lens : VarArray<uint32>
        ghost var ArrayRepr : set<object> // This is the "allObjects" object in new code
        ghost predicate ValidArrays() // This is "validObjects" in new code
            reads this, ArrayRepr
        {
            // Repr contents
                (ArrayRepr == {srcs, dsts, lens})
            // Non-aliasing
            && srcs != dsts && srcs != lens && dsts != lens
            // array lengths
            && |srcs.cells| == |dsts.cells| == |lens.cells| == nFlows
            // ghost aliasing ARGH
            && this.fullStore != this.collectorStore
        }
        ghost const fullStore : ExactStore // models collector that just processes everything
        ghost const collectorStore : ExactStore // models collector that processes evicted records
        constructor ()
            ensures ValidArrays() && base.New()
            ensures fullStore.flows == map[]
            ensures collectorStore.flows == map[]
        {
            srcs := new VarArray<uint32>.Create(nFlows, 0 as nat);
            dsts := new VarArray<uint32>.Create(nFlows, 0 as nat);
            lens := new VarArray<uint32>.Create(nFlows, 0 as nat);
            ArrayRepr := {srcs, dsts, lens};
            fullStore := new ExactStore();
            collectorStore := new ExactStore();
            base := new Switch(true);
        }
        // Number of packets counted by the cache.
        ghost function cacheLen(key : flowKey_t) : nat
            reads this, ArrayRepr
            requires ValidArrays()
        {
            var idx : uint32 := hashn(10, seed, [key.0, key.1]);
            if ((srcs.cells[idx] == key.0) && (dsts.cells[idx] == key.1))
            then lens.cells[idx]
            else 0
        }
        // Number of packets counted by a model of the collector.
        ghost function collectorLen(key : flowKey_t) : nat            
            reads this.collectorStore
        {
            if key in this.collectorStore.flows
                then this.collectorStore.flows[key]
                else 0 // not found
        }
        // Number of packets counted by the monolithic model.
        ghost function fullLen(key : flowKey_t) : nat
            reads this.fullStore
        {            
            if key in fullStore.flows
                then fullStore.flows[key]
                else 0               
        }
        ghost predicate stateInvariant(key : flowKey_t)
            // The cache is correct for flow k if the cache counter + collector counter == full counter
            reads this, ArrayRepr
            reads this.fullStore, this.collectorStore
            requires ValidArrays()            
        {
            fullLen(key) == cacheLen(key) + collectorLen(key)
        }

        function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
        function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }
        function safeIncr (oldVal: uint32, incrBy: uint32) : uint32 {         
            // if the new counter value is above some unsafe threshold, 
            // such that the next packet may cause it to overflow, 
            // we want to evict, which means resetting it.
            if oldVal + incrBy > 4294967295 - maxPktLen
            then incrBy
            else oldVal + incrBy
        }

        function ZaveSafeIncr (oldVal: uint32, incrBy: uint32) : uint32 {
            // This is a custom memcalc.  If the new size is above some unsafe
            // threshold, such that the next packet may cause it to overflow,
            // then the old size will be sent to the collector, and the new
            // size will be installed.
            if ((oldVal + incrBy) % max32) < oldVal then
                incrBy
            else (oldVal + incrBy) % max32
            }
        method packet(src : uint32, dst : uint32, len : uint32)
            modifies srcs`cells, dsts`cells, lens`cells, base`outputQueue
            modifies this.fullStore, this.collectorStore // ghost
            requires this.fullStore != this.collectorStore
            requires ValidArrays() && base.baseInvariant ()
            requires len < maxPktLen && cacheLen((src, dst)) < max32 - maxPktLen // Length correctness
            requires stateInvariant((src, dst))
            ensures  ValidArrays() && base.baseInvariant ()
            ensures  cacheLen((src, dst)) < max32 - maxPktLen
            ensures  stateInvariant((src, dst))
            // Without the additional case that checks for a near-overflow and then evicts, 
            // only the weaker state invariant below holds
            // ensures  (old(cacheLen((src, dst))) + len as nat < max32) ==> stateInvariant((src, dst))
        {
            fullStore.Update((src, dst), len);
            var idx : uint32 := hashn(10, seed, [src, dst]);
            assert (idx < nFlows);
            var oldSrc := srcs.GetSet(idx, memval, 0, newval, src);
            var oldDst := dsts.GetSet(idx, memval, 0, newval, dst);         
            // check for collision and reset the counter if there is one.
            if (oldSrc != src || oldDst != dst) {
                var oldLen := lens.GetSet(idx, memval, 0, newval, len);
                base.generateOutput({collectorPort}, FlowRecord(oldSrc, oldDst, oldLen));
                collectorStore.Update((oldSrc, oldDst), oldLen);
            }
            else {
                // lens.Set(idx, incr, len);
                var oldLen : uint32 := lens.GetSet(idx, memval, 0, safeIncr, len);
                // if the old length was too large, reset the counter.
                if ((oldLen + len) > (4294967295 - maxPktLen) ) {
                    base.generateOutput({collectorPort}, FlowRecord(oldSrc, oldDst, oldLen));
                    collectorStore.Update((oldSrc, oldDst), oldLen);
                }
            }
        }



    }
