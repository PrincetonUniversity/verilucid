// A simple count min library. 
// methods: 
// count(key) -- count the key, return updated result
// events / handlers:
// query(sport, key) -- get value of key, send response(key, value) back to sport
// clear(min, max) -- clear indices from min to max

include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)


    datatype {:lucid_event} Event = 
        | query(sport : uint8, key : uint32)
        | response(key : uint32, count : uint32)
        | clear(i : uint32, j : uint32)
    
    class {:lucid_program} Program {
        const base : Switch<Event>
        const nRows : uint32 := 32
        const seed0 : uint32 := 7
        const seed1 : uint32 := 13

        const col0 : VarArray<uint32>
        const col1 : VarArray<uint32>

        ghost const allObjects : set <object> := {col0, col1}
        ghost predicate validObjects ()   
            reads allObjects
        {  true  }      


        constructor ()
            ensures fresh(col0)
            ensures fresh(col1)
            ensures col0.cells == zeros(nRows) && col1.cells == zeros(nRows)
            ensures fresh(this)
        {
            base := new Switch<Event>(true);
            col0 := new VarArray<uint32>.Create(nRows, 0 as uint32);
            col1 := new VarArray<uint32>.Create(nRows, 0 as uint32);
        }

        function calc_hash(seed : uint32, key : uint32) : uint32
            ensures 0 <= calc_hash(seed, key) < nRows
        {
            ((seed + key) % nRows) % max32
        }

        // memops
        function incr (oldVal: uint32, incrBy: uint32) : uint32 { 
            (oldVal + incrBy) % max32
        }
        function memval (oldVal: uint32, unused: uint32) : uint32 { oldVal }
        function newval (oldVal: uint32, newVal: uint32) : uint32 { newVal }


        // Increment a key and return current min count
        method count(key : uint32) returns (result : uint32)          
            modifies col0`cells, col1`cells
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            // the result is the minimum of the two counts
            ensures result == 
                var h0 := calc_hash(seed0, key);
                var h1 := calc_hash(seed1, key);
                var count0 := ((  (old(col0.cells)[h0] + 1) % max32));
                var count1 := ((  (old(col1.cells)[h1] + 1) % max32));
                if count0 <= count1 then count0 else count1
            // the arrays are updated correctly
            ensures             
                var h0 := calc_hash(seed0, key);
                var h1 := calc_hash(seed1, key);
                var count0 := (old(col0.cells)[h0] + 1 as uint32) % max32;
                var count1 := (old(col1.cells)[h1] + 1 as uint32) % max32;
                col0.updatedCell(h0, count0)
                && col1.updatedCell(h1, count1)
        {
            var h0 := calc_hash(seed0, key);
            var h1 := calc_hash(seed1, key);
            var count1 := col0.GetSet(h0, incr, 1, incr, 1);
            var count2 := col1.GetSet(h1, incr, 1, incr, 1);
            if (count1 <= count2) {
                result := count1;
            } else {
                result := count2;
            }
        }

        // Query event handler. Generates a response event with the minimum count of the two arrays.
        method Query(sport : uint8, key : uint32)
            modifies base`outputQueue
            requires base.baseInvariant()
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            ensures base.baseInvariant()
            ensures 
                var h0 := calc_hash(seed0, key);
                var h1 := calc_hash(seed1, key);
                var count0 := old(col0.cells)[h0];
                var count1 := old(col1.cells)[h1];
                var count := if count0 <= count1 then count0 else count1;
                base.generatedToPorts({sport}, response(key, count))
        {
            var h0 := calc_hash(seed0, key);
            var h1 := calc_hash(seed1, key);
            var count0 := col0.Get(h0, memval, 0);
            var count1 := col1.Get(h1, memval, 0);
            var count := if count0 <= count1 then count0 else count1;
            base.generateOutput({sport}, response(key, count));
        }

        // Clear event handler. Clears i, then as long as i < j, clears i+1 by generating a recursive event.
        method Clear(i : uint32, j : uint32)
            modifies col0`cells, col1`cells
            modifies base`recircQueue
            requires base.baseInvariant()
            requires |col0.cells| == nRows && |col1.cells| == nRows
            requires col0 != col1
            requires i < nRows && j < nRows
            ensures base.baseInvariant()
            ensures 
                col0.updatedCell(i, 0)
                && col1.updatedCell(i, 0)
            ensures i < j ==> base.recircGenerated(clear(i + 1, j))
        {
            col0.Set(i, newval, 0);
            col1.Set(i, newval, 0);
            if i < j {
                base.generateRecircEvent(clear(i + 1, j));
            }
        }            
    }