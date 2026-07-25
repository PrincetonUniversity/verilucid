// TODO: use correct object syntax
include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)

const numRows : nat := 1024
type index = x : nat | 0 <= x < numRows 

    class {:lucid_module} BloomFilter {

    const filter : VarArray <uint1>
    ghost var exactSet : set <uint32>

    function calc_hash(key : uint32) : index
    {  key % numRows  }

    ghost const allObjects : set <object> := {filter}
    ghost predicate validObjects ()   
        reads allObjects
    {  | filter.cells | == numRows  }      

    ghost predicate inFilter (key : uint32)
        reads allObjects
        requires validObjects ()
    {  filter.cells [calc_hash (key)] == 1  }

    ghost predicate noFalseNegatives () 
        reads this, allObjects
        requires validObjects ()
    {  forall k: uint32 :: ! inFilter (k) ==> k !in exactSet  }

    constructor ()                
        ensures exactSet == {}
        ensures validObjects () 
        ensures noFalseNegatives () 
        ensures fresh(filter)
        ensures fresh(this)
    {  filter := new VarArray.Create(numRows, 0 as uint1);
        exactSet := {};
    }

   function nocalc (oldVal: uint1, newArg: uint1) : uint1 {  oldVal  }
   function swapcalc (oldVal: uint1, newArg: uint1) : uint1 {  newArg  }            


    method insert (key : uint32)
        modifies this, this.allObjects
        requires validObjects ()  
        requires noFalseNegatives ()  
        ensures exactSet == old (exactSet) + { key }
        ensures validObjects () 
        ensures noFalseNegatives ()  
        ensures inFilter (key)
    {
        filter.Set (calc_hash (key), swapcalc, 1 as uint1);
        exactSet := exactSet + { key };
    }

    method query(key : uint32) returns (found : bool)
        requires validObjects ()  
        requires noFalseNegatives ()  
        ensures found == inFilter(key)
    {
        var v := filter.Get(calc_hash(key), nocalc, 0);
        return v == 1;
    }


    method clearCell (idx : index) 
        modifies this, this.allObjects
        requires validObjects ()
        requires noFalseNegatives ()
        ensures validObjects () 
        ensures noFalseNegatives ()  
    {  
        filter.Set (idx, swapcalc, 0);  
        exactSet := exactSet - (set k : uint32 | calc_hash(k) == idx);
    }   
    }  
