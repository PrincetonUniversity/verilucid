// Use multiple columns
include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)


ghost predicate allUnique<t>(globals : seq<t>) {
    forall i, j :: 0 <= i < |globals| && 0 <= j < |globals| && i != j ==> globals[i] != globals[j]
}

// TODO: design choice -- how should compiler handle const and range types?
const numRows : nat := 1024 
const numarrs : nat := 4
type index = x : nat | 0 <= x < numRows 

class {:lucid_module} BloomFilter {

    const arrs : seq4<VarArray <uint1>>
    ghost var exactSet : set <uint32>

    function compute_hash (key : uint32) : index
    {  key % numRows  }

    ghost const allObjects : set <object> 
    ghost predicate validObjects ()   
        reads allObjects
    {  
        allObjects == toSet(arrs)
        && UniqueSeqLen(arrs, 4)
        && (forall i :: 0 <= i < |arrs| ==> | arrs[i].cells| == numRows)
        && (forall i :: 0 <= i < |arrs| ==> arrs[i] in allObjects)
    }  

    ghost predicate inFilter (key : uint32)
        reads allObjects
        requires validObjects ()
    {  
        // key must be in all arrs
        forall i :: 0 <= i < |arrs| ==> arrs[i].cells [compute_hash (key)] == 1
    }
    ghost predicate inFilterUpTo (key : uint32, n : uint32)
        reads allObjects
        requires validObjects ()
    {  
        // key must be in all arrs
        n <= |arrs| && forall i :: 0 <= i < n ==> arrs[i].cells [compute_hash (key)] == 1
    }

    ghost predicate noFalseNegatives ()
        reads this, allObjects
        requires validObjects ()
    // {  forall k: uint32 :: ! inFilter (k) ==> k !in exactSet  }
    {  forall k: uint32 :: k in exactSet ==> inFilter (k) }

    constructor ()                
        ensures exactSet == {}
        ensures validObjects () 
        ensures noFalseNegatives () 
        ensures fresh(allObjects)
        ensures fresh(this)
        ensures fresh(arrs)
    {  
        var arrsTemp : seq<VarArray<uint1>> := [];
        for i := 0 to numarrs
            invariant |arrsTemp| == i
            invariant fresh(arrsTemp)
            invariant (forall j | 0 <= j < i :: |arrsTemp[j].cells| == numRows)
            invariant UniqueSeqLen(arrsTemp, i)
        {
            var tmp := new VarArray.Create(numRows, 0 as uint1);
            AppendIsDistributive(arrsTemp, tmp);
            arrsTemp := arrsTemp + [tmp];
        }
        arrs := arrsTemp;
        exactSet := {};
        allObjects := toSet(arrsTemp);
    }
   function nocalc (oldVal: uint1, newArg: uint1) : uint1 {  oldVal  }
   function swapcalc(oldVal: uint1, newArg: uint1) : uint1 {  newArg  }            

    method insert (key : uint32)
        modifies this, this.allObjects
        requires validObjects ()  
        requires noFalseNegatives ()  
        ensures exactSet == old (exactSet) + { key }
        ensures validObjects () 
        ensures noFalseNegatives ()  
        ensures inFilter (key)
    {
        for i := 0 to numarrs
            invariant validObjects ()
            invariant inFilterUpTo(key, i)
            invariant exactSet == old(exactSet)
            invariant noFalseNegatives()
        {
            arrs[i].Set (compute_hash (key), swapcalc, 1 as uint1);
        }
        exactSet := exactSet + { key };
    }

    method query(key : uint32) returns (found : bool)
        requires validObjects ()  
        requires noFalseNegatives ()  
        ensures  noFalseNegatives()
        ensures found == inFilter(key)
    {
        for i := 0 to numarrs
            invariant inFilterUpTo(key, i)
        {             
            var v := arrs[i].Get(compute_hash(key), nocalc, 0);
            if (v != 1) {
                return false;
            }
        }
        return true;
    }

    method clearCell (idx : index) 
        modifies this, this.allObjects
        requires validObjects ()
        requires noFalseNegatives ()
        ensures validObjects () 
        ensures  noFalseNegatives()
    {  
        exactSet := exactSet - (set k : uint32 | compute_hash(k) == idx);
        for i := 0 to numarrs
            invariant validObjects ()
            invariant forall k: uint32 :: k in exactSet  ==> compute_hash(k) != idx
            invariant noFalseNegatives()
        {
            arrs[i].Set (idx, swapcalc, 0);  
        }
    }   

}  

