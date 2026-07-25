/*-------------------------------------------------------------------------
A SLIDING-WINDOW BLOOM FILTER
   For quick readability, the built-in arraySizes has been renamed to
validArrays.  The built-in stateInvariant has been renamed to 
noFalseNegativesInPanes.
-------------------------------------------------------------------------*/
include "../src/lib/lucidLibrary.dfy"
include "bfMinimal.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)

const T : nat := max32
const numPanes : nat := 4
const I : nat := 1048576    // interval length, ~ 1 ms assuming ns clock

type pane = x : nat | 0 <= x < numPanes
type uint1 = x : nat | 0 <= x < 2

class {:lucid_module} SlidingBloomFilter {                     

   // Program State
   const clearIdx : VarArray<index>
   const panes : seq<BloomFilter>

   ghost const allObjs : set<object> :=  
    (set p | p in panes :: p) + 
    (set p | p in panes, obj | obj in p.allObjects :: obj) + 
    {clearIdx as object}

   ghost predicate validArrays ()
      reads allObjs
   {
      |panes| == 4
      && (forall i, j :: 0 <= i < |panes| && 0 <= j < |panes| && i != j ==> panes[i].allObjects != panes[j].allObjects)
      && (forall p | p in panes :: p.validObjects())
      && |clearIdx.cells| == 1
   }

   predicate inFilterWindow (key: uint32, ts : uint32)
      reads allObjs
      requires validArrays ()
   {
         panes[frontPane(ts)].inFilter(key) 
      || panes[(frontPane(ts)-1) % 4].inFilter(key)
      || panes[(frontPane(ts)-2) % 4].inFilter(key)
   }

   constructor () 
      ensures validArrays ()                         
      ensures noFalseNegativesInPanes ()
      ensures fresh(allObjs)
   {   
      clearIdx := new VarArray.Create(1, 0 as index);
      var p0 := new BloomFilter ();
      var p1 := new BloomFilter ();
      var p2 := new BloomFilter (); 
      var p3 := new BloomFilter ();
      panes := [p0, p1, p2, p3];
   }
   function incr (oldVal: index, incrBy: index) : index {  (oldVal + incrBy) % numRows}

   ghost predicate noFalseNegativesInPanes () reads this, allObjs  
    requires validArrays ()
   {  forall i :: 0 <= i < |panes| ==> panes[i].noFalseNegatives() }

   function frontPane (timestamp: uint32) : pane
   {  ( timestamp / I ) % numPanes  }    
   twostate predicate insertEffect (k: uint32, ts : uint32) 
      reads allObjs
      requires validArrays()
   {
      inserted(panes[frontPane(ts)], k)
      && unchanged(panes[(frontPane(ts)-1)%4])
      && unchanged(panes[(frontPane(ts)-2)%4])
   }

   twostate predicate inserted (p : BloomFilter, k : uint32) 
    reads p
   {  p.exactSet == old (p.exactSet) + {k}  }

   method insert (key : uint32, ts : uint32)
      modifies allObjs
      requires validArrays ()
      ensures validArrays ()
      requires forall p | p in panes :: p.noFalseNegatives()
      ensures  forall p | p in panes :: p.noFalseNegatives()
      ensures panes[frontPane(ts)].exactSet == old(panes[frontPane(ts)].exactSet) + {key}
      ensures unchanged(panes[(frontPane(ts)-1)%4], panes[(frontPane(ts)-2)%4])//warm panes
   {
      var idx := clearIdx.GetSet(0, incr, 1, incr, 1);
      match frontPane (ts) {
         case 0 => {  panes[0].insert (key);  
                      panes[1].clearCell (idx); }
         case 1 => {  panes[1].insert (key);  
                      panes[2].clearCell (idx); }
         case 2 => {  panes[2].insert (key);  
                      panes[3].clearCell (idx); }
         case 3 => {  panes[0].clearCell (idx); 
                      panes[3].insert (key);    }
      }
   }

   twostate predicate queryEffect(ts : uint32)
      reads allObjs
      requires validArrays()
   {
         unchanged(panes[frontPane(ts)]) 
      && unchanged(panes[(frontPane(ts)-1)%4])
      && unchanged(panes[(frontPane(ts)-2)%4])
   }


   method query (key: uint32, ts : uint32) returns (inSet : bool)
      modifies allObjs
      requires validArrays ()
      requires noFalseNegativesInPanes ()
      ensures validArrays ()
      ensures noFalseNegativesInPanes ()
      ensures queryEffect (ts) 
      ensures inSet == inFilterWindow (key, ts)
   {
      var idx := clearIdx.GetSet(0, incr, 1, incr, 1);
      match frontPane (ts) {
          case 0 => { 
            var in0 := panes[0].query(key);
            panes[1].clearCell (idx);
            var in2 := panes[2].query(key);
            var in3 := panes[3].query(key);
            inSet := in0 || in2 || in3;
        }
        case 1 => { 
            var in0 := panes[0].query(key);
            var in1 := panes[1].query(key);
            panes[2].clearCell (idx); 
            var in3 := panes[3].query(key);
            inSet := in0 || in1 || in3;
        }
        case 2 => { 
            var in0 := panes[0].query(key);
            var in1 := panes[1].query(key);
            var in2 := panes[2].query(key);
            panes[3].clearCell (idx); 
            inSet := in0 || in1 || in2;
        }
        case 3 => { 
            panes[0].clearCell (idx); 
            var in1 := panes[1].query(key);
            var in2 := panes[2].query(key);
            var in3 := panes[3].query(key);
            inSet := in1 || in2 || in3;
        }  
      }
   }

}



method Main ()
{
   var sbf := new SlidingBloomFilter ();

   var insertTime : nat := *;

   var key : uint32 := *;
   sbf.insert (key, insertTime%T);

   var found : bool := true;
   var time : nat := insertTime;
   while (time <= insertTime + 2*I) 
      invariant sbf.validArrays ()
      invariant sbf.noFalseNegativesInPanes ()
      invariant key in sbf.panes[sbf.frontPane(insertTime%T)].exactSet
      invariant found == true
   {
      var doInsert : bool := *;
      var k : uint32 := *; 
      if (doInsert) { sbf.insert(k, time%T); } 
      else { var _ := sbf.query(k,  time%T); }
      found := sbf.query (key, time%T);
      var jump : nat :| jump > 0;
      time := time + jump;
      if (found != true) { print "BUG: key not found!"; }
   }
}
