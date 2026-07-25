/*-------------------------------------------------------------------------
LUCID LIBRARY
   The Lucid library has 4 modules: LucidTypes, LucidObjects, LucidSwitch, and LucidHelpers.

   LucidTypes defines bounded-integer types (uint8, uint16, uint32, uint64).
   LucidObjects defines arrays, statevars, and memops.
   LucidSwitch defines a switch model that can be used to simulate a P4 processor.
   LucidHelpers defines a few other stateless helpers (hash, rand, etc).
-------------------------------------------------------------------------*/




module LucidHelpers {
   import opened LucidTypes

   // Helpers for sequences of arrays
   // Some helpers we will need -- these should probably go into the LucidObjects module
   // All items in the sequence are unique and its length is n
   ghost predicate UniqueSeqLen<T>(vs : seq<T>, n : nat)
   {
      |vs| == n == |set v | v in vs|
      && noDuplicates(vs)
   }

   // Seq to Set conversion is distributive over 
   // adding a unique item to the Seq
   lemma AppendIsDistributive<T>(s: seq<T>, x: T)
      requires x !in s
      ensures  (set v | v in s) + {x} == (set v | v in s + [x])
   { }


   function toSet<T> (xs: seq<T>): set<T>
   {  set x: T | x in xs  }

   ghost predicate noDuplicates<T>(xs: seq<T>)
   {
      forall i, j :: 0 <= i < |xs| && 0 <= j < |xs| && i != j ==> xs[i] != xs[j]
   }

    // Inner method for hash builtin
    function {:fuel 16} hash_nat(seed : nat, key : seq<nat>) : nat
    {
        if |key| == 0
            then seed
            else key[0] + hash_nat(seed, key[1..])
    }

   function pow2(n: nat): nat
      ensures pow2(n) > 0
   {
      if n == 0 then 1 else 2 * pow2(n - 1)
   }

   function hashn(n : nat, seed : nat, key : seq<nat>) : nat
      requires 0 < n <= 32        
      ensures hashn(n, seed, key) < pow2(n)
   {
      hash_nat(seed, key) % pow2(n)
   }

    method rand(s : nat, e : nat) returns (rv : nat)
        requires s < e
        ensures s <= rv < e
    {
        return s;
    }

   function {:opaque} rand32() : uint32
      ensures 0 <= rand32() < max32 
   { 0 }


    // helper to represent flood port group
    function flood(p : nat) : nat {
        p + 1001
    }
}



module TimesAndEvents {       
   import opened LucidTypes

   type bits = x : nat | 0 <= x < 4294967296
   const T : nat := 4294967296    

   datatype TimedEvent<Event> =
      TimedEvent (event: Event, time: nat, timestamp: bits)

   datatype EventOption<Event> = 
    | None()
    | Some(event : Event)

   datatype Output<Event> = Output (ports: set <nat>, event: Event, time: nat)   
}


module LucidSwitch {
   import opened LucidTypes
   import opened TimesAndEvents

class Switch<Event(==)> {
   const inputFirst : bool          // true if input events have priority
                                      // over recirculation events
   const recircDelay : nat := 600      // the approximate delay between the time
                                // of a dispatched event and the generation
                                // of a recirculation event caused by it;
                                // should be nonzero
   var inputQueue : seq <TimedEvent<Event>>
   var recircQueue : seq <TimedEvent<Event>>
   var outputQueue : seq <Output<Event>>
   var now : nat                   // the present, in simulated "real" time
   var lastDispatch : nat              // time of the last event dispatched
   
   ghost predicate validQueue (q: seq <TimedEvent<Event>>)   // queue invariant
   // In a valid queue of timed events, times and timestamps match, and
   // time is nondecreasing.
   {   
      match |q| {
         case 0 => true
         case _ =>  
            (  forall j | 0 <= j <= |q|-1 :: 
                  q[j].timestamp == q[j].time % T  )
         && (  forall j | 0 <= j <  |q|-1 :: 
                  q[j].time <= q[j+1].time         )
   }  }

   lemma {:axiom} timeOrdered (q: seq <TimedEvent<Event>>)
      ensures (|q| > 0 && validQueue (q)) ==> q[0].time <= q[|q|-1].time

   ghost predicate baseInvariant () 
      reads this
   {     validQueue (inputQueue)
      && validQueue (recircQueue)
      && (|inputQueue| > 0 ==> lastDispatch <= inputQueue[0].time)
      && (|inputQueue| > 0 ==> inputQueue[|inputQueue|-1].time <= now)
      && (|recircQueue| > 0 ==> 
         recircQueue[|recircQueue|-1].time <= lastDispatch +recircDelay)
      && lastDispatch <= now
      && timestamp() == now % T
   }

   ghost predicate New()
      reads this
   { 
         baseInvariant ()
      && inputQueue == [] && outputQueue == [] && recircQueue == [] 
      && lastDispatch == 0
      && now == 0
   }

   constructor (inputFst : bool) 
      ensures New ()
      ensures inputFirst == inputFst
   {
      inputQueue := []; recircQueue := []; outputQueue := []; 
      now, lastDispatch := 0, 0;    
      inputFirst := inputFst;
   }

   method simulateOnlyArrival(e : Event)
      modifies this`inputQueue
      requires baseInvariant ()
      requires validQueue ([TimedEvent(e, now, now%T)])
      ensures old (inputQueue) <= inputQueue //old queue is a prefix of new
      ensures baseInvariant ()
      ensures inputQueue == old (inputQueue) + [TimedEvent(e, now, now%T)]
   {
      inputQueue := inputQueue + [TimedEvent(e, now, now%T)];
   }

   method simulateArrival(e : Event, time : nat)
   // arrival of a single packet. Convenience wrapper for simulateArrivals.
      modifies this`inputQueue, this`now
      requires now <= time
      requires validQueue ([TimedEvent(e, time, time%T)])
      requires baseInvariant ()
      ensures old (inputQueue) <= inputQueue //old queue is a prefix of new
      ensures baseInvariant ()
      ensures inputQueue == old(inputQueue) + [TimedEvent(e, time, time%T)]
      ensures now == time
   {
      simulateArrivals([TimedEvent(e, time, time%T)]);
   }

   method simulateArrivals (inputs: seq <TimedEvent<Event>>)
   // This method adds zero or more events to the input queue.
   // It also advances the clock to the time when the last
   // event arrives.
      modifies this`inputQueue, this`now
      requires |inputs| > 0 ==> now <= inputs[0].time
      requires validQueue (inputs)
      requires baseInvariant ()
      ensures old (inputQueue) <= inputQueue //old queue is a prefix of new
      ensures baseInvariant ()
      ensures lastDispatch == old (lastDispatch)
      // functional spec
      ensures inputQueue == old(inputQueue) + inputs
      ensures |inputs| > 0 ==> now == inputs[|inputs|-1].time
   {   
      inputQueue := inputQueue + inputs;
      if |inputs| > 0 {  
         timeOrdered (inputs);  
         now := inputs[|inputs|-1].time;  } 
   }

   function timestamp() : bits
   // current time as fixed-width uint
      reads this`now
   {
      this.now % T
   }

   predicate recircAvailable ()
      reads this
   {  |recircQueue| > 0 && recircQueue[0].time <= now  }

   predicate emptyQueues ()
      reads this
   { |inputQueue| == 0 && |recircQueue| == 0 && |outputQueue| == 0}
   method clearOutput ()
      modifies this`outputQueue
      ensures outputQueue == []
   { outputQueue := []; }

   ghost function nextEvent() : EventOption<Event>
      // Looks into the future and tells you what pickNextEvent
      // will return. Useful in abstract test cases.
      reads this`inputQueue, this`recircQueue, baseInvariant.reads
      requires baseInvariant ()
   {
      if |(inputQueue)| == 0 && |(recircQueue)| == 0 then 
            None()
      else 
         if |(inputQueue)| > 0 && (inputFirst || ! (recircAvailable ())) 
         then 
               Some((inputQueue[0]).event)
         else 
            if ! (recircAvailable ())
            then 
                  Some((recircQueue[0]).event)
         else 
               Some((recircQueue[0]).event)
   }
   ghost function nextTime() : nat
      // Tells you what time pickNextEvent will choose for 
      // the next event dispatch. Useful in abstract test cases.
      reads this`inputQueue, this`recircQueue, baseInvariant.reads, this`now
      requires baseInvariant ()
   {
      if |(inputQueue)| == 0 && |(recircQueue)| == 0 then 
           now
      else 
         if |(inputQueue)| > 0 && (inputFirst || ! (recircAvailable ())) 
         then 
               now
         else 
            if ! (recircAvailable ())
            then 
                  recircQueue[0].time
         else 
               now
   }
   function nextRecircTime() : nat
      // The time attached to the next pending recirc event.
      reads this`recircQueue
      requires |this.recircQueue| > 0
   {
      this.recircQueue[0].time
   }

   function nextRecircEvent() : Event
      // The next pending recirc event.
      reads this`recircQueue
      requires |this.recircQueue| > 0
   {
      this.recircQueue[0].event
   }

   predicate isNextRecircEvent(e : Event, t : nat) 
      // Is the next recirc event e at time t?
      reads this`recircQueue
   {
      |recircQueue| > 0 ==> recircQueue[0].event == e && recircQueue[0].time == t
   }


   predicate nextRecircIsE(e : Event) 
      // Is the next recirc event e?
      reads this`recircQueue
   {
      |recircQueue| > 0 && recircQueue[0].event == e
   }

   // temporal predicates
   predicate until(time : nat)
   reads this`now
   {
      this.now < time
   }

   predicate after(time : nat)
   reads this`now
   {
      this.now >= time
   }

   method pickNextEvent () returns (event: EventOption<Event>)
      modifies this`now, this`inputQueue, this`recircQueue, this`lastDispatch
      requires baseInvariant ()
      ensures baseInvariant ()
      ensures lastDispatch >= old (lastDispatch)
      // functional specification
      ensures 
         if |old(inputQueue)| == 0 && |old(recircQueue)| == 0 then 
               event == None()
            && now == old(now)
            && inputQueue == old(inputQueue)
            && recircQueue == old(recircQueue)
            && lastDispatch == old(lastDispatch)
         else 
            if |old(inputQueue)| > 0 && (inputFirst || ! old(recircAvailable ())) 
            then 
                  event == Some(old(inputQueue[0]).event)
               && now == old(now)
               && (inputQueue == old(inputQueue)[1..|old(inputQueue)|])
               && recircQueue == old(recircQueue)
               && lastDispatch == old(inputQueue)[0].time
            else
               if ! old(recircAvailable ())
               then (
                     event == Some(old(recircQueue[0]).event)
                  && now == old(recircQueue[0]).time
                  && inputQueue == old(inputQueue)
                  && (recircQueue == old(recircQueue)[1..|old(recircQueue)|])               
                  && lastDispatch == now
                  && |recircQueue| == |old(recircQueue)| - 1)
               else (
                     event == Some(old(recircQueue[0]).event)
                  && now == old(now)
                  && inputQueue == old(inputQueue)
                  && (recircQueue == old(recircQueue)[1..|old(recircQueue)|])               
                  && lastDispatch == old(lastDispatch))

   {  
      if (|inputQueue| == 0 && |recircQueue| == 0) {
         event := None();
      }  else {
         if |inputQueue| > 0 && (inputFirst || ! recircAvailable ()) { 
            assert inputQueue[|inputQueue|-1].time <= now;  
            assert validQueue (inputQueue);      
            timeOrdered (inputQueue);
            assert inputQueue[0].time <= now;
            event := Some(inputQueue[0].event); 
            lastDispatch := inputQueue[0].time;
            inputQueue := inputQueue[1..]; 
         }  else {
            assert |recircQueue| > 0;
            assert |inputQueue| == 0 || ! inputFirst;
            if ! recircAvailable () {
               assert |inputQueue| == 0 && |recircQueue| > 0;
               assert (recircQueue[0].time > now);
               assert |recircQueue| > 0;
               now := recircQueue[0].time;
               assert now == recircQueue[0].time;
               event := Some(recircQueue[0].event);
               lastDispatch := now;
               assert now == old(recircQueue[0]).time;
            }  else {
               assert recircQueue[0].time <= now;
               assert recircAvailable ();
               assert |recircQueue| > 0;
               event := Some(recircQueue[0].event); 
               assert now == old(now);
                  
            }
            assert |recircQueue| > 0;
            recircQueue := recircQueue[1..]; 
         }
      }
   }

   twostate predicate recircGenerated(e : Event)
      // Has e been generated as a recirculation event?
      reads this`recircQueue, this`lastDispatch
   {
         var recircTime := lastDispatch + recircDelay;
         recircQueue == old(recircQueue) + [TimedEvent (e, recircTime, recircTime % T)]
   }

   method generateRecircEvent (recirc: Event) 
      // generates a recirculation event.
      modifies this`recircQueue
      requires baseInvariant ()
      ensures baseInvariant ()
      ensures lastDispatch == old (lastDispatch)
      // functional spec
      ensures recircGenerated(recirc)
   {  var recircTime := lastDispatch + recircDelay;
      recircQueue := recircQueue +
         [TimedEvent (recirc, recircTime, recircTime % T)];
   }

   twostate predicate generatedToPorts(ports: set <nat>, e: Event)
      // has an event e been generated to these ports?
     reads this`outputQueue, this`now
   {     outputQueue == old(outputQueue) + [Output (ports, e, now)]
         && outputQueue[|outputQueue|-1] == Output (ports, e, now)
    }

   //  twostate predicate generatedSomePort(pred : nat -> bool, e : Event)
   //    // has event e been generated to one output port?
   //    reads this`outputQueue, this`now
   //  { exists p : nat :: pred(p) && generated({p}, e) }

   twostate predicate generated(e : Event)
   // has this event been generated to some output ports?
      reads this`outputQueue
   {
         |outputQueue| == |old(outputQueue)| + 1
      && outputQueue[|outputQueue|-1].event == e
   }
   twostate predicate generatedPredicate(pred : Event -> bool)
   // has an event been generated that matches a predicate?
      reads this`outputQueue
   {
         |outputQueue| == |old(outputQueue)| + 1
      && pred(outputQueue[|outputQueue|-1].event)
   }
   

   method generateOutput (ports: set <nat>, e: Event)
      // generate an output event
      modifies this`outputQueue
      requires baseInvariant ()
      ensures baseInvariant ()
      ensures lastDispatch == old (lastDispatch)
      // functional spec
      ensures generatedToPorts(ports, e)
   {  outputQueue := outputQueue + [Output (ports, e, now)]; }

   method simulateClockTick (jump: nat) 
   // The clock can tick at any time.
      modifies this`now
      requires baseInvariant ()
      ensures baseInvariant ()
      ensures now == old(now) + jump
      // functional spec
   {  now := now + jump; }
}
}


module LucidObjects {

   type memcalc <!t> = (t, t) -> t
   class StateVar<t> {
      var cell : t

         constructor Create(init : t)
            ensures cell == init
            ensures fresh(this)
         {  cell := init;  }

         method Get (mget: memcalc<t>, garg: t) returns (oldVal:t)
            ensures oldVal == mget(cell, garg)
         {  oldVal := mget (cell, garg);  }

         method Set (mset: memcalc<t>, sarg: t)
            modifies this`cell
            ensures cell == mset(old(cell), sarg)
         {  cell := mset (cell, sarg);  }

         method GetSet (mget: memcalc<t>, garg: t,
                        mset: memcalc<t>, sarg: t) returns (oldVal: t)
            modifies this`cell
            ensures oldVal == mget(old(cell), garg)
            ensures cell == mset(old(cell), sarg)
         {
            oldVal := mget (cell, garg);
            cell   := mset (cell, sarg);
         }
   }

   class VarArray <t(==)> {
      var cells : seq<t>

         constructor Create(n: nat, init: t)
            ensures cells == seq(n, (_ => init))
            ensures |cells| == n
         {  cells := seq(n, (_ => init));  }

         method Get(idx: nat, mget: memcalc<t>, garg: t) 
                                                        returns (oldVal: t)
            requires 0 <= idx < |cells|
            ensures oldVal == mget(cells[idx], garg)
         {  oldVal := mget (cells[idx], garg);  }

         method Set (idx:nat, mset: memcalc<t>, sarg: t)
             modifies this`cells
             requires 0 <= idx < |cells|
             ensures cells == 
                             old(cells)[idx := mset(old(cells[idx]), sarg)]
         {
             cells := cells[idx := mset(cells[idx], sarg)];
         }

         method GetSet 
            (idx: nat, mget: memcalc<t>, garg: t,
                       mset: memcalc<t>, sarg: t) returns (oldVal: t)
            modifies this`cells
            requires 0 <= idx < |cells|
            ensures oldVal == mget(old(cells)[idx], garg)
            ensures cells == old(cells)[idx := mset(old(cells[idx]), sarg)]
        {
            oldVal := mget (cells[idx], garg);
            cells := cells[idx := mset(cells[idx], sarg)];
        }

        ghost predicate allEqual(v : t)
        reads this`cells
         {forall i ::0 <= i < |cells| ==> cells[i] == v}
      
        twostate predicate updatedCell(idx : nat, v : t)
             reads this`cells
             requires 0 <= idx < |old(cells)|
         { cells == old(cells)[idx :=v] }

    }
}



module LucidTypes {

    type uint1 = x : nat | 0 <= x < 2             
    type uint8 = x : nat | 0 <= x < 256             
    type uint16 = x : nat | 0 <= x < 65536
    type uint20 = x : nat | 0 <= x < 1048576        
    type uint24 = x : nat | 0 <= x < 16777216
    type uint32 = x : nat | 0 <= x < 4294967296     
    type uint48 = x : int | 0 <= x < 281474976710656

    const max1 : nat := 2
    const max8 : nat := 256
    const max16 : nat := 65536
    const max20 : nat := 1048576
    const max24 : nat := 16777216
    const max32 : nat := 4294967296
    const max48 : nat := 281474976710656

    function to_uint8(x : int) : uint8
        ensures to_uint8(x) == x % max8
    { x % max8 }

    function to_uint16(x : int) : uint16
        ensures to_uint16(x) == x % max16
    { x % max16 }

    function to_uint20(x : int) : uint20
        ensures to_uint20(x) == x % max20
    { x % max20 }

    function to_uint24(x : int) : uint24
        ensures to_uint24(x) == x % max24
    { x % max24 }

    function to_uint32(x : nat) : uint32
        ensures to_uint32(x) == x % max32
    { x % max32 }

   function zeros(len : uint32) : seq<uint32> 
       {  seq(len, (_ => 0))  }


   type seq2<t> = s : seq<t> | (|s| == 2) witness *
   type seq4<t> = s : seq<t> | (|s| == 4) witness *
   type seq8<t> = s : seq<t> | (|s| == 8) witness *
   type seq16<t> = s : seq<t> | (|s| == 16) witness *
   type seq32<t> = s : seq<t> | (|s| == 32) witness *
   type seq64<t> = s : seq<t> | (|s| == 64) witness *
   type seq128<t> = s : seq<t> | (|s| == 128) witness *
   type seq256<t> = s : seq<t> | (|s| == 256) witness *
   type seq512<t> = s : seq<t> | (|s| == 512) witness *
   type seq1024<t> = s : seq<t> | (|s| == 1024) witness *

}
