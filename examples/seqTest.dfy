include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)


// sequences in Dafny do not have fixed length, like they do in Lucid. 
// As a workaround, we define types for all sequence lengths
// we want to support in the library. This is very inelegant, 
// but at least it is all hidden in the library.
// Note, its still a todo (for me) to add all the necessary 
// types to the library for fixed-length sequences. 
// For now, just use the seq16 type in examples.
// Its defined in LucidTypes as:
// type seq16<t> = s : seq<t> | (|s| == 16) witness *


datatype {:lucid_event} Event = 
    // An event can carry a sequence of value types as a field.
    | foo(xs: seq16<uint32>)
{
}

class {:lucid_program} Program {
    const base : Switch<Event>
    // A program or data structure can contains sequences of globals
    // they are declared as fields and initialized in the constructor. 
    // They _must_ be initialized in the constructor because there's no 
    // way to create objects in the field declaration.
    const n := 16
    const pool : seq16<VarArray<uint32>>

    // a program or data structure can also contain a sequence of constants
    const seeds : seq16<uint32>

    constructor ()
    {
        // a sequence of constants is constructed by either enumerating the 
        // items or a sequence comprehension.
        seeds := seq(n, i => i+7 as uint32);

        // a sequence of globals is constructed by either 
        // 1. enumerating the items (that unfortunately must be defined as tmps first)
        // var pool0 := new VarArray.Create(128, 0 as uint32);
        // var pool1 := new VarArray.Create(128, 0 as uint32);
        // pool := [pool0, pool1];

        // or 2. a loop that appends to a temporary sequence variable.
        // Loop-based sequence of globals construction: 
        // 1. create empty tmp sequence var (notice: it is not a seq16 yet)
        // 2. construct all globals in a loop and append, 
        //    using the exact same constructor every time.
        // 3. assign the tmp sequence to the field
        var poolTmp : seq<VarArray<uint32>> := [];
        for i := 0 to n 
                invariant  UniqueSeqLen(poolTmp, i) && fresh(poolTmp)
                invariant (forall j | 0 <= j < i :: |poolTmp[j].cells| == n)
            {
                var tmp := new VarArray.Create(n, 0 as uint32);
                AppendIsDistributive(poolTmp, tmp);
                poolTmp := poolTmp + [tmp];
            }
        pool := poolTmp;
        base := new Switch(true);
    }

    function incr (mv: uint32, incrBy: uint32) : uint32 { 
        (mv + incrBy) % max32
    }

    method Foo(xs : seq16<uint32>)
        modifies base`outputQueue, base`recircQueue
        modifies pool
        requires forall i | 0 <= i < n :: |pool[i].cells| == 128
        requires base.baseInvariant()
        ensures base.baseInvariant()
    {
        // A handler can access elements in a sequence with constant indices.
        var x := xs[8];
        // pool[3].Set(7, incr, x);

        // A handler can also construct new sequences of values.
        // This can be done explicitly by enumerating the items.
        var ys : seq16<uint32> := [1 as uint32, 2 as uint32, 3 as uint32, 4 as uint32, 5 as uint32, 6 as uint32, 7 as uint32, 8 as uint32, 9 as uint32, 10 as uint32, 11 as uint32, 12 as uint32, 13 as uint32, 14 as uint32, 15 as uint32, 16 as uint32];

        // If the construction does not require calling methods on globals, 
        // it can be done with a "seq" constructor that translates directly 
        // into a Lucid sequence comprehension.
        var ys2 : seq16<uint32> := seq(n, i requires 0 <= i < 16 => (xs[i] + i)%max32);
        // In lucid, this can compile to: int<32>[16] ys2 = [xs[i] for i < 16];

        // If the construction requires calling global methods, Dafny 
        // does not allow it to be done in a seq comprehension, and so 
        // we must do it in a for loop, similar to how sequences of globals can be constructed.
        // We follow a very specific 3 step convention, also the same as for constructing sequences of globals.
        // 1. declare a temporary sequence variable, initialized to an empty sequence.
        // 2. construct all items in a loop and append, using the exact same constructor evert time.
        // 3. assign the temporary sequence to the final variable, which is declared as a fixed-length seq type.
        // Note that nothing else can happen in the loop besides: 1. constructing the item; 2. appending it to the tmp list.
        var ys3Tmp : seq<uint32> := [];
        for i := 0 to n
                invariant |ys3Tmp| == i
                invariant forall i | 0 <= i < n :: |pool[i].cells| == 128
                invariant base.baseInvariant()
        {
            var v := pool[i].GetSet(7, incr, xs[i], incr, xs[i]);
            ys3Tmp := ys3Tmp + [v];
        }
        var ys3 : seq16<uint32> := ys3Tmp;
        // The above 3 statements translate to the following comprehension in Lucid.
        // int<32>[16] ys3 = [pool[i].GetSet(7, incr, xs[i], incr, xs[i]) for i < 16];

        base.generateOutput({1}, foo(ys3));

    }

}
