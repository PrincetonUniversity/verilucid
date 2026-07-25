/*
A packet sampler with a simple anonymizer. (an absolutely minimal version of ontas)
The condition is that any packetSample generated 
contains a source and destination IP address that is the 
hashed version of the input packet's fields. 
The same idea can extend to register writes as well.
*/


include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)

const nFlows : nat := 1024
type  flowIdx_t = f : nat | f < 1024
type  flowKey_t = (uint32, uint32)
const maxPktLen : uint32 := 2048

datatype {:lucid_event} Event = 
    | Packet(src : uint32, dst : uint32, len : uint32)
    | PacketSample(src : uint32, dst : uint32, len : uint32)

class {:lucid_program} Program {
    const switch : Switch<Event>
    const seed : nat := 7
    const collectorPort : nat := 0
    constructor ()
        ensures switch.New()
        ensures fresh(this) && fresh(switch)
    {
        switch := new Switch(true);
    }

    ghost predicate safePkt(e : Event, ie : Event) {
        e.PacketSample? ==> e.src == (hashn(32, seed, [ie.src])% max32) && (e.dst == hashn(32, seed, [ie.dst]) % max32)
    }

    method packet(src : uint32, dst : uint32, len : uint32)
        modifies switch`outputQueue
        requires switch.baseInvariant()
        ensures switch.baseInvariant()
        // any PacketSample event generated has src and dst equal to source and dest
        ensures switch.generatedPredicate(( (e : Event) => e.PacketSample?) ) 
                ==>  switch.generatedPredicate((e : Event) => safePkt(e, Packet(src, dst, len)))
    {
        var c : uint8 := to_uint8(rand32());
        if (c <= 5){
            var hashed_src := hashn(32, seed, [src]) % max32;
            var hashed_dst := hashn(32, seed, [dst]) % max32;
            switch.generateOutput({0}, PacketSample(hashed_src, hashed_dst, len));
            assert switch.generatedPredicate((e : Event) => safePkt(e, Packet(src, dst, len)));
        } 
    }
}
