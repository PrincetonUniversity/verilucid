/* 
A simple MAC learner, that we prove a basic property about: 

For any MAC address, 
    if the mac address is not in the table
    and the table has free slots
    the MAC address gets put into the table after some bounded amount of time t

*/
include "../src/lib/lucidLibrary.dfy"
import opened LucidTypes   // bounded integer types (uint8, ...)
import opened LucidObjects // arrays, statevars, and memops
import opened LucidSwitch    // switch model
import opened LucidHelpers // other helpers (hash, rand, etc)

    // Events
    datatype {:lucid_event} Event = 
        | pkt(src : uint32, dst : uint32, ingress_port : uint8)
        | install(src : uint32, port : uint8)

    class {:lucid_program} Program {
        const switch : Switch<Event>
        const N : nat := 1024
        const seed : uint32 := 7

        ghost predicate ValidArrays ()
            reads this, this.src_ports, this.dst_ports
        {
            |src_ports.cells| == N
            && |dst_ports.cells| == N
        }

        // Array and initialization
        const src_ports : VarArray<uint8>
        const dst_ports : VarArray<uint8>

        constructor () 
            ensures fresh(src_ports)
            ensures fresh(dst_ports)
            ensures fresh(this)
            ensures fresh(switch)
            ensures src_ports.cells == seq(N, (_ => 0))
            ensures dst_ports.cells == seq(N, (_ => 0))
            ensures ValidArrays()
            ensures switch.New()
        {   
            src_ports := new VarArray<uint8>.Create(N, 0);
            dst_ports := new VarArray<uint8>.Create(N, 0);
            switch := new Switch(true);
        }

        // Memops
        function memval8 (mv: uint8, unused: uint8) : uint8 { mv }
        function newval8 (unused : uint8, nv : uint8) : uint8 { nv }

        // Handlers
        method Pkt(src : uint32, dst : uint32, ingress_port : uint8)
            modifies    switch`outputQueue, switch`recircQueue
            requires switch.baseInvariant()
            requires ValidArrays()
            ensures switch.baseInvariant()
            ensures  ValidArrays()
            ensures src_ports.cells[hashn(10, seed, [src])] != ingress_port <==> switch.recircGenerated(install(src, ingress_port))
            ensures  
                var out_port := dst_ports.cells[hashn(10, seed, [dst])];
                if (out_port != 0) then (
                    switch.generatedToPorts({out_port}, pkt(src, dst, ingress_port))
                ) else (
                    switch.generatedToPorts({flood(ingress_port)}, pkt(src, dst, ingress_port))
                )
        {
            var src_idx := hashn(10, seed, [src]);
            var dst_idx := hashn(10, seed, [dst]);
            var sport := src_ports.Get(src_idx, memval8, 0);
            // Recirculate to install
            if (sport != ingress_port) {
                switch.generateRecircEvent(install(src, ingress_port));
                assert switch.recircGenerated(install(src, ingress_port));
            }
            var dport := dst_ports.Get(dst_idx, memval8, 0);
            if (dport == 0) {
                switch.generateOutput({flood(ingress_port)}, pkt(src, dst, ingress_port));
                assert switch.generatedToPorts({flood(ingress_port)}, pkt(src, dst, ingress_port));
            } else {
                switch.generateOutput({dport}, pkt(src, dst, ingress_port));
                assert switch.generatedToPorts({dport}, pkt(src, dst, ingress_port));
            }
        }
        // Just set the port in both arrays
        method Install(src : uint32, port : uint8)
            modifies this.src_ports`cells, this.dst_ports`cells
            requires ValidArrays() && switch.baseInvariant()
            ensures ValidArrays() && switch.baseInvariant()
            ensures src_ports.cells[hashn(10, seed, [src])] == port
            ensures dst_ports.cells[hashn(10, seed, [src])] == port
        {
            var idx := hashn(10, seed, [src]);
            src_ports.Set(idx, newval8, port);
            dst_ports.Set(idx, newval8, port);
        }
    }

    method EventualInstall()
    {
        var p := new Program();
        var switch := p.switch;
        var src : uint32 := *;
        var dst : uint32 := *;
        var port : uint8 :| port > 0;
        
        // send the packet in
        label L1:
        p.Pkt(src, dst, port);
        // This packet got flooded.
        assert switch.generatedToPorts@L1({flood(port)}, pkt(src, dst, port));

        switch.simulateClockTick(1);

        label L:
        var trecirc : nat :| switch.recircDelay < trecirc < switch.recircDelay + 1000;
        for i := 0 to trecirc
            invariant p.ValidArrays() && switch.baseInvariant()
            invariant |switch.recircQueue| > 0
            invariant |switch.inputQueue| == 0
            invariant switch.nextRecircEvent() == install(src, port)

            // invariant p.handlingRecirc == false
            // invariant p.generatedEvent == None
            invariant switch.now == old@L(switch.now) + i
            // invariant |p.recircQueue| >= |old@L(p.recircQueue)|
            // invariant p.recircQueue[0] == old@L(p.recircQueue)[0]
        {
            var arrival := rand(0, 1);
            if (arrival == 1) {
                var s : uint32 := *;
                var d : uint32 := *;
                var port : uint32 :| port > 0;
                p.Pkt(s, d, port);
            }
            switch.simulateClockTick(1);            
        }
        // handle the next recirc event when there's a pause
        var e := switch.pickNextEvent();
        match e {
            case Some(install(src, port)) => 
                p.Install(src, port);
        }
        // // wait a bit longer, then process the return packet
        switch.simulateClockTick(1);
        var port_of_dst : uint8 :| 0 < port_of_dst;
        label F:
        p.Pkt(dst, src, port_of_dst);
        // we emitted the packet to the expected port.
        assert switch.generatedToPorts@F({port}, pkt(dst, src, port_of_dst));
    }
