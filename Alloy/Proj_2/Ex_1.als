sig Node {}  // Non-member nodes (green in the diagram)

sig Member in Node {  
    nxt: lone Member,                // Next member in the ring (blue in the diagram)
    qnxt: Node -> lone Node,         // Queue of nodes (green) pointing to this member
    outbox: set Msg
}

one sig Leader in Member {           // Leader member (L in the diagram)
    lnxt: Node -> lone Node          // Leader-specific queue relation
}

abstract sig Msg {
    sndr: Node,
    rcvrs: set Node
}

sig SentMsg, SendingMsg, PendingMsg extends Msg {}

// Fact to enforce the ring topology for the members
fact RingTopology {
    // 1. Every member has a next member (forming a closed ring)
    all m: Member | some m.nxt

    // 2. The set of members forms a strongly connected cycle (every member is reachable from every other member)
    all m: Member | m in m.^nxt  // Transitive closure of nxt relation must include the member itself
}



run {#Node = 6} for 6
