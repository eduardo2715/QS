sig Node {}

sig Member in Node {
    nxt: lone Member,
    qnxt : Node -> lone Node,
    outbox: set Msg
}

one sig Leader in Member {
    lnxt: Node -> lone Node
}

sig LQueue in Member {}

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
