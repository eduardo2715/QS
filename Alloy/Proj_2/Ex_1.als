sig Node {}

sig Member in Node {
    nxt: lone Member,   
    var qnxt: Node -> lone Node, 
    outbox: set Msg
}

one sig Leader in Member {
    var lnxt: Node -> lone Node
}

sig LQueue in Member {}

abstract sig Msg {
    sndr: Node,
    rcvrs: set Node
}

// Fact to enforce the ring topology for the members
fact RingTopology {
    // 1. Every member has a next member (forming a closed ring)
    all m: Member | some m.nxt

    // 2. Only the Leader can point to itself, others must point to a different member
    all m: Member - Leader | m.nxt != m

    // 3. The set of members forms a strongly connected cycle (every member is reachable from every other member)
    all m: Member | m in m.^nxt  

    // 4. Leader must be part of the ring (reachable through transitive closure of nxt)
    all m: Member | Leader in m.^nxt
}

// Helper function to get the set of non-member nodes
/* fun NonMembers[]: set Node {
    Node - Member
}

fun OnlyMembers[]: set Node {
    Member - Leader
} */

pred init[]{
    no qnxt
    no lnxt
}

pred stutter[]{
    qnxt' = qnxt
}

pred qnxt[m: Member, n1: Node, n2: Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt               // n1 should not already point to n2 in m's queue
    n1 !in Member                       // n1 must be a non-member
    (n2 !in Member) or (n2 = m)         // n2 can either be another non-member or the member
    n1 != n2                            // n1 and n2 must be different (no self-pointing)

    // Postconditions
    m.qnxt' = m.qnxt + (n1 -> n2)

    // Frame conditions
    all m1: Member - m | m1.qnxt' = m1.qnxt
}

fact MQueueTermination {
    // For each member, their queue must eventually terminate with themselves
    all m: Member | all n1, n2: Node | (n1->n2) in m.qnxt implies ((n1->m) in m.qnxt) and n1 != n2

    all m: Member, n: Node | (n -> n) !in m.qnxt
}

pred lnxt[l: Leader, m1: Member, m2: Member] {
    // Preconditions
    (m1 -> m2) !in l.lnxt                       // m1 should not already point to m2 in l's queue
    m1 in (Member - Leader)                     // m1 must be a non leader member
    (m2 in (Member - Leader)) or (m2 = l)       // m2 can either be another non leder member or the leader
    m1 != m2                                    // m1 and m2 must be different (no self-pointing)

    // Postconditions
    l.lnxt' = l.lnxt + (m1 -> m2)

    // Frame conditions
    all l1: Leader - l | l1.lnxt' = l1.lnxt 
}

fact LQueueTermination {
    // For each leader, their queue must eventually terminate with themselves
    all l: Leader | all m1, m2: Member | (m1->m2) in l.lnxt implies ((m1->l) in l.qnxt) and m1!=m2

    all l: Leader, m: Member | (m -> m) !in l.lnxt
}

pred trans[] {
    stutter[]
    or 
    (some n1, n2: Node, m: Member | n1 in Node and n2 in (Node - Member) and n1 != n2 and qnxt[m, n1, n2])
    or
    (some m1, m2: Member, l: Leader | m1 in (Member - Leader) and m2 in Member and m1 != m2 and lnxt[l, m1, m2])
}


pred system[]{
    init[]
    and
    always trans[]
}


fact{
    system[]
}

// Ensure that no non-member node is queued by more than one member at a time
fact UniqueNonMemberQueue {
    // For any two members m1 and m2, if a non-member node n1 is in m1's queue,
    // it cannot appear in m2's queue for a different node.
    all m1, m2: Member, n1, n2: Node, n3, n4: Node | 
        m1 != m2 and (n1 -> n2) in m1.qnxt and (n3 -> n4) in m2.qnxt implies (n1 != n3 and n2 != n4 and n1 != n4 and n2 != n3)

}


// Helper function to visualize the member queues
fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

fun VisualizeLeaderQueues[]: Node -> lone Node {
    Leader.lnxt
}

assert CorrectQueues {
    all l: Leader, m1: Member, m2: Member | (m1 -> m2) in l.lnxt implies m1 in (Member - Leader) and (m2 in (Member - Leader) or m2 = l)
    all m: Member, n1: Node, n2: Node |  (n1 -> n2) in m.qnxt implies n1 in (Node - Member) and n2 in Member
    all m1, m2: Member, n1, n2: Node, n3, n4: Node | m1 != m2 and (n1 -> n2) in m1.qnxt and (n3 -> n4) in m2.qnxt implies (n1 != n3 and n2 != n4 and n1 != n4 and n2 != n3)

}
check CorrectQueues


run{
    eventually some qnxt
    eventually some lnxt
} for 3 steps 
// Run the model with 6 nodes, 1 leader, and 5 members
run { #Node = 6 && #Leader = 1 && #Member = 5 } for 6
