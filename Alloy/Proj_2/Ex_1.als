sig Node {}

sig Member in Node {
    nxt: lone Member,          // each Member points to at most one next Member
    var qnxt: Node -> lone Node,   // queue mechanism linking to nodes
    outbox: set Msg            // outbox to hold messages
}

one sig Leader in Member {
    lnxt: Node -> lone Node     // specific next link for the leader if needed
}

sig LQueue in Member {}

abstract sig Msg {
    sndr: Node,               // sender of the message
    rcvrs: set Node           // receivers of the message
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
fun NonMembers[]: set Node {
    Node - Member
}

pred init[]{
    no qnxt
}

pred stutter[]{
    qnxt' = qnxt
}

pred qnxt[m: Member, n1: Node, n2: Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt        // n1 should not already point to n2 in m's queue
    n1 in NonMembers[]           // n1 must be a non-member
    n2 in NonMembers[] or n2 = m // n2 can either be another non-member or the member
    n1 != n2                     // n1 and n2 must be different (no self-pointing)

    // Postconditions
    m.qnxt' = m.qnxt + (n1 -> n2)

    // Frame conditions
    all m1: Member - m | m1.qnxt' = m1.qnxt
}

fact MQueueTermination {
    // For each member, their queue must eventually terminate with themselves
    all m: Member | all n: Node | (n->n) in m.qnxt implies ((n->m) in m.qnxt)
}

pred trans[]{
    stutter[]
    or 
    (some n1,n2:Node, m:Member | qnxt[m, n1, n2])
}

pred system[]{
    init[]
    and
    always trans[]
}


fact{
    system[]
}


// Helper function to visualize the member queues
fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

run{eventually some qnxt} for 2 steps 
// Run the model with 6 nodes, 1 leader, and 5 members
run { #Node = 6 && #Leader = 1 && #Member = 5 } for 6
