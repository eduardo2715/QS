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

pred addqnxt[m: Member, n1: Node, n2: Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt               // n1 should not already point to n2 in m's queue
    n1 != n2
    n1 in (Node - Member)                       // n1 must be a non-member
    (n2 in (Node - Member)) or (n2 = m)         // n2 can either be another non-member or the member                         // n1 and n2 must be different (no self-pointing)

    // Postconditions
    m.qnxt' = m.qnxt + (n1 -> n2)

    // Frame conditions
    all m1: Member - m | m1.qnxt' = m1.qnxt
}


fact MQueueTermination {
    // For each member, their queue must eventually terminate with themselves
    all m: Member | all n1, n2: Node | 
        (n1 -> n2) in m.qnxt implies 
        (n2 = m or some n3: Node | (n2 -> n3) in m.qnxt and n3 = m)

    // No self-pointing within the queue, except at the termination
    //all m: Member, n: Node | (n -> n) !in m.qnxt
}


pred addlnxt[l: Leader, m1: Member, m2: Member] {
    // Preconditions
    (m1 -> m2) !in l.lnxt                       // m1 should not already point to m2 in l's queue
    m1 in (Member - Leader)                     // m1 must be a non leader member
    (m2 in (Member - Leader)) or (m2 = l)       // m2 can either be another non member or the leader
    m1 != m2                                    // m1 and m2 must be different (no self-pointing)

    // Postconditions
    l.lnxt' = l.lnxt + (m1 -> m2)

    // Frame conditions
    all l1: Leader - l | l1.lnxt' = l1.lnxt 
}

fact LQueueTermination {
    // For each leader, their queue must eventually terminate with themselves
    all l: Leader | all m1, m2: Member |
        (m1 -> m2) in l.lnxt implies 
        (m2 = l or some m3: Member | (m2 -> m3) in l.lnxt and m3 = l)

    // No member can point to itself in the leader's queue
    //all l: Leader, m: Member | (m -> m) !in l.lnxt
}


pred trans[] {
    stutter[]
     or 
    (some n1, n2: Node, m: Member | addqnxt[m, n1, n2])
    or
    (some m1, m2: Member, l: Leader | addlnxt[l, m1, m2])
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
    all m: Member, n1: Node, n2: Node |  (n1 -> n2) in m.qnxt implies n1 != n2
    all m1, m2: Member, n1, n2: Node, n3, n4: Node | m1 != m2 and (n1 -> n2) in m1.qnxt and (n3 -> n4) in m2.qnxt implies (n1 != n3 and n2 != n4 and n1 != n4 and n2 != n3)
}

assert MemberQueueTermination {
    all m: Member | 
        all n1, n2: Node | 
            (n1 -> n2) in m.qnxt implies 
            n2 = m or no n3: Node | (n2 -> n3) in m.qnxt
}


check MemberQueueTermination


run{
    eventually #(Member.qnxt) > 1
    eventually #(Leader.lnxt) > 1
} for 3 steps 
// Run the model with 6 nodes, 1 leader, and 5 members
run { #Node = 6 && #Leader = 1 && #Member = 5 } for 6





// Helper predicates to enforce configuration requirements

// Predicate to ensure that the leader queue is not empty
pred NonEmptyLeaderQueue[] {
    no Leader.lnxt
}

// Predicate to ensure that at least two member queues are not empty
pred AtLeastTwoNonEmptyMemberQueues[] {
    #(Member.qnxt) = 1
}

// Run the model to generate a configuration with at least 5 nodes, non-empty leader queue, and two non-empty member queues
run {
    #Node >= 5
    NonEmptyLeaderQueue[]
    AtLeastTwoNonEmptyMemberQueues[]
} for 6

// Run the model again for a second configuration