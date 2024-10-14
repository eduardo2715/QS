sig Node {}

sig Member in Node {
    nxt: one Member,   
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
    all m:Member | m.(^nxt) = Member
}

fun MemberqueueElements[m: Member]:set Node{
    m.^(~(m.qnxt))
}
fun LeaderqueueElements[l: Leader]:set Member{
    l.^(~(l.lnxt))
}


// Helper function to get the set of non-member nodes
/* fun NonMembers[]: set Node {
    Node - Member
}

fun OnlyMembers[]: set Node {
    Member - Leader
} */



fact MQueueTermination {
    // For each member, their queue must eventually terminate with themselves
    // all m: Member | all n1, n2: Node | 
    //     (n1 -> n2) in m.qnxt implies 
    //     (n1 = m or some n3: Node | (n1 -> n3) in m.qnxt and n3 not in Member)

    // all m: Member | all n: Node - Member | (m -> n) in m.qnxt implies no (n -> m)

    // all m: Member | all n1,n2: Node - Member | (m -> n1) in m.qnxt implies (m -> n2) !in m.qnxt
    // all m: Member | all n1,n2: Node - Member | (n1->n2) in m.qnxt implies n1 != n2
    // No self-pointing within the queue, except at the termination
    //all m: Member, n: Node | (n -> n) !in m.qnxt
    all m1,m2: Member | m1 != m2 implies no (MemberqueueElements[m1] & MemberqueueElements[m2])
    all m: Member | no (Member & MemberqueueElements[m])

}




fact LQueueTermination {
    // For each leader, their queue must eventually terminate with themselves
//     all l: Leader | all m1, m2: Member |
//         (m1 -> m2) in l.lnxt implies 
//         (m2 = l or some m3: Member | (m2 -> m3) in l.lnxt and m3 = l)

//     // No member can point to itself in the leader's queue
     all q: LQueue, l: Leader | q in LeaderqueueElements[l]
    all l: Leader | no(LeaderqueueElements[l] & (Node - Member))
    //  all l: Leader | all m: Member | (l -> m) in Leader.lnxt
    }



// Ensure that no non-member node is queued by more than one member at a time
// fact UniqueNonMemberQueue {
//     // For any two members m1 and m2, if a non-member node n1 is in m1's queue,
//     // it cannot appear in m2's queue for a different node.
//     all m1, m2: Member, n1, n2: Node, n3, n4: Node | 
//         m1 != m2 and (n1 -> n2) in m1.qnxt and (n3 -> n4) in m2.qnxt implies (n1 != n3 and n2 != n4 and n1 != n4 and n2 != n3)

// }

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

check CorrectQueues


// Run the model with 6 nodes, 1 leader, and 5 members
run {#Leader = 1 && #Node = 7 && some m1,m2:Member | m1 != m2 && some MemberqueueElements[m1] && some MemberqueueElements[m2] } for 7
//some m1 , m1 != m2 some queue[m1] and some queue[m2]
