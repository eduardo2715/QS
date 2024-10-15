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

fun MemberQueueElements[m: Member]:set Node{
    m.^(~(m.qnxt))
}

fun MemberQueueElementsTest[m: Member]:set Node{
    m.*(~(m.qnxt))
}

fun LeaderqueueElements[l: Leader]:set Member{
    l.^(~(l.lnxt))
}

fun LeaderQueueConnections[l: Leader]:set Node -> Node {
    // Collect the set of all (n -> n') pairs in lnxt, i.e., L -> M1, M1 -> M2, M2 -> M3, ...
    ^(l.lnxt)
}

fun MemberQueueConnections[m: Member]:set Node -> Node {
    // Collect the set of all (n -> n') pairs in qnxt, i.e., M1 -> N1, N1 -> N2, N2 -> N3, ...
    ^(m.qnxt)
}


fact MQueueTermination {
    all m1,m2: Member | m1 != m2 implies no (MemberQueueElements[m1] & MemberQueueElements[m2])
    all m: Member | no (Member & MemberQueueElements[m])
    //all m: Member, n1,n2:Node | #MemberQueueElements[m] > 0 implies n1.^(m.qnxt) != n2.^(m.qnxt)
}

fact LQueueTermination {
    all q: LQueue, l: Leader | q in LeaderqueueElements[l]
    all l: Leader | no(LeaderqueueElements[l] & (Leader + (Node - LQueue)))
    //all l: Leader | all m1, m2: LeaderqueueElements[l] | m1 != m2 implies m1.^(l.lnxt) != m2.^(l.lnxt)
    //  all l: Leader | all m: Member | (l -> m) in Leader.lnxt
    }

// Helper function to visualize the member queues
fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

fun VisualizeLeaderQueues[]: Node -> lone Node {
    Leader.lnxt
}

assert CorrectQueues {
    //all m: Member | (Member !in MemberQueueElements[m])
    //all m: Member, n1,n2:Node | ((n1 in MemberQueueElements[m]) && (n2 in MemberQueueElements[m])) implies n1 != n2
    all m: Member, n1,n2:MemberQueueElements[m] | #MemberQueueElements[m] > 1 implies n1.^(m.qnxt) != n2.^(m.qnxt)
}

check CorrectQueues



// Run the model with 6 nodes, 1 leader, and 5 members
run {
    #Leader = 1 && 
    #Node > 5 &&
     some m1, m2: Member, l: Leader |
        m1 != m2 &&
        some MemberQueueElements[m1] &&
        //#MemberQueueElements[m1] > 0 &&
        some MemberQueueElements[m2] &&
        some LeaderqueueElements[l] //&&
        //#LeaderqueueElements[l] > 0
} for 7
//some m1 , m1 != m2 some queue[m1] and some queue[m2]
