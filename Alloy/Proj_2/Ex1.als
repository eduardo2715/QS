sig Node {
  outbox: set Msg
}

sig Member in Node { 
 nxt: one Node, 
 qnxt : Node -> lone Node 
}

one sig Leader in Member {
   lnxt: Member -> lone Member
}

sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  rcvrs: set Node 
}

sig SentMsg, SendingMsg, PendingMsg in Msg {}

//// TOPOLOGICAL CONSTRAINTS

// members form a ring with each member pointing to another member (or itself);
fact RingTopology {
    all m:Member | m.(^nxt) = Member
}

// function that returns the set of elements that are in the Member queue of a given member 
fun MemberQueueElements[m: Member]:set Node{
    m.^(~(m.qnxt))
}

// function that returns the set of elements that are in the Leader queue of a given leader
fun LeaderqueueElements[l: Leader]:set Member{
    l.^(~(l.lnxt))
}

//a node that belongs to a member queue cannot belong to another member queue
// all elements inside Menber queue must be non-Member Nodes (no Members)
fact MQueueTermination {
    all m1,m2: Member | m1 != m2 implies no (MemberQueueElements[m1] & MemberQueueElements[m2])
    all m: Member | no (Member & MemberQueueElements[m])
}

// all members that are Lqueue are in the leader queue
// all elements inside Leader queue must be non-Leader members (no nodes that are not members and no leaders)
fact LQueueTermination {
    all q: LQueue, l: Leader | q in LeaderqueueElements[l]
    all l: Leader | no(LeaderqueueElements[l] & (Leader + (Node - LQueue)))
}

// Each member/Leader must have at most 1 queue
fact OneQueuePerNode{
    all m: Member | #((m.qnxt)).m <= 1
    all l: Leader | #((l.lnxt)).l <= 1
}

// Helper function to visualize the member queues
fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

// Helper function to visualize the leader queue
fun VisualizeLeaderQueues[]: Node -> lone Node {
    Leader.lnxt
}

//// MESSAGE-CONSISTENCY CONSTRAINTS



//Only sending or sent messages have receivers
//A sender cannot be in its receivers
fact receivers{
    all msg:Msg | msg in PendingMsg implies no(msg.rcvrs)
    all msg:Msg | no (msg.rcvrs & msg.sndr)
}

fact {
    all msg:Msg | no (msg.sndr & (Node - Member))
    all msg:Msg | no (msg.rcvrs & (Node - Member))
    all n:Node-Member | no(n.outbox)
}

//if a message is in a sending state it means that it must have receivers and it belongs to someones outbox
fact sendingMessage{
    all msg:Msg | msg in SendingMsg implies some (msg.rcvrs) and some n:Node | msg in n.outbox
    one SendingMsg
    SendingMsg in (Member - Leader).outbox

}

//if a message is in a pending state it means that it must not have receivers and it belongs to the senders outbox
fact pendingMessage{
    all msg:Msg | msg in PendingMsg implies no (msg.rcvrs)
     PendingMsg in Leader.outbox
}

//if a message is in a sent state it means that it must have receivers and it belongs to the senders outbox
fact sentMessage{
    // all msg:Msg | msg in SentMsg implies some (msg.rcvrs) and all n:Node | msg !in n.outbox
     no (SentMsg & Member.outbox)
     //received by someone
}

//THIS IS JUST FOR TESTING
//Run the model with 5 nodes, 1 leader
//at least 2 mambers
//one of the members queue must have more than one node
//leader queue must have more than one node
run {
    #Leader = 1 && 
    #Node > 5 &&
     some m1, m2: Member, l: Leader |
        m1 != m2 &&
        some MemberQueueElements[m1] &&
        #MemberQueueElements[m1] > 1 &&
        some MemberQueueElements[m2] &&
        some LeaderqueueElements[l] &&
        #LeaderqueueElements[l] > 1 &&
        #SentMsg > 1 &&
        #SendingMsg = 1 &&
        #PendingMsg > 1
} for 7
