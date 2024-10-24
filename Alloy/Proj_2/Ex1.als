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

// Members form a ring with each member pointing to another member (or itself);
fact RingTopology {
    all m:Member | m.(^nxt) = Member
}

// Function that returns the set of elements that are in the Member queue of a given member 
fun MemberQueueElements[m: Member]:set Node{
    m.^(~(m.qnxt))
}

// Function that returns the set of elements that are in the Leader queue of a given leader
fun LeaderqueueElements[l: Leader]:set Member{
    l.^(~(l.lnxt))
}

// A node that belongs to a member queue cannot belong to another member queue
// All elements inside Menber queue must be non-Member Nodes (no Members)
// A member queue must terminate in the member
fact MQueueTermination {
    all m1,m2: Member | m1 != m2 implies no (MemberQueueElements[m1] & MemberQueueElements[m2])
    all m: Member | no (Member & MemberQueueElements[m])
    all n: Node | all m: Member | some n.(m.qnxt) implies m in n.^(m.qnxt)
}

// All members that are Lqueue are in the leader queue
// All elements inside Leader queue must be LQMembers
// Leader queue must end in the leader, each Leader queue member must point to exactly 1 other member an be pointed by at most 1 member 
fact LQueueTermination {
    all q: LQueue, l: Leader | q in LeaderqueueElements[l]
    no(LeaderqueueElements[Leader] & (Leader + (Node - LQueue)))
    all m: Member | some m.(Leader.lnxt) implies Leader in m.^(Leader.lnxt) && lone m.~(Leader.lnxt) && one m.(Leader.lnxt)
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

// A sender cannot be in its receivers
fact receivers{
    all msg:Msg | no (msg.rcvrs & msg.sndr)
}

// Non-Members cannot be message receivers
fact {
    all msg:Msg | no (msg.rcvrs & (Node - Member))
}

// If a message is in a sending state it means that it must have receivers and it belongs to someones outbox
// There can only be one or none sending message at each time
// Only non-leader members can have sending messages in their outboxes
fact sendingMessage{
    all msg:Msg | msg in SendingMsg implies some (msg.rcvrs) and some n:Node | msg in n.outbox
    lone SendingMsg
    SendingMsg in (Member - Leader).outbox
}

// If a message is in a pending state it means that it must not have receivers and it belongs to the senders outbox
fact pendingMessage{
    all msg: PendingMsg | no (msg.rcvrs)
    all msg: PendingMsg | msg in msg.sndr.outbox
}

// If a node has a message in its outbox that belongs to the leader than the node is a member and the node is in the rcvrs of that message
fact outbox {
    all n: Node - Leader | 
    all msg: Msg | msg in n.outbox and msg.sndr = Leader implies n in Member && n in msg.rcvrs

}

// If a message is in a sent state it means that it must have receivers and it belongs to the senders outbox
fact sentMessage{
    no (SentMsg & Member.outbox)
    all msg: SentMsg | some msg.rcvrs
}

//each message must belong to one of the three types (pending, sending, sent)
fact MessageType{
    all msg:Msg | msg in PendingMsg or msg in SendingMsg or msg in SentMsg
}

// NETWORK CONFIGURATION
// 1 Leader
// At least 5 Nodes
// 2 non-empty member queues
// 1 non-empty leader queue
// at least on sent message
// at least on sending message
// at least on pending message
run {
    #Leader = 1 && 
    #Node >= 5 &&
     some m1, m2: Member |
        m1 != m2 &&
        some MemberQueueElements[m1] &&
        some MemberQueueElements[m2] &&
        some LeaderqueueElements[Leader] &&
        #SentMsg > 0 &&
        #SendingMsg > 0 &&
        #PendingMsg > 0
} for 7
