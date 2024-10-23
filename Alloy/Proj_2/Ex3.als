sig Node {
  var outbox: set Msg
}

var sig Member in Node { 
 var nxt: one Node, 
 var qnxt : Node -> lone Node 
}

var one sig Leader in Member {
   var lnxt: Member -> lone Member
}

var sig LQueue in Member {}

sig Msg {
  sndr: Node, 
  var rcvrs: set Node 
}

var sig SentMsg, SendingMsg, PendingMsg in Msg {}

// Members form a ring with each member pointing to another member (or itself);
fact RingTopology {
    all m:Member | m.(^nxt) = Member
}

fun MemberqueueElements[m: Member]:set Node{
    m.^(~(m.qnxt))
}
fun LeaderqueueElements[l: Leader]:set Member{
    l.^(~(l.lnxt))
}

pred init[]{
    no qnxt
    no lnxt
    Member = Leader
    no SendingMsg
    no SentMsg
    all m: Msg | m in PendingMsg 
    && #outbox.m = 1 and m in m.sndr.outbox
    no rcvrs
    
}


pred stutter[]{
    qnxt' = qnxt
    lnxt' = lnxt
    nxt' = nxt
    Member' = Member
    Leader' = Leader
    Msg' = Msg
    LQueue' = LQueue
    PendingMsg' = PendingMsg
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    rcvrs' = rcvrs
    outbox' = outbox
}

pred stutterMessage[]{
    Msg' = Msg
    rcvrs' = rcvrs
    sndr' = sndr
    outbox' = outbox
    PendingMsg' = PendingMsg
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
}
pred stutterLeader[]{
    Leader' = Leader
    lnxt' = lnxt
    LQueue' = LQueue
}
pred stutterMember[]{
    qnxt' = qnxt

}
pred stutterRing[]{
    nxt' = nxt
    Member' = Member
}

pred memberApplication[m: Member, n: Node] {
    some n2: Node | memberApplicationAux[m, n, n2]
}

pred memberApplicationAux[m: Member, n1: Node, n2: Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt                   // n1 should not already point to n2 in m's queue
    n1 != n2                                // n1 and n2 must be different (no self-pointing)
    n1 in Node - Member                     // n1 must not already be a Member
    n1 not in MemberqueueElements[m]         // n1 should not already be in the member's queue

    
    #MemberqueueElements[m] = 0 implies n2 = m // If the queue is empty, n2 should be the member itself (n1 will point to the member)
    
    #MemberqueueElements[m] > 0 implies { // If the queue is not empty, n2 must be the last node in the queue
        n2 in MemberqueueElements[m]          // n2 is a node in the queue
        no n0: Node | (n0 -> n2) in m.qnxt    // n2 should not point to any other node (last in the queue)
    }

    // Postconditions
    m.qnxt' = (n1 -> n2) + m.qnxt             //add the member to the queue, Add the new connection (n1 -> n2)
    
    // Frame conditions
    stutterLeader[]
    stutterMessage[]
    stutterRing[]
    all m2 : Member' - m | m2.qnxt' = m2.qnxt 
}



pred memberPromotion[m:Member, n:Node]{
    //Preconditions
    (n -> m) in m.qnxt //the node is the first in line to become member
    n in Node - Member //node isnt a member
    n in MemberqueueElements[m] //node is in the queue


    //Postconditions
    nxt' = nxt - (m->m.nxt) + (m->n) + (n->m.nxt) //add the member to the ring, member now points to newly appointed node
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (~(m.qnxt)[n] -> n) + (~(m.qnxt)[n] -> n.(m.qnxt)) //remove node from the queue, remove links (n->next) and (prev->n) add link (prev -> next)
    Member' = Member + n //node becomes a Member

    //Frame conditions
    all m2 : Member' - m | m2.qnxt' = m2.qnxt
    stutterMessage[]
    stutterLeader[] 
}

pred memberExit[m:Member]{ //not working properly
    //Preconditons
    m not in Leader //member isn't the leader
    m not in LeaderqueueElements[Leader] // member not in the leader queue elements
    no (MemberqueueElements[m]) //member cant have a member queue
    some sndr.m implies all m: sndr.m | m in SentMsg //FIXME: ??????????
    no (m.outbox) //FIXME: can the member have pending messages or no messages
    one (m.nxt) //member is part of the ring

    //Postconditions

    Member' = Member - m // remove member(m) from Members
    nxt' = nxt - ((m.~nxt) -> m) - (m -> m.nxt) + ((m.~nxt) -> m.nxt) //remove members from the ring, remove link (prev -> m) and (m -> next) add link (prev -> next)

    //Frame conditions
    stutterMessage[]
    stutterLeader[]
    stutterMember[]

}

pred nonMemberExit[m: Member, n: Node] {
    // Preconditions
    n not in Member                        // n isn't a member
    n in MemberqueueElements[m]            // n is in m's queue

    //Postconditions
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (~(m.qnxt)[n] -> n) + (~(m.qnxt)[n] -> n.(m.qnxt)) //remove node from the queue, remove links (n->next) and (prev->n) add link (prev -> next)

    // Frame conditions
    all m2 : Member' - m | m2.qnxt' = m2.qnxt
    stutterRing[]
    stutterLeader[]
    stutterMessage[]
}

pred leaderApplication[l: Leader, m: Member] {
    some m2: Member | leaderApplicationAux[l, m, m2]
}

pred leaderApplicationAux[l: Leader, m1: Member, m2: Member] {
    // Preconditions
    (m1 -> m2) !in l.lnxt                   // m1 should not already point to m2 in l's queue
    m1 != m2                                // m1 and m2 must be different (no self-pointing)
    m1 in Member - Leader                     // m1 must not be a Leader
    m1 not in LeaderqueueElements[l]         // m1 should not already be in the member's queue
    
    #LeaderqueueElements[l] = 0 implies m2 = l // If the queue is empty, m2 should be the leader itself (m1 will point to the leader)
    
    #LeaderqueueElements[l] > 0 implies { // If the queue is not empty, m2 must be the last node in the queue
        m2 in LeaderqueueElements[l]          // m2 is a Member in the leader queue
        no m0: Member | (m0 -> m2) in l.lnxt    // m2 should not point to any other member (last in the queue)
    }

    // Postconditions
    l.lnxt' = (m1 -> m2) + l.lnxt             // Add the new connection (m1 -> m2)

    // Frame conditions
    stutterRing[]
    stutterMember[]
    stutterMessage[]
}

pred leaderPromotion[l:Leader, m:Member]{
    //Preconditions
    (m -> l) in l.lnxt //the node is the first in line to become member
    m in Member - Leader //member is not a leader
    m in LeaderqueueElements[l] //node is in the leader queue elements
    no l.outbox //FIXME: is this correct? Leader can have pending messages no?
    sndr.Leader in SentMsg //the leader has no sending message

    //Postconditions
    m.lnxt' = l.lnxt - (m->l) //remove leader queue link from the member to the leader
    Leader' = m //node becomes a member

    //Frame conditions
    stutterRing[]
    stutterMember[]
    stutterMessage[]
}

pred broadcastInitialisation[l: Leader, m: Msg]{
    //Pre conditions
    m in l.outbox //message must be in the leader outbox
    l in m.sndr //leader must be the message sender
    some l.nxt //TODO: remove
    l.nxt != l //next member in the ring cannot be the leader
    l.nxt in Member //TODO: remove
    m in PendingMsg //message must be in a pending state
    no m.rcvrs //message cannot have receivers

    //Post conditions
     m in l.outbox implies l.outbox' = l.outbox - m && //remove message from leader outbox
     l.nxt.outbox' = l.nxt.outbox + m && //add message to the next ring member outbox
     m.rcvrs' = m.rcvrs + l.nxt && //add the next ring member to the message receivers
     PendingMsg' = PendingMsg - m && //message is no longer pending
     SendingMsg' = m //message is now sending

    //Frame conditions
    stutterRing[]
    stutterMember[]
    stutterLeader[]
    SentMsg' = SentMsg
    all m2: Msg - m | m2.rcvrs' = m2.rcvrs
    all m3 : Member - Leader - Leader.nxt | m3.outbox' = m3.outbox
}

pred MessageRedirect[m:Member,msg: Msg]{
    //Pre conditions
    msg in m.outbox  //message must be in the member outbox
    msg in SendingMsg  //message must be in a sending state
    m.nxt !in Leader //next member in the ring cannot be the leader

    //Post conditions
    msg.rcvrs' = msg.rcvrs + m.nxt //add next ring member to the message receivers
    m.outbox' = m.outbox - msg //remove message from the member outbox
    m.nxt.outbox' = m.nxt.outbox + msg //add the message to the next ring member outbox

    //Frame conditions
    stutterRing[]
    stutterLeader[]
    stutterMember[]
    PendingMsg ' =  PendingMsg
    SentMsg' = SentMsg
    SendingMsg' = SendingMsg
    all m3 : Member - m - m.nxt | m3.outbox' = m3.outbox
}

pred broadcastTermination[m:Member,msg: Msg]{
    //Pre conditions
    msg in m.outbox  //message must be in the member outbox
    msg in SendingMsg  //message must be in a sending state
    m in msg.rcvrs //member must be in the message receivers
    m.nxt = Leader //next member in the ring must be the leader
    m != Leader //member cannot be the leader
    //Post conditions
    m.outbox' = m.outbox - msg //remove message from the member outbox

    //Frame conditions
    stutterRing[]
    stutterLeader[]
    stutterMember[]
    SentMsg' =  SentMsg + msg
    SendingMsg' = SendingMsg - msg
    PendingMsg' = PendingMsg
    all m3 : Member - m | m3.outbox' = m3.outbox
    msg.rcvrs' = msg.rcvrs 
    msg.sndr' = msg.sndr
}

pred trans[] {
    stutter[]
    or
    (some n1, n2: Node | memberApplication[n1, n2])
    or
    (some m: Member, n: Node | memberPromotion[m, n])
    or
    (some m: Member, n: Node | nonMemberExit[m ,n])
    or
    (some m: Member | memberExit[m])
    or
    (some l: Leader | some m: Member |  leaderApplication[l, m])
    or 
    (some l: Leader | some m: Member  | leaderPromotion[l,m])
    or 
    (some l: Leader, m: Msg | broadcastInitialisation[l,m])
    or 
    (some m: Member | some sm: Msg | MessageRedirect[m, sm])
    or
    (some m: Member - Leader, msg: Msg | broadcastTermination[m,msg])
    
}

pred system[]{
    init[]
    and
    always trans[]
}

// Helper function to visualize the member queues
fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

// Helper function to visualize the leader queues
fun VisualizeLeaderQueues[]: Node -> lone Node {
    Leader.lnxt
}

fact{
    system[]
}

// Each member/Leader must have at most 1 queue
fact OneQueuePerNode{ //this might not be needed
    all m: Member | #((m.qnxt)).m <= 1
    all l: Leader | #((l.lnxt)).l <= 1
}


//TODO: not working, integrate this in leader application pre-condition
fact{
    all q: LQueue, l: Leader | q in LeaderqueueElements[l]
}


assert ValidTopology{
    all m:Member | m.(^nxt) = Member

    all m1,m2: Member | m1 != m2 implies no (MemberqueueElements[m1] & MemberqueueElements[m2])
    all m: Member | no (Member & MemberqueueElements[m])
    all n: Node | all m: Member | some n.(m.qnxt) implies m in n.^(m.qnxt)


    no(LeaderqueueElements[Leader] & (Leader + (Node - LQueue)))
    all q: LQueue, l: Leader | q in LeaderqueueElements[l]
    all m: Member | some m.(Leader.lnxt) implies Leader in m.^(Leader.lnxt) && lone m.~(Leader.lnxt) && one m.(Leader.lnxt)

    all m: Member | #((m.qnxt)).m <= 1
    all l: Leader | #((l.lnxt)).l <= 1
}

assert ValidMessage{
    all msg:Msg | no (msg.rcvrs & msg.sndr)

    all msg:Msg | no (msg.rcvrs & (Node - Member))

    all msg:Msg | msg in SendingMsg implies some (msg.rcvrs) and some n:Node | msg in n.outbox
    lone SendingMsg
    SendingMsg in (Member - Leader).outbox

    all msg: PendingMsg | no (msg.rcvrs)
    all msg: PendingMsg | msg in msg.sndr.outbox

    all n: Node - Leader | 
    all msg: Msg | msg in n.outbox and msg.sndr = Leader implies n in Member && n in msg.rcvrs

    no (SentMsg & Member.outbox)
    all msg: SentMsg | some msg.rcvrs

    all msg:Msg | msg in PendingMsg or msg in SendingMsg or msg in SentMsg

}

//3.1
check ValidTopology
check ValidMessage

//3.2

