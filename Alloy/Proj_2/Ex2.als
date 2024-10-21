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

pred init[]{
    all n:Node | n.outbox = PendingMsg
    no qnxt
    no lnxt
    Member = Leader
    Msg = PendingMsg
}

pred stutter[]{
    qnxt' = qnxt
    lnxt' = lnxt
    nxt' = nxt
    Member' = Member
    Leader' = Leader
    Msg' = Msg
    LQueue' = LQueue
}

pred stutterMessage[]{
    Msg' = Msg
    rcvrs' = rcvrs
    sndr' = sndr
    outbox' = outbox
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

    // If the queue is empty, n2 should be the member itself (n1 will point to the member)
    #MemberqueueElements[m] = 0 implies n2 = m
    // If the queue is not empty, n2 must be the last node in the queue
    #MemberqueueElements[m] > 0 implies {
        n2 in MemberqueueElements[m]          // n2 is a node in the queue
        no n0: Node | (n0 -> n2) in m.qnxt    // n2 should not point to any other node (last in the queue)
    }

    // Postconditions
    m.qnxt' = (n1 -> n2) + m.qnxt             // Add the new connection (n1 -> n2)
    all m2 : Member' - m | m2.qnxt' = m2.qnxt
    //some n: Node | n != m && n in MemberqueueElements[m] implies (n -> m) in m.qnxt'
    // Frame conditions
    stutterLeader[]
    stutterMessage[]
    stutterRing[]
}



pred memberPromotion[m:Member, n:Node]{
    //Preconditions
    (n -> m) in m.qnxt //the node is the first in line to become member
    n in Node - Member //node isnt a member
    n in MemberqueueElements[m] //node is in the queue


    //Postconditions
    nxt' = nxt - (m->m.nxt) + (m->n) + (n->m.nxt) // member now points to newly appointed node
    // (some n.(m.qnxt)) implies (m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (~(m.qnxt)[n] -> n) + (~(m.qnxt)[n] -> n.(m.qnxt)))
    // no(n.(m.qnxt)) implies m.qnxt' = m.qnxt - (~(m.qnxt)[n] -> n)
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (~(m.qnxt)[n] -> n) + (~(m.qnxt)[n] -> n.(m.qnxt))
    Member' = Member + n //node becomes a member

    //Frame conditions
    all m2 : Member' - m | m2.qnxt' = m2.qnxt
stutterMessage[]
   stutterLeader[] 
}

pred memberExit[m:Member]{ //not working properly
    //Preconditons
    m not in Leader //member isnt the leader
    one l:Leader | m not in LeaderqueueElements[l] // member not in the leaderqueuelements
    no (m.qnxt) //member has no nodes in its queue
    no m.outbox //all its messages are sent
    one (m.~nxt) //member is part of the ring

    //Postconditions

    Member' = Member - m
    nxt' = nxt - ((m.~nxt) -> m) - (m -> m.nxt) + ((m.~nxt) -> m.nxt)

    //Frame conditions
    qnxt' = qnxt
    lnxt' = lnxt
    Leader' = Leader
    Msg' = Msg

}

pred nonMemberExit[m: Member, n: Node] { //currenty only removing the last member from the queue (?)
    // Preconditions
    n not in Member                        // n isn't a member
    n in MemberqueueElements[m]            // n is in m's queue

    //Postconditions
    //some m: Member | n in MemberqueueElements[m] implies n' not in MemberqueueElements[m'] && 
    m.qnxt' = m.qnxt - (n -> n.(m.qnxt)) - (~(m.qnxt)[n] -> n) + (~(m.qnxt)[n] -> n.(m.qnxt))

    // Frame conditions
    lnxt' = lnxt
    nxt' = nxt
    Member' = Member
    Leader' = Leader
    Msg' = Msg
}

pred leaderApplication[l: Leader, m: Member] {
    some m2: Member | leaderApplicationAux[l, m, m2]
}

pred leaderApplicationAux[l: Leader, m1: Member, m2: Member] {
    // Preconditions
    (m1 -> m2) !in l.lnxt                   // n1 should not already point to n2 in l's queue
    m1 != m2                                // n1 and n2 must be different (no self-pointing)
    m1 in Member - Leader                     // n1 must not already be a Leader
    m1 not in LeaderqueueElements[l]         // n1 should not already be in the member's queue
    // If the queue is empty, n2 should be the member itself (n1 will point to the member)
    #LeaderqueueElements[l] = 0 implies m2 = l
    // If the queue is not empty, n2 must be the last node in the queue
    #LeaderqueueElements[l] > 0 implies {
        m2 in LeaderqueueElements[l]          // n2 is a node in the queue
        no m0: Member | (m0 -> m2) in l.lnxt    // n2 should not point to any other node (last in the queue)
    }

    // Postconditions
    l.lnxt' = (m1 -> m2) + l.lnxt             // Add the new connection (n1 -> n2)

    // Frame conditions
    stutterRing[]
    stutterMember[]
    stutterMessage[]
}

pred leaderPromotion[l:Leader, m:Member]{
    //Preconditions
    (m -> l) in l.lnxt //the node is the first in line to become member
    m in Member - Leader //node isnt a member
    m in LeaderqueueElements[l] //node is in the queue
    no MemberqueueElements[l]
    no l.outbox

    //Postconditions
    m.lnxt' = l.lnxt - (m->l)
    Leader' = m //node becomes a member

    //Frame conditions
    stutterRing[]
    stutterMember[]
    stutterMessage[]
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
}

pred system[]{
    init[]
    and
    always trans[]
}

fun VisualizeMemberQueues[]: Node -> lone Node {
    Member.qnxt
}

fun VisualizeLeaderQueues[]: Node -> lone Node {
    Leader.lnxt
}

fact{
    system[]
}

pred trace1[] {
    #Leader = 1
    some l: Leader |
    eventually (#LeaderqueueElements[l] = 2 and (
         eventually #LeaderqueueElements[l] = 1
    )
    )
}



run {
    trace1[]
} for 5


/* pred trace2[]{
    eventually( #Member = 3
    and 
    some m :Member | (eventually memberExit[m]))
}
run {
    trace2[]
} for 5 */

/* pred trace3[]{

    some m1:Member, n1, n2, n3:Node | 
    m1 != n1
    and
    n1!=n2 and n1!=n3 and n2!=n3
    and
    eventually (memberApplication[m1, n1]
    and
    eventually (memberApplication[m1, n2]
    and
    eventually (memberPromotion[m1, n1]
    and
    eventually memberApplication[n1, n3])))
    
}
run{
    trace3[]
}for 5 */

/* pred trace4[]{
    #Leader = 1
    and
    eventually (#Member > 1
    and
    some m1,m2:Member | 
    m1 != m2
    and
    eventually (#MemberqueueElements[m1] > 0
    and 
    eventually #MemberqueueElements[m2] > 0)
    )
}
run{
    trace4[]
}for 5 */

//TESTING
fact OneQueuePerNode{
    all m: Member | #((m.qnxt)).m <= 1
    all l: Leader | #((l.lnxt)).l <= 1
}



pred trace5[]{
    #Leader = 1
    and
    eventually (#Member > 2
    and
    some l:Leader, m1/* , m2 */:Member - Leader | 
/*     m1!=m2
    and */
    eventually (leaderApplication[l,m1]
    and 
    eventually leaderPromotion[l,m1])
    )
}
run{
    trace5[]
}for 5