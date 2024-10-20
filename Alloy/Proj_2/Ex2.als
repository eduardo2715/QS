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
}

pred memberAplication[m: Member, n: Node] {
    some n2: Node | memberAplicationAux[m, n, n2]
}

pred memberAplicationAux[m: Member, n1: Node, n2: Node] {
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

    // Frame conditions
    lnxt' = lnxt
    nxt' = nxt
    Member' = Member
    Leader' = Leader
    Msg' = Msg
}



pred memberPromotion[m:Member, n:Node]{ //curruntly works for members with a single queue element
    //Preconditions
    (n -> m) in m.qnxt //the node is the first in line to become member
    n in Node - Member //node isnt a member
    n in MemberqueueElements[m] //node is in the queue

    //Postconditions
    nxt' = nxt - (m->m.nxt) + (m->n) + (n->m.nxt) // member now points to newly appointed node
    //lone n2: Node | (n -> n2) in m.qnxt implies  m.qnxt' = m.qnxt - (m -> n) - (n -> n2) + (m ->  n2)
    // updated meber queue so that node that was before newly appointed node now points to leader

    //Frame conditions
    lnxt' = lnxt
    Leader' = Leader
    Member' = Member + n
    Msg' = Msg
}

fun PB[m:Member, n:Node]:some Node{
    n.(m.qnxt)
}
fun PA[m:Member, n:Node]:some Node{
    ~(m.qnxt)[n]
}


pred memberExit[m:Member]{ //not working properly
    //Preconditons
    m not in Leader //member isnt the leader
    one l:Leader | m not in LeaderqueueElements[l] // member not in the leaderqueuelements
    no (m.qnxt) //member has no nodes in its queue
    no m.outbox //all its messages are sent
    one (m.~nxt) //member is part of the ring

    //Postconditions

    nxt' = nxt - ((m.~nxt) -> m) - (m -> m.nxt) + ((m.~nxt) -> m.nxt)

    //Frame conditions
    qnxt' = qnxt
    lnxt' = lnxt
    Member' = Member
    Leader' = Leader
    Msg' = Msg

}

pred nonMemberExit[m: Member, n: Node] { //currenty only removing the last member from the queue
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


pred trans[] {
    stutter[]
    or
    (some n1, n2: Node | memberAplication[n1, n2])
    or
    (some m: Member, n: Node | memberPromotion[m, n])
    or
    (some m: Member, n: Node | nonMemberExit[m ,n])
    or
    (some m: Member | memberExit[m])
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

/* pred trace1[]{
    some m, n1:Node |
    (eventually memberAplication[m, n1]
    and 
    eventually memberPromotion[m, n1]
    and
    eventually nonMemberExit[m, n1]
    )

    #Node >= 5
    #Leader = 1
}
run {
    trace1[]
} for 5 */

pred trace2[]{
    some m, n1, n2, n3:Node |
    n1!=n2 and n1!=n3 and n2!=n3
    and
    eventually memberAplication[m, n1]
    and 
    eventually memberAplication[m, n2]
    and
    eventually memberAplication[m, n3]
    and
    eventually nonMemberExit[m, n1]
}

run {
    trace2[]
} for 5

//TODO Fix memberExit[m]
/* pred trace3[]{
    eventually( #Member = 3
    and 
    some m :Member | (eventually memberExit[m]))
}
run {
    trace3[]
} for 5 */
