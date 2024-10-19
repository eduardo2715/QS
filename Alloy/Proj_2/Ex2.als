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
    m.*(~(m.qnxt))
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
}



pred memberAplication[m: Member, n: Node] {
    some n2: Node | memberAplicationAux[m, n, n2]
}

pred memberAplicationAux[m: Member, n1: Node, n2:Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt                   // n1 should not already point to n2 in m's queue
    n1 != n2                                // n1 and n2 must be different (no self-pointing)
    n1 in Node - Member
    n2 in MemberqueueElements[m]
    all n3: Node | ((n2 -> n3) !in m.qnxt) //n2 is the last in the queue

    // Postconditions
    m.qnxt' = (n2 -> n1) + m.qnxt

    // Frame conditions
    lnxt' = lnxt
    nxt' = nxt

}

pred memberPromotion[m:Member, n:Node]{
    //Preconditions
    (m -> n) in m.qnxt //the node is the first in line to become member
    n in Node - Member //node isnt a member
    n in MemberqueueElements[m] //node is in the queue

    //Postconditions
    n' in Member //node becomes a member
    m.nxt' = n // member now points to newly appointed node
    n.nxt' = m.nxt //newly apointed node points to where member used to point
    lone n2: Node | (n -> n2) in m.qnxt implies  m.qnxt' = m.qnxt - (m -> n) - (n -> n2) + (m ->  n2)
    // updated meber queue so that node that was before newly appointed node now points to leader

    //Frame conditions
    lnxt' = lnxt
}   

pred memberExit[m:Member]{
    //Preconditons
    m not in Leader //member isnt the leader
    one l:Leader | m not in LeaderqueueElements[l] // member not in the leaderqueuelements
    no (Node & MemberqueueElements[m]) //member has no nodes in its queue
    no m.outbox //all its messages are sent

    //Postconditions
    m' not in Member //no longer a member
    (m.~nxt).nxt' = m.nxt //close the loop

    //Frame conditions
    lnxt' = lnxt
    qnxt' = qnxt

}

pred nonMemberExit[n:Node]{
    //Preconditions
    n not in Member //node isnt a member
    some m: Member | n in MemberqueueElements[m]

    //Postconditions
    some m: Member | n in MemberqueueElements[m] implies n' not in MemberqueueElements[m'] && 
    some n2: Node | lone n3: Node | (n2 ->n ) in m.qnxt && (n -> n3) in m.qnxt &&
    m.qnxt' = m.qnxt -  (n2 -> n) - (n -> n3) + (n2 -> n3)

}

pred trans[] {
    stutter[]
    or
    (some n1, n2: Node | memberAplication[n1, n2])
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

pred trace1[]{
    eventually some m, n2:Node | memberAplication[m, n2] 
    eventually #(Member.qnxt) > 1
    #Node >= 5
    #Leader = 1
    // eventually some m: Member, n: Node | memberPromotion[m,n]
    // eventually some n: Node | nonMemberExit[n]
    // eventually some m: Member | memberExit[m]

}

run {
    trace1[]
} for 6





/* pred addlnxt[l: Leader, m1: Member, m2: Member] {
    // Preconditions
    (m1 -> m2) !in l.lnxt                       // m1 should not already point to m2 in l's queue
    m1 in (Member - Leader)                     // m1 must be a non leader member
    (m2 in (Member - Leader)) or (m2 = l)       // m2 can either be another non member or the leader
    m1 != m2                                    // m1 and m2 must be different (no self-pointing)

    // Postconditions
    l.lnxt' = l.lnxt + (m1 -> m2)

    // Frame conditions
    all l1: Leader - l | l1.lnxt' = l1.lnxt 
} */

/* pred addqnxt[m: Member, n1: Node, n2: Node] {
    // Preconditions
    (n1 -> n2) !in m.qnxt                   // n1 should not already point to n2 in m's queue
    n1 != n2                                // n1 and n2 must be different (no self-pointing)
    n1 in (Node - Member)                   // n1 must be a non-member
    (n2 in (Node - Member)) or (n2 = m)     // n2 can either be another non-member or the member                         

    // Postconditions
    m.qnxt' = m.qnxt + (n1 -> n2)

    // Frame conditions
    all m1: Member - m | m1.qnxt' = m1.qnxt
} */




//acoes 

//membership apllication

/* pred memberAplication[m: Member, n: Node] {
    some n2: Node memberAplicationAux[m, n, n2]
} */

/* pred memberAplicationAux[m: Member, n1: Node, n2:Node] {
    // Preconditions
    //n2 is the last node in the queue

    // Postconditions
    m.qnxt' = (n1 -> n2) + m.qnxt

    // Frame conditions

} */

//membership promoion
//lider apllication
//lider promotion
