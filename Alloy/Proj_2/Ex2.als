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
    //TODO n2 is the last node in the queue
    (n1 -> n2) !in m.qnxt                   // n1 should not already point to n2 in m's queue
    n1 != n2                                // n1 and n2 must be different (no self-pointing)
    n1 in Node - Member
    n2 in MemberqueueElements[m]

    // Postconditions
    m.qnxt' = (n1 -> n2) + m.qnxt

    // Frame conditions
    lnxt' = lnxt
    nxt' = nxt

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
    eventually some n1, n2:Node | memberAplication[n1, n2]
    eventually #(Member.qnxt) > 1
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
