sig User{
    profs:set Profile
}

sig Profile{
    var connections:set Profile,
    var dblocks:set Profile,
    var iblocks:set Profile
}

pred init[]{
    all p :Profile | one p.(~profs)
    no connections
    no dblocks
    no iblocks
}

pred stutter[]{
    connections' = connections
    dblocks' = dblocks
    iblocks' = iblocks
}

pred system[]{
    init[]
    always trans[]
}

pred trans[]{
    stutter[]
    or 
    (some p1,p2 : Profile | connect[p1, p2])
    or
    (some p1,p2 : Profile | block[p1, p2])
    or
    (some p1,p2 : Profile | disconnect[p1, p2])
    or
    (some p1,p2 : Profile | unblock[p1, p2])
}

fact{
    system[]
}

pred connect[p1:Profile, p2:Profile]{
    //preconditions
    //p1 and p2 belong to distinct users
    p1.(~profs) != p2.(~profs)
    //p1 doesnt block p2 and p2 doesnt block p1
    p1 !in p2.dblocks and p2 !in p1.dblocks
    //p1 is not connected to p2
    p2 !in p1.connections

    //postconditions
    connections' = connections + (p1->p2) + (p2->p1)

    //frame conditins
    dblocks' = dblocks
    iblocks' = iblocks
}

pred block[p1:Profile, p2:Profile]{
    //preconditions
    //p2 cannot block p1
    p1 !in p2.dblocks
    //p1 cannot block p2
    p2 !in p1.dblocks
    //p1 and p2 cannot belong to the same user
    p1.(~profs) != p2.(~profs)
    //p1 and p2 cannot be connected
    p1 !in p2.connections

    //postconditions
    dblocks' = dblocks + (p1->p2)
    iblocks' = dblocks'.(~profs').profs' - dblocks'

    //frame conditins
    connections' = connections
}

pred disconnect[p1:Profile, p2:Profile]{
    //pre
    p2 in p1.connections
    //post
    connections' = connections - p1 -> p2 + p2 -> p1
    //frame
    iblocks' = iblocks
    dblocks' = dblocks
}

pred unblock[p1:Profile, p2:Profile]{
    //pre
    p2 in p1.dblocks
    //post
    dblocks' = dblocks - (p1 -> p2)
    iblocks' = dblocks'.(~profs'.profs') - dblocks'
    //frame
    connections' = connections
}


assert a1 {
    always all p1,p2:Profile | p2 in p1.connections implies p1.~profs != p2.~profs
}

check a1 for 5

assert simetricConnetions {
    always connections = ~connections
}

check simetricConnetions for 5




pred trace1[]{
    eventually some p1, p2:Profile | disconnect[p1, p2]
    eventually some p1, p2:Profile | unblock[p1, p2]
}

run{ 
    trace1[] 
    } for 5 but 3 steps



//safetyProperty
// always p

//livenessProperty
// fairness[] implies envetually p