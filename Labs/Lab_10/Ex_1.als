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
}

fact{
    system[]
    //init[] && some p1,p2: Profile | connect[p1,p2]
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



run{
    eventually some connections
    eventually some dblocks
    } for 5 but 3 steps