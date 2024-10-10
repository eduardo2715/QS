sig User{
    profs:set Profile
}

sig Profile{
    connections:set Profile,
    dblocks:set Profile,
    iblocks:set Profile
}

fact{
    all u:User, p1,p2:Profile | 
        (p1 + p2) in u.profs
        implies 
        p1 ! in p2.connections
}

fact{
    no(((~profs).profs) //relation that associates each profile with the profiles of the same user
    & 
    connections)
}

fact{
    connections = ~connections
}

fact{
    all p:Profile | one p.(~profs)
}

fact{
   no((~profs.profs) & dblocks)
}

fact{
    //all p1, p2 :Profile | (p1 in p2.dblocks) implies (p2 !in p1.dblocks)
    no(dblocks & ~dblocks)
}

fact{
    //all p1,p2:Profile | (p2 in p1.dblocks) implies (p2 !in p1.connections)
    no(dblocks & connections)
}

fact{
    iblocks = dblocks.(~profs).profs - dblocks
}

fun frenimies[u1:User]:set User{
        {u2 : User | 
    (some p2,p3:Profile | 
        p3 in p2.connections 
        && p2 in u1.profs
        && p3 in u2.profs)
    &&
    (some p1, p4:Profile|
        p1 in u1.profs
        && p4 in u2.profs
        && p1 in p4.dblocks)}
        
    /* (profs.(~dblocks).(~profs)
    &
    profs.connections.(~profs)) */
}

assert a1{
    all p1,p2:Profile |
    p1 in p2.iblocks implies p2 !in p1.iblocks
}

check a1 for 4

run{#Profile = 5 && #User = 2} for 6

