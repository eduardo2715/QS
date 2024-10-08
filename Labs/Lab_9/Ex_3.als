sig User{
    profs:set Profile
}

sig Profile{
    connections:set Profile
}

fact{
    all u:User, p1,p2:Profile | 
        (p1 + p2) in u.profs
        implies 
        p1 ! in p2.connections
}

fact{
    no(((~profs).profs)
    & 
    connections)
}

fact{
    connections = ~connections
}

fact{
    all p:Profile | one p.(~profs)
}




run{#Profile = 5 && #User = 2} for 6

