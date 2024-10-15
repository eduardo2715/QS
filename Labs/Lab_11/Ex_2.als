enum Liveness {Dead, Alive, Unborn}


sig Person{
    var spouse:lone Person,
    var children: set Person,
    var liveness: Liveness
}

pred init[]{
    no spouse
    no children
    Person.liveness = Alive + Unborn
}
pred stutter[]{
    spouse' = spouse
    children' = children
    liveness' = liveness
}

pred trans[]{
    stutter[]
    or
    some p:Person | die[p]
    or
    some p1,p2,p3:Person | beBorn[p1, p2, p3]
    or
    some p1,p2:Person | marry[p1, p2]

}

pred system[]{
    init[] and always trans[]
}

pred die[p:Person]{
    //pre
    p.liveness = Alive
    //pos
    liveness' = liveness - p->Alive + p->Dead
    //frame
    spouse' = spouse
    children' = children
}

pred beBorn[p1:Person, p2:Person, p3:Person]{
    //pre
    (p1 + p2).liveness = Alive
    p3.liveness = Unborn
    p1 != p2
    //post
    children' = children + (p1->p3) + (p2->p3)
    liveness' = liveness - (p3->Unborn) + (p3->Alive)
    //frame
    spouse' = spouse
}

pred marry[p1:Person, p2:Person]{
    //pre
    (p1 + p2).liveness = Alive
    no(p1.spouse) and no(p2.spouse)
    p1 != p2
    //post
    spouse' = spouse + (p1->p2) + (p2->p1)
    //frame
    children' = children
    liveness' = liveness
}


pred fairness[] {
   some p:Person | 
   (eventually always p.liveness = Alive)
   implies
   (always eventually die[p])
}




pred trace1[]{
    eventually some p:Person | die[p]
}

pred trace2[]{
    eventually some p1, p2, p3:Person | beBorn[p1, p2, p3]
}

pred trace3[]{
    eventually some p1, p2:Person | marry[p1, p2]
}


fact{system[]}

run {trace3[]} for 5
 