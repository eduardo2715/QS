sig Person{
    father: lone Person,
    mother: lone Person,
    siblings: set Person
}

sig Married in Person{
    spouse: Married
}

//siblings

fact{
    //all p1,p2 : Person | p1 in p2.siblings implies (p1.father = p2.father || p1.mother = p2.mother)
    siblings = (father + mother).~(father + mother) - iden
}

fact{
    spouse = ~spouse
}

fact{
    //all p:Person |p !in p.^(father + mother)
    no(^(father + mother) & iden)
}

fun bloodRelative[p1:Person] : set Person{
    { 
        p2: Person |  some (ancestors[p1] & ancestors[p2])
    }
}

fun ancestors[p:Person]:set Person{
    p.*(father + mother) 
}

fact{
    all p:Person | some p.spouse implies p.spouse !in bloodRelative[p]
}

fun coparents[p:Person]:set Person{
    p.~(father + mother).(father + mother) - p
}

fact{
    all p:Person | no(bloodRelative[p] & coparents[p])
}

assert a1{
    all p1, p2:Person | p1 = p2.father implies p1 !in p2.siblings
}

check a1 for 5

run {#Person >=  4 && #Married >= 2 && #siblings >= 2} for 5
