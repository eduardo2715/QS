sig Name, Addr{}

sig Book{
    var addr: Name->lone Addr,
}

pred init[]{
    no Book.addr
}

pred addAddr[b:Book, n:Name, a:Addr]{
    //pre-condition
    (n -> a) !in b.addr
    //post-condition
    b.addr' = b.addr + (n->a)
    //frame conditions
    all b1 : Book - b | b1.addr' = b1.addr
}

pred removeAddrAux[b:Book, n:Name, a:Addr]{
    //pre-condition
    (n -> a) in b.addr
    //post-condition
    b.addr' = b.addr - (n->a)
    //frame conditions
    all b1 : Book - b | b1.addr' = b1.addr
}

pred removeAddr[b:Book, n:Name]{
    some a:Addr | removeAddrAux[b, n, a]
}

pred stutter[]{
    addr' = addr
}

pred trans[]{
    (some b:Book, n:Name, a:Addr | addAddr[b, n, a])
    or 
    (some b:Book, n:Name | removeAddr[b, n])
    or
    (stutter[])
}

pred system[]{
    init[]
    and
    always trans[]
}

fact{
    system[]
}

fun VisualizeAddr[]:Name->lone Addr{
    Book.addr
}

run{eventually some addr} for 5 steps