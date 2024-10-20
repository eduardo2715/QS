one sig Button {}

var sig Pressed in Button {}

one sig Clock {}

var sig Stopped in Clock {}

var sig Zero in Clock {}

pred r {no Stopped}

pred z {some Zero}

pred p { some Pressed}

fact {
    always ((p and (after (not p))) iff (r and (after (not r)) or ((not r) and (after r))))
}

fact {
    z
    and 
    not r 
}

fact{
    always (
        (p and (after p) and (after(after not p)))
        iff // if and only if , A implies B and B implies A
        (after(after z))
    )
}

fact{
    (always (not r) and z) implies (after z)
}

fact{
    always(eventually z)
}

fact{
    always(eventually (not p))
}

run {
    eventually (r and eventually (not r))
    and 
    after(after(eventually z))
}

