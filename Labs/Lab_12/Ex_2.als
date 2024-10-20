enum status {R, W, F, IO}

one sig Processor{}

sig Thread{
    var flag: status
    }

var sig Busy in Processor{}

pred r [t:Thread]{t.flag = R}
pred w [t:Thread]{t.flag = W}
pred f [t:Thread]{t.flag = F}
pred io [t:Thread]{t.flag = IO}

pred busy[]{some Busy}

fact{
    always(not busy iff (no t : Thread | r[t]))
    always (lone t:Thread | r[t])
    always(
            not busy[] and (some t: Thread | w[t])
            implies
            after busy[]
    )
    always(
            all t: Thread | f[t]
            implies
            once r[t]
    )
    all t:Thread | always(eventually(not r[t]))
    all t:Thread | always(not f[t] 
                        implies
                        eventually r[t]
                    )
    all t:Thread | always( f[t] implies always f[t])
}

fact{
    not busy[]
    all t:Thread | w[t]
}

run {
    eventually busy[]
} for 2 Thread 