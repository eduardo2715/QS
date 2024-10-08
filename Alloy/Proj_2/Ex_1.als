sig  Node  {}

sig  Member  in  Node  {
    nxt:  lone  Member,
    qnxt  :  Node  ->  lone  Node,
    outbox:  set  Msg
}

one  sig  Leader  in  Member  {
    lnxt:  Node  ->  lone  Node
}

sig  LQueue  in  Member  {}

abstract  sig  Msg  {
    sndr:  Node,
    rcvrs:  set  Node
}

sig  SentMsg,  SendingMsg,  PendingMsg  extends  Msg  {}

