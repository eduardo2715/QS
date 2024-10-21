sig  Node  {}

var  sig  Member  in  Node  {}

var  one  sig  Leader  in  Member  {}

var  sig  LQueue  in  Member  {}

sig  Msg  {
sndr:  Node,
var  rcvrs:  set  Node
}

var  sig  SentMsg,  SendingMsg,  PendingMsg  in  Msg  {}

//Sent messages are those that have been received by someone (safety)

fact {
    always 
        all msg:SentMsg |
        some msg.rcvrs   
}

//All nodes will be the leader at some point;

fact{
    all n:Node | eventually n = Leader
}

//If a node still has messages to send, then it will be the leader at some point in the future;

fact{
    all n:Node | 
        always (
            some (n.(~sndr) & PendingMsg) 
                implies 
                    (eventually n = Leader))
}

//Once a message is sent, it never changes state again;

fact{
    all msg:Msg | always (
            msg in SentMsg 
                implies 
                    always msg in SentMsg)
}
