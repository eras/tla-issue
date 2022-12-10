------------------------------ MODULE Channel -------------------------------

(* Channel is an asynchronous channel between with a buffer of at most
   one message.

   The state is stored in the channel function. Channels maps via Id to the
   actual channel.

   Copyright 2022 Erkki Seppälä <erkki.seppala@vincit.fi>
*)

----------------------------------------------------------------------------
LOCAL INSTANCE TLC              (* Assert *)

CONSTANT Data                   (* Data constrains the kind of messages this module processes*)

VARIABLE channel                (* Channel *)

UnchangedVars == UNCHANGED channel

(* When a channel is not busy, it has this value. *)
Null == <<>>

ASSUME Null \notin Data

Channel == Data \cup {Null}

TypeOK == channel \in Channel

Busy ==
   channel # Null

Send(data) ==
   /\ Assert(data \in Data, <<"Sending invalid data", data, "while expecting", Data>>)
   /\ \lnot Busy
   /\ channel' = data

Recv(data) ==
   /\ Assert(data \in Data, <<"Receiving invalid data", data, "while expecting", Data>>)
   /\ Busy
   /\ data = channel
   /\ channel' = Null

Sending ==
   IF Busy
   THEN {channel}
   ELSE {}

Init ==
   channel = Null

=============================================================================
