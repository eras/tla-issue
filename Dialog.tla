---- MODULE Dialog -------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANTS
   NumFiles                 \* Needed for DialogChannel
   , MaxFileSize            \* Needed for DialogChannel
   , MaxConcurrentTransfers \* Needed for DialogChannel

VARIABLES
   dialog_state                 (* state of the dialog *)
   , chan_local_to_dialog       (* channel to request dialog to be opened *)

vars == <<dialog_state, chan_local_to_dialog>>

LOCAL INSTANCE Messages
LOCAL INSTANCE DialogChannel

(* Used from Main to express this module does not modify variables *)
UnchangedVars == UNCHANGED vars

(* Startup state: dialog is closed *)
Init ==
   /\ dialog_state = "closed"
   (* chan_local_to_dialog initial value is set via Channels!Init *)

(* If a dialog is requested, open a dialog *)
Open ==
   /\ dialog_state = "closed"
   /\ LocalToDialog!Recv([ message |-> "request_dialog"])
   /\ dialog_state' = "open"

(* Reset the dialog request and set it to accepted state if user acknowledges the dialog *)
Accept ==
   /\ dialog_state = "open"
   /\ dialog_state' = "accepted"
   /\ UNCHANGED<<chan_local_to_dialog>>

(* Close accepted dialogs *)
Close ==
   /\ dialog_state = "accepted"
   /\ dialog_state' = "closed"
   /\ UNCHANGED<<chan_local_to_dialog>>

(* A request to open the dialog; this is used by other modules, not by the Next action *)
Request ==
   /\ LocalToDialog!Send([ message |-> "request_dialog"])
   /\ UNCHANGED<<dialog_state>>

Next ==
   \/ Open
   \/ Accept
   \/ Close

(* Quiescent: none of the Next actions can be taken *)
Quiescent == ~ENABLED Next

(* For tlsd *)
State ==
  [ state |-> dialog_state ]

================================================================================
