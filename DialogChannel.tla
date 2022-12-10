---- MODULE DialogChannel ------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
CONSTANTS
   NumFiles                 \* Needed for Messages
   , MaxFileSize            \* Needed for Messages
   , MaxConcurrentTransfers \* Needed for Messages

VARIABLES
   chan_local_to_dialog         (* Channel from local to dialog *)

LOCAL INSTANCE Messages

LocalToDialog == INSTANCE Channel WITH channel <- chan_local_to_dialog, Data <- MsgLocalToDialog

================================================================================
