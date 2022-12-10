---- MODULE Channels -----------------------------------------------------------
(* Lists all channels of the system: one from local to remote and one back *)
--------------------------------------------------------------------------------
CONSTANTS
   NumFiles                 \* Needed for Messages
   , MaxFileSize            \* Needed for Messages
   , MaxConcurrentTransfers \* Needed for Messages

VARIABLES
   chan_local_to_remote      (* Channel from local to remote *)
 , chan_remote_to_local      (* Channel from remote to local *)
 , chan_local_to_dialog      (* Channel from local to dialog *)

LOCAL INSTANCE Messages

INSTANCE DialogChannel          (* LocalToDialog *)

chans == <<chan_local_to_remote, chan_remote_to_local, chan_local_to_dialog>>

LocalToRemote == INSTANCE Channel WITH channel <- chan_local_to_remote, Data <- MsgLocalToRemote
RemoteToLocal == INSTANCE Channel WITH channel <- chan_remote_to_local, Data <- MsgRemoteToLocal

(* These are named in a way that they don't conflict other operators, so this module can
 * be INSTANCEd directly to other modules. *)

(* Are all the channels empty? *)
QuiescentChannels ==
   /\ ~LocalToRemote!Busy
   /\ ~LocalToDialog!Busy
   /\ ~RemoteToLocal!Busy

UnchangedVarsChannels ==
   /\ LocalToRemote!UnchangedVars
   /\ LocalToDialog!UnchangedVars
   /\ RemoteToLocal!UnchangedVars

InitChannels ==
   /\ LocalToRemote!Init
   /\ RemoteToLocal!Init
   /\ LocalToDialog!Init

================================================================================
