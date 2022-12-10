---- MODULE Messages -----------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

CONSTANTS
   NumFiles                 \* Needed for Records
   , MaxFileSize            \* Needed for Records
   , MaxConcurrentTransfers \* Needed for Records

LOCAL INSTANCE Records

(* Request a list of files from the remote *)
RequestListFiles ==
  [ message: {"list_files"} ]

(* Respond with one file, or the indication of the end of list *)
RespondListFiles ==
   UNION({
      [ message : {"list_files"},
        file    : RemoteFile ],
      [ message : {"end_list_files"} ]
   })

(* Request one block of a named file *)
RequestFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

(* Respond one block of a named file *)
RespondFileBlock ==
   [ message: {"file_block"},
     name   : FileName,
     block  : BlockId ]

(* Request a dialog to be shown *)
RequestDialog ==
   [ message : {"request_dialog"} ]

(* All messages from local to remote *)
MsgLocalToRemote ==
  UNION({
     RequestListFiles,
     RequestFileBlock
  })

(* All messages from remote to local *)
MsgRemoteToLocal ==
   UNION({
      RespondListFiles,
      RespondFileBlock
   })

MsgLocalToDialog ==
   UNION({
      RequestDialog
   })

================================================================================
