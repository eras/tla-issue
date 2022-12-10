---- MODULE Local --------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC
LOCAL INSTANCE FiniteSets
LOCAL INSTANCE FiniteSetsExt

CONSTANTS
   NumFiles
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   local_files                  (* The files the local knows of *)
   , local_state                (* State of the scanner/transfer *)
   , local_transfers            (* On-going local_transfers *)
   , chan_local_to_remote       (* Channel from local to remote *)
   , chan_remote_to_local       (* Channel from remote to local *)
   , dialog_state               (* Dialog *)
   , chan_local_to_dialog       (* Channel from local to dialog *)

LOCAL INSTANCE Records
LOCAL INSTANCE Messages
LOCAL INSTANCE Channels

Dialog == INSTANCE Dialog

vars == <<local_files, local_state, local_transfers>>

(* Used from Main to express this module does not modify variables *)
UnchangedVars == UNCHANGED vars

----
\* Local information about the remote files
LocalFile == [remote_file : RemoteFile,
              transfer_id : {0} \cup TransferId,
              state       : {"waiting-transfer", (* waiting to be transferred *)
                             "transferring",     (* transferring *)
                             "transferred"}]     (* transferred *)

\* An on-going transfer of a file
Transfer == [ remote_file : RemoteFile,         (* information about the file we're transferring *)
              state       : {"transferring",    (* waiting to be requested from remote *)
                             "finished"},       (* transfer is complete *)
              request_next: FileSize,           (* current size of the local file *)
              blocks_received : FileSize,       (* the number of received blocks *)
              file_id     : FileId ]

\* TypeOK invariants
LocalFilesTypeOK     == local_files \in [FileId -> {<<>>} \cup LocalFile]
LocalStateTypeOK     == local_state \in {"idle", "running", "transferring"}
LocalTransfersTypeOK == local_transfers \in [TransferId -> {<<>>} \cup Transfer]

(* Assert is used to more easily determine which of the TypeOK constraints failed *)
TypeOK ==
  /\ Assert(LocalFilesTypeOK, <<"LocalFilesTypeOK", local_files>>)
  /\ Assert(LocalStateTypeOK, <<"LocalStateTypeOK", local_state>>)
  /\ Assert(LocalTransfersTypeOK, <<"LocalTransfersTypeOK", local_transfers>>)

----
\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

\* Get an index for an empty entry in local_files
FreeFileId == CHOOSE file_id \in FileId: local_files[file_id] = <<>>

\* Unused transfer slots are the empty tuple <<>>; get the set of unused transfer ids
FreeTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] = <<>>}

\* Get the set of active transfer ids
ActiveTransferId == {transfer_id \in TransferId: local_transfers[transfer_id] # <<>>}
----
(* Scanning *)

(* If scanner is idle, start running and send the list_files request to remote *)
ScanStart ==
   /\ local_state = "idle"
   /\ LocalToRemote!Send([ message |-> "list_files" ])
   /\ local_state' = "running"
   /\ RemoteToLocal!UnchangedVars
   /\ Dialog!UnchangedVars
   /\ UNCHANGED<<local_transfers, local_files>>

(* Receive and process list_files-responses from the remote *)
ScanReceive ==
   /\ local_state = "running"
   /\ \E remote_file \in RemoteFile:
      /\ RemoteToLocal!Recv([ message |-> "list_files",
                              file    |-> remote_file ])
      /\ local_files' = [ local_files EXCEPT ![FreeFileId] = [
                             remote_file |-> remote_file,
                             transfer_id |-> 0,
                             state       |-> "waiting-transfer"
                          ]
                        ]
      /\ LocalToRemote!UnchangedVars
      /\ Dialog!UnchangedVars
      /\ UNCHANGED<<local_transfers, local_state>>

(* Receive and process end_list_files-response from the remote *)
ScanFinished ==
   /\ RemoteToLocal!Recv([ message |-> "end_list_files" ])
   /\ LocalToRemote!UnchangedVars
   /\ Dialog!UnchangedVars
   /\ UNCHANGED<<local_state, local_files, local_transfers>>

(* Are there free slots in the local_transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: local_transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If there are local files waiting to be transferred and we have space in the transfer queue,
 * start transferring one such file by adding a new entry to local_transfers *)
TransferStart ==
   /\ \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"
   /\ \E transfer_id \in FreeTransferId:
      LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "waiting-transfer" IN
      LET local_file == local_files[file_id] IN
      /\ local_transfers' = [
            local_transfers EXCEPT ![transfer_id] = [
               remote_file  |-> local_file.remote_file,
               state        |-> "transferring",
               request_next |-> 0,
               blocks_received |-> 0,
               file_id      |-> file_id
            ]
         ]
      /\ local_files' = [local_files EXCEPT ![file_id].transfer_id = transfer_id,
                                            ![file_id].state       = "transferring"]
      /\ RemoteToLocal!UnchangedVars
      /\ Dialog!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state, chans>>

(* If there are pending-request local_transfers and the file is not completely transferred,
 * request one unit of data. If the file is completely transferred, mark the transfer finished. *)
TransferRequest ==
   /\ \E transfer_id \in ActiveTransferId:
         LET transfer == local_transfers[transfer_id] IN
         /\ transfer.state = "transferring"
         /\ transfer.request_next < transfer.remote_file.size
         /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].request_next = @ + 1]
         /\ LocalToRemote!Send([ message |-> "file_block",
                                 name    |-> transfer.remote_file.name,
                                 block   |-> transfer.request_next ])
         /\ RemoteToLocal!UnchangedVars
         /\ Dialog!UnchangedVars
         /\ UNCHANGED<<local_files, local_state>>

(* Receive a block of data from the remote *)
TransferReceive ==
   /\ \E transfer_id \in ActiveTransferId:
      LET transfer == local_transfers[transfer_id] IN
      /\ transfer.state = "transferring"
      /\ IF transfer.blocks_received = transfer.remote_file.size
         THEN /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].state = "finished"]
              /\ RemoteToLocal!UnchangedVars
         ELSE \E block \in BlockId:
                 /\ RemoteToLocal!Recv([ message |-> "file_block",
                                         name    |-> transfer.remote_file.name,
                                         block   |-> block ])
                 /\ local_transfers' = [local_transfers EXCEPT ![transfer_id].blocks_received = @ + 1]
      /\ LocalToRemote!UnchangedVars
      /\ Dialog!UnchangedVars
      /\ UNCHANGED<<local_state, local_files>>

CheckDialogOpenPrime ==
   IF \A file_id \in HasFileId: local_files'[file_id].state = "transferred"
   THEN Dialog!Request
   ELSE Dialog!UnchangedVars

(* If the transfer is finished, release the transfer slot and mark the local file transferred *)
TransferFinished ==
   /\ \E transfer_id \in ActiveTransferId:
      LET transfer == local_transfers[transfer_id] IN
      LET file_id == transfer.file_id IN
      /\ transfer.state = "finished"
      /\ local_transfers' = [local_transfers EXCEPT ![transfer_id] = <<>>]
      /\ local_files' = [local_files EXCEPT ![file_id].transfer_id = 0,
                                            ![file_id].state       = "transferred"]
      /\ CheckDialogOpenPrime
      /\ RemoteToLocal!UnchangedVars
      /\ LocalToRemote!UnchangedVars
      /\ UNCHANGED<<local_state>>

----
\* State description for TLSD
State ==
  LET files_in_state(x) == {local_files[file_id].remote_file.name[2]:
                            file_id \in {file_id \in FileId:
                                         /\ local_files[file_id] # <<>>
                                         /\ local_files[file_id].state = x}} IN
  [ transferred      |-> files_in_state("transferred"),
    waiting_transfer |-> files_in_state("waiting-transfer"),
    transferring     |-> files_in_state("transferring") ]

(* State *)

Next ==
   \/ ScanStart                  (* Start scannning *)
   \/ ScanReceive                (* Receive scan results *)
   \/ ScanFinished               (* Finish scanning *)
   \/ TransferStart              (* Start transfer of one file; acquire transfer slot *)
   \/ TransferRequest            (* Request a block for one file *)
   \/ TransferReceive            (* Receive a block for one file *)
   \/ TransferFinished           (* Clean up a transfer; release transfer slot *)

Init ==
   /\ local_files     = [file_id \in FileId |-> <<>>]
   /\ local_transfers = [transfer_id \in TransferId |-> <<>>]
   /\ local_state     = "idle"

(* Properties *)

Spec ==
   /\ Init
   /\ [][Next]_vars
   /\ WF_vars(Next)

================================================================================
