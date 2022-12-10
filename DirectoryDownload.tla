---- MODULE DirectoryDownload --------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------

LOCAL INSTANCE Naturals
LOCAL INSTANCE TLC

CONSTANTS
   NumFiles
   , MaxFileSize
   , MaxConcurrentTransfers

VARIABLES
   remote_files                 (* The files the remote has *)
   , local_files                (* The files the local knows of *)
   , scanner_state              (* State of the scanner *)
   , transfers                  (* On-going transfers *)

vars == <<remote_files, local_files, scanner_state, transfers>>

FileId == (1..NumFiles)

TransferId == (1..MaxConcurrentTransfers)

\* Unused transfer slots are the empty tuple <<>>
FreeTransferId == {transfer_id \in TransferId: transfers[transfer_id] = <<>>}
ActiveTransferId == {transfer_id \in TransferId: transfers[transfer_id] # <<>>}

FileName == {"filename"} \X (1..NumFiles)
FileSize == (0..MaxFileSize)

\* A file in the remote service is described by this
RemoteFile == [name: FileName,
             size: FileSize]

\* Local information about the remote files
LocalFile == [remote_file   : RemoteFile,
              transfer_id : {0} \cup TransferId,
              state       : {"ignore", "waiting-transfer", "transferring", "transferred"}]

\* An on-going transfer of a file
Transfer == [remote_file  : RemoteFile,
             state      : {"active", "transfer", "finished"},
             local_size : FileSize,
             file_id    : FileId]

----
\* TypeOK invariants
RemoteFileTypeOK     ==
  /\ \A remote_file \in remote_files: remote_file \in RemoteFile
  /\ ~ \E remote_file1 \in remote_files:
     \E remote_file2 \in remote_files:
     /\ remote_file1.name = remote_file2.name
     /\ remote_file1.size # remote_file2.size
LocalFileTypeOK    == local_files \in [FileId -> {<<>>} \cup LocalFile]
ScannerStateTypeOK == scanner_state \in {"idle", "scanning", "scanned"}
TransfersTypeOK    == transfers \in [TransferId -> {<<>>} \cup Transfer]

TypeOK ==
  /\ RemoteFileTypeOK
  /\ LocalFileTypeOK
  /\ ScannerStateTypeOK
  /\ TransfersTypeOK

----
\* Generate uniquely named file of different names and varying sizes
RECURSIVE GenerateFiles(_)
GenerateFiles(files) ==
  IF \E file \in RemoteFile: file.name \notin {file2.name: file2 \in files}
  THEN LET file == CHOOSE file \in RemoteFile:
                   /\ file.name \notin {file2.name: file2 \in files}
                   /\ \lnot \E file2 \in files: file.size <= file2.size
       IN GenerateFiles({file} \union files)
  ELSE files

\* Set of files we are locally aware of
HasFileId == {file_id \in FileId: local_files[file_id] # <<>>}

\* Set of file names we are locally aware of
LocalFileNames == {local_files[file_id].remote_file.name: file_id \in HasFileId}

\* Are we locally aware of this file in the remote?
FoundLocally(remote_file) == \E local_file_name \in LocalFileNames: remote_file.name = local_file_name

----
(* Scanning *)

(* If scanner is idle, start scanning *)
ScanStart ==
  /\ scanner_state = "idle"
  /\ scanner_state' = "scanning"
  /\ UNCHANGED<<transfers, remote_files, local_files>>

(* If scanner is scanning, find a file we're not locally aware of and copy its information *)
(* If no such files are found, finish scanning *)
ScanDo ==
  /\ scanner_state = "scanning"
  /\ IF \E remote_file \in remote_files: ~FoundLocally(remote_file) THEN
        LET remote_file == CHOOSE remote_file \in remote_files: ~FoundLocally(remote_file) IN
        LET file_id == CHOOSE file_id \in FileId: local_files[file_id] = <<>> IN
        /\ local_files' = [local_files EXCEPT ![file_id] = [remote_file |-> remote_file,
                                                            transfer_id |-> 0,
                                                            state |-> "waiting-transfer"]]
        /\ UNCHANGED<<transfers, remote_files, scanner_state>>
     ELSE
        /\ scanner_state' = "scanned"
        /\ UNCHANGED<<transfers, remote_files, local_files>>

(* Transfer *)

(* Are there free slots in the transfers structure? *)
HasFreeTransferSlot == \E transfer_id \in TransferId: transfers[transfer_id] = <<>>

(* Are there files that are waiting for transfer? *)
HasFileWaitingTransfer == \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"

(* If the scanner has scanned, there are free transfer slots and there are files waiting transfer,
 * pick one such file and start the transfer. *)
TransferStart ==
  /\ scanner_state = "scanned"
  /\ HasFreeTransferSlot /\ HasFileWaitingTransfer
  /\ \E file_id \in HasFileId: local_files[file_id].state = "waiting-transfer"
  /\ \E transfer_id \in FreeTransferId:
     LET file_id == CHOOSE file_id \in HasFileId: local_files[file_id].state = "waiting-transfer" IN
     LET local_file == local_files[file_id] IN
     /\ transfers' = [transfers EXCEPT ![transfer_id] = [remote_file  |-> local_file.remote_file,
                                                         state      |-> "active",
                                                         local_size |-> 0,
                                                         file_id    |-> file_id]]
     /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = transfer_id,
                                                                  !.state           = "transferring"]]
     /\ UNCHANGED<<remote_files, scanner_state>>

(* If there are active transfers, transfer one unit of data. If the file has already transferred
 * all the data, mark it finished.  *)
TransferDo ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  /\ transfer.state = "active"
  /\ IF transfer.local_size < transfer.remote_file.size
     THEN transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.local_size = transfer.local_size + 1]]
     ELSE transfers' = [transfers EXCEPT ![transfer_id] = [@ EXCEPT !.state = "finished"]]
  /\ UNCHANGED<<remote_files, local_files, scanner_state>>

(* If the transfer is finished, release the transfer slot and mark the local file transferred *)
TransferFinished ==
  \E transfer_id \in ActiveTransferId:
  LET transfer == transfers[transfer_id] IN
  LET file_id == transfer.file_id IN
  /\ transfer.state = "finished"
  /\ transfers' = [transfers EXCEPT ![transfer_id] = <<>>]
  /\ local_files' = [local_files EXCEPT ![file_id] = [@ EXCEPT !.transfer_id     = 0,
                                                               !.state           = "transferred"]]
  /\ UNCHANGED<<remote_files, scanner_state>>

----
(* State *)

Stutter == UNCHANGED<<vars>>

Next ==
  \/ ScanStart
  \/ ScanDo
  \/ TransferStart
  \/ TransferDo
  \/ TransferFinished
\*  \/ Stutter

Init ==
  /\ remote_files    = GenerateFiles({})
  /\ local_files   = [file_id \in FileId |-> <<>>]
  /\ transfers     = [transfer_id \in TransferId |-> <<>>]
  /\ scanner_state = "idle"

(* Properties *)

EventuallyAllFilesAreTransferred ==
  Init =>
  <>\A remote_file \in remote_files:
    \E file_id \in HasFileId:
    /\ local_files[file_id].remote_file = remote_file
    /\ local_files[file_id].state = "transferred"

Spec ==
  /\ Init
  /\ [][Next]_vars
  /\ WF_vars(Next)

================================================================================
