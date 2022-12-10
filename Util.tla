---- MODULE Util ---------------------------------------------------------------
(* Documentation *)
--------------------------------------------------------------------------------
LOCAL INSTANCE Sequences
LOCAL INSTANCE Naturals

(* Convert a set to a sequence (in some order) *)
RECURSIVE SeqOfSet(_)
SeqOfSet(S) ==
   IF S # {}
   THEN LET element == CHOOSE x \in S: TRUE IN
        LET next_S == S \ {element} IN
        <<element>> \o SeqOfSet(next_S)
   ELSE <<>>

(* Given an array, return its values as a set *)
Image(F) == { F[x] : x \in DOMAIN F }

(* Return a sequence with the given index omitted (and the remaining values shifted) *)
SeqRemoveIndex(S, Index) ==
   SubSeq(S, 1, Index - 1) \o SubSeq(S, Index + 1, Len(S))

================================================================================
