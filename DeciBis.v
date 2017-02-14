
Require Import Lib BinNatDef BinIntDef.

(** Instead of list of digits as in [Deci.v], we try here
    an ad-hoc specialized list-like datatype.

    Pro :
     - No dependency over the list datatype, hence easier reification.
     - Slightly more compact representation in memory

    Cons :
     - Quite harder to prove correctness with this version.
       For the moment, the proofs are done by proving a
       bijection with the list-based representation.
*)

Inductive dec :=
 | Stop
 | D0 : dec -> dec
 | D1 : dec -> dec
 | D2 : dec -> dec
 | D3 : dec -> dec
 | D4 : dec -> dec
 | D5 : dec -> dec
 | D6 : dec -> dec
 | D7 : dec -> dec
 | D8 : dec -> dec
 | D9 : dec -> dec.

Definition ten := D1 (D0 Stop). (** For example... *)

(** This representation favors simplicity over canonicity :
    we might need later to normalize by removing the leading zeros *)

Fixpoint norm l :=
  match l with
  | D0 l => norm l
  | _ => l
  end.



(** Conversion between decimal and Peano nat representations *)

Module DecNat.

Definition nat2digit n d :=
  match n with
  | 0 => D0 d
  | 1 => D1 d
  | 2 => D2 d
  | 3 => D3 d
  | 4 => D4 d
  | 5 => D5 d
  | 6 => D6 d
  | 7 => D7 d
  | 8 => D8 d
  | _ => D9 d (* n>9 shouldn't happen *)
  end.

Fixpoint d2n (d:dec)(acc:nat) :=
  match d with
  | Stop => acc
  | D0 d => d2n d (TailNat.addmul 0 10 acc)
  | D1 d => d2n d (TailNat.addmul 1 10 acc)
  | D2 d => d2n d (TailNat.addmul 2 10 acc)
  | D3 d => d2n d (TailNat.addmul 3 10 acc)
  | D4 d => d2n d (TailNat.addmul 4 10 acc)
  | D5 d => d2n d (TailNat.addmul 5 10 acc)
  | D6 d => d2n d (TailNat.addmul 6 10 acc)
  | D7 d => d2n d (TailNat.addmul 7 10 acc)
  | D8 d => d2n d (TailNat.addmul 8 10 acc)
  | D9 d => d2n d (TailNat.addmul 9 10 acc)
  end.

Definition dec2nat d := d2n d 0.

Fixpoint n2d (n:nat)(acc:dec)(count:nat) :=
 match count, n with
 | 0, _ => acc
 | _, 0 => acc
 | S count', _ =>
     let (q,r) := diveucl n 10 in
     n2d q (nat2digit r acc) count'
 end.

Definition nat2dec n := n2d n Stop n.

End DecNat.

(** Same for decimal and binary N numbers *)

Module DecN.

Local Open Scope N.

Fixpoint d2n (d:dec)(acc:N) :=
  match d with
  | Stop => acc
  | D0 d => d2n d (N.add 0 (N.mul 10 acc))
  | D1 d => d2n d (N.add 1 (N.mul 10 acc))
  | D2 d => d2n d (N.add 2 (N.mul 10 acc))
  | D3 d => d2n d (N.add 3 (N.mul 10 acc))
  | D4 d => d2n d (N.add 4 (N.mul 10 acc))
  | D5 d => d2n d (N.add 5 (N.mul 10 acc))
  | D6 d => d2n d (N.add 6 (N.mul 10 acc))
  | D7 d => d2n d (N.add 7 (N.mul 10 acc))
  | D8 d => d2n d (N.add 8 (N.mul 10 acc))
  | D9 d => d2n d (N.add 9 (N.mul 10 acc))
  end.

Definition dec2n d := d2n d 0.

Definition n2digit (n:N) d :=
  match n with
  | 0 => D0 d
  | 1 => D1 d
  | 2 => D2 d
  | 3 => D3 d
  | 4 => D4 d
  | 5 => D5 d
  | 6 => D6 d
  | 7 => D7 d
  | 8 => D8 d
  | _ => D9 d (* n>9 shouldn't happen *)
  end.

Fixpoint n2d (n:N)(acc:dec)(count:positive) :=
 match count, n with
 | xH, _ => acc
 | _, 0 => acc
 | xO count', _ | xI count', _ =>
     let (q,r) := N.div_eucl n 10 in
     n2d q (n2digit r acc) count'
 end.

Definition n2dec n :=
  n2d n Stop (match n with 0 => xH | Npos p => xO p end).

End DecN.

(** For positive and Z numbers, we simply go through N for the moment. *)

Module DecPos.

Definition dec2pos d :=
 match DecN.dec2n d with
 | N0 => None
 | Npos p => Some p
 end.

Definition pos2dec p := DecN.n2dec (Npos p).

End DecPos.

Module DecZ.

Definition dec2z d :=
 match DecN.dec2n d with
 | N0 => Z0
 | Npos p => Zpos p
 end.

Definition z2dec z :=
 match z with
 | Zpos p => DecN.n2dec (Npos p)
 | _ => Stop (* TODO : for now, we discard negative numbers *)
 end.

End DecZ.
