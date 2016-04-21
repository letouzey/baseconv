
Require Import Lib BinNatDef BinIntDef.

Open Scope list_scope.

(** We represent here number in base 10 by lists of decimal digits,
    in big endian order (most significant digit comes first). *)

Inductive digit := D0 | D1 | D2 | D3 | D4 | D5 | D6 | D7 | D8 | D9.

Definition dec := list digit. (** big endian *)

Definition ten := D1 :: D0 :: nil. (** For example... *)

(** This representation favors simplicity over canonicity :
    we might need later to normalize by removing the leading zeros *)

Fixpoint norm l :=
  match l with
  | D0 :: l => norm l
  | _ => l
  end.



(** Conversion between decimal and Peano nat representations *)

Module DecNat.

Definition digit2nat d :=
  match d with
  | D0 => 0
  | D1 => 1
  | D2 => 2
  | D3 => 3
  | D4 => 4
  | D5 => 5
  | D6 => 6
  | D7 => 7
  | D8 => 8
  | D9 => 9
  end.

Definition nat2digit n :=
  match n with
  | 0 => D0
  | 1 => D1
  | 2 => D2
  | 3 => D3
  | 4 => D4
  | 5 => D5
  | 6 => D6
  | 7 => D7
  | 8 => D8
  | _ => D9 (* n>9 shouldn't happen *)
  end.

Fixpoint d2n (d:dec)(acc:nat) :=
  match d with
  | nil => acc
  | d :: l => d2n l (TailNat.addmul (digit2nat d) 10 acc)
  end.

Definition dec2nat d := d2n d 0.

Fixpoint n2d (n:nat)(acc:dec)(count:nat) :=
 match count, n with
 | 0, _ => acc
 | _, 0 => acc
 | S count', _ =>
     let (q,r) := diveucl n 10 in
     n2d q (nat2digit r :: acc) count'
 end.

Definition nat2dec n := n2d n nil n.

End DecNat.


(** Same for decimal and binary N numbers *)

Module DecN.

Local Open Scope N.

Definition digit2n d : N :=
  match d with
  | D0 => 0
  | D1 => 1
  | D2 => 2
  | D3 => 3
  | D4 => 4
  | D5 => 5
  | D6 => 6
  | D7 => 7
  | D8 => 8
  | D9 => 9
  end.

Definition n2digit (n:N) :=
  match n with
  | 0 => D0
  | 1 => D1
  | 2 => D2
  | 3 => D3
  | 4 => D4
  | 5 => D5
  | 6 => D6
  | 7 => D7
  | 8 => D8
  | _ => D9 (* n>9 shouldn't happen *)
  end.

Fixpoint d2n (d:dec)(acc:N) :=
  match d with
  | nil => acc
  | d :: l => d2n l (N.add (digit2n d) (N.mul 10 acc))
  end.

Definition dec2n d := d2n d 0.

Fixpoint n2d (n:N)(acc:dec)(count:positive) :=
 match count, n with
 | xH, _ => acc
 | _, 0 => acc
 | xO count', _ | xI count', _ =>
     let (q,r) := N.div_eucl n 10 in
     n2d q (n2digit r :: acc) count'
 end.

Definition n2dec n :=
  n2d n nil (match n with 0 => xH | Npos p => xO p end).

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
 | _ => nil (* TODO : for now, we discard negative numbers *)
 end.

End DecZ.
