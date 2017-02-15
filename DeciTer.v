
Require Import Lib BinPosDef BinNatDef BinIntDef.

(** Instead of list of digits as in [Deci.v], we try here
    an ad-hoc specialized list-like datatype. Moreover, the conversion
    to digits are done via Horner-style computations in base 10 instead
    of division+modulo in the other base.
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

(** A few easy operations. For more advanced computations, use the conversions
    with other Coq numeral datatypes (e.g. Z) and the operations on them. *)

(** For conversions with binary numbers, it is easier to operate
    on little-endian numbers. *)

Fixpoint rev (l l' : dec) :=
  match l with
  | Stop => l'
  | D0 l => rev l (D0 l')
  | D1 l => rev l (D1 l')
  | D2 l => rev l (D2 l')
  | D3 l => rev l (D3 l')
  | D4 l => rev l (D4 l')
  | D5 l => rev l (D5 l')
  | D6 l => rev l (D6 l')
  | D7 l => rev l (D7 l')
  | D8 l => rev l (D8 l')
  | D9 l => rev l (D9 l')
  end.

Module Little.

(** Successor of little-endian numbers *)

Fixpoint succ d :=
  match d with
  | Stop => D1 Stop
  | D0 l => D1 l
  | D1 l => D2 l
  | D2 l => D3 l
  | D3 l => D4 l
  | D4 l => D5 l
  | D5 l => D6 l
  | D6 l => D7 l
  | D7 l => D8 l
  | D8 l => D9 l
  | D9 l => D0 (succ l)
  end.

(** Doubling little-endian numbers *)

Fixpoint double d :=
  match d with
  | Stop => Stop
  | D0 l => D0 (double l)
  | D1 l => D2 (double l)
  | D2 l => D4 (double l)
  | D3 l => D6 (double l)
  | D4 l => D8 (double l)
  | D5 l => D0 (succ_double l)
  | D6 l => D2 (succ_double l)
  | D7 l => D4 (succ_double l)
  | D8 l => D6 (succ_double l)
  | D9 l => D8 (succ_double l)
  end

with succ_double d :=
  match d with
  | Stop => D1 Stop
  | D0 l => D1 (double l)
  | D1 l => D3 (double l)
  | D2 l => D5 (double l)
  | D3 l => D7 (double l)
  | D4 l => D9 (double l)
  | D5 l => D1 (succ_double l)
  | D6 l => D3 (succ_double l)
  | D7 l => D5 (succ_double l)
  | D8 l => D7 (succ_double l)
  | D9 l => D9 (succ_double l)
  end.

End Little.


(** Conversion between decimal and Peano nat representations *)

Module DecNat.

Local Notation ten := (S (S (S (S (S (S (S (S (S (S O)))))))))).
Local Notation tenfold := (TailNat.mul ten).

Fixpoint of_dec_acc (d:dec)(acc:nat) :=
  match d with
  | Stop => acc
  | D0 d => of_dec_acc d (tenfold acc)
  | D1 d => of_dec_acc d (S (tenfold acc))
  | D2 d => of_dec_acc d (S (S (tenfold acc)))
  | D3 d => of_dec_acc d (S (S (S (tenfold acc))))
  | D4 d => of_dec_acc d (S (S (S (S (tenfold acc)))))
  | D5 d => of_dec_acc d (S (S (S (S (S (tenfold acc))))))
  | D6 d => of_dec_acc d (S (S (S (S (S (S (tenfold acc)))))))
  | D7 d => of_dec_acc d (S (S (S (S (S (S (S (tenfold acc))))))))
  | D8 d => of_dec_acc d (S (S (S (S (S (S (S (S (tenfold acc)))))))))
  | D9 d => of_dec_acc d (S (S (S (S (S (S (S (S (S (tenfold acc))))))))))
  end.

Definition of_dec (d:dec) := of_dec_acc d O.

Fixpoint to_little_dec n acc :=
  match n with
  | O => acc
  | S n => to_little_dec n (Little.succ acc)
  end.

Definition to_dec n :=
  rev (to_little_dec n Stop) Stop.

End DecNat.


(** Same for decimal and binary N numbers *)

Module DecPos.

Local Open Scope positive.

Fixpoint to_dec_rev p :=
  match p with
  | 1 => D1 Stop
  | p~1 => Little.succ_double (to_dec_rev p)
  | p~0 => Little.double (to_dec_rev p)
  end.

Definition to_dec p := rev (to_dec_rev p) Stop.

Local Notation ten := 1~0~1~0.
Local Notation tenfold := (Pos.mul ten).

Fixpoint of_dec_acc (d:dec)(acc:positive) :=
  match d with
  | Stop => acc
  | D0 l => of_dec_acc l (tenfold acc)
  | D1 l => of_dec_acc l (Pos.add 1 (tenfold acc))
  | D2 l => of_dec_acc l (Pos.add 2 (tenfold acc))
  | D3 l => of_dec_acc l (Pos.add 3 (tenfold acc))
  | D4 l => of_dec_acc l (Pos.add 4 (tenfold acc))
  | D5 l => of_dec_acc l (Pos.add 5 (tenfold acc))
  | D6 l => of_dec_acc l (Pos.add 6 (tenfold acc))
  | D7 l => of_dec_acc l (Pos.add 7 (tenfold acc))
  | D8 l => of_dec_acc l (Pos.add 8 (tenfold acc))
  | D9 l => of_dec_acc l (Pos.add 9 (tenfold acc))
  end.

Fixpoint of_dec (d:dec) : N :=
  match d with
  | Stop => N0
  | D0 l => of_dec l
  | D1 l => Npos (of_dec_acc l 1)
  | D2 l => Npos (of_dec_acc l 1~0)
  | D3 l => Npos (of_dec_acc l 1~1)
  | D4 l => Npos (of_dec_acc l 1~0~0)
  | D5 l => Npos (of_dec_acc l 1~0~1)
  | D6 l => Npos (of_dec_acc l 1~1~0)
  | D7 l => Npos (of_dec_acc l 1~1~1)
  | D8 l => Npos (of_dec_acc l 1~0~0~0)
  | D9 l => Npos (of_dec_acc l 1~0~0~1)
  end.

End DecPos.


Module DecN.

Local Open Scope N.

Definition of_dec := DecPos.of_dec.

Definition to_dec (n:N) :=
  match n with
  | N0 => Stop
  | Npos p => DecPos.to_dec p
  end.

End DecN.

Module DecZ.

Definition dec2z d :=
 match DecN.of_dec d with
 | N0 => Z0
 | Npos p => Zpos p
 end.

Definition z2dec z :=
 match z with
 | Zpos p => DecPos.to_dec p
 | _ => Stop (* TODO : for now, we discard negative numbers *)
 end.

End DecZ.


(** A successor on decimal. Not really mandatory, just to state
    that our conversions preserve the order of numbers *)

Definition succ d := rev (Little.succ (rev d Stop)) Stop.

(** The strict order on decimal numbers is the transitive
    closure of the successor *)

Inductive lt : dec -> dec -> Prop :=
 | Succ x : lt x (succ x)
 | Trans x y z : lt x y -> lt y z -> lt x z.
