
Require Import Lib BinPosDef BinNatDef BinIntDef.

Open Scope list_scope.

(** We represent here number in base 16 by lists of hex digits,
    in big endian order (most significant digit comes first). *)

Inductive hexdigit :=
  H0 | H1 | H2 | H3 | H4 | H5 | H6 | H7 |
  H8 | H9 | HA | HB | HC | HD | HE | HF.

Definition hex := list hexdigit. (** big endian *)

Definition sixteen := H1 :: H0 :: nil. (** For example... *)

(** This representation favors simplicity over canonicity :
    we might need later to normalize by removing the leading zeros *)

Fixpoint norm l :=
  match l with
  | H0 :: l => norm l
  | _ => l
  end.



(** Conversion between decimal and Peano nat representations *)

Module HexNat.

Definition digit2nat d :=
  match d with
  | H0 => 0
  | H1 => 1
  | H2 => 2
  | H3 => 3
  | H4 => 4
  | H5 => 5
  | H6 => 6
  | H7 => 7
  | H8 => 8
  | H9 => 9
  | HA => 10
  | HB => 11
  | HC => 12
  | HD => 13
  | HE => 14
  | HF => 15
  end.

Definition nat2digit n :=
  match n with
  | 0 => H0
  | 1 => H1
  | 2 => H2
  | 3 => H3
  | 4 => H4
  | 5 => H5
  | 6 => H6
  | 7 => H7
  | 8 => H8
  | 9 => H9
  | 10 => HA
  | 11 => HB
  | 12 => HC
  | 13 => HD
  | 14 => HE
  | _ => HF (* n>15 shouldn't happen *)
  end.

Fixpoint h2n (h:hex)(acc:nat) :=
  match h with
  | nil => acc
  | hd :: l => h2n l (TailNat.addmul (digit2nat hd) 16 acc)
  end.

Definition hex2nat h := h2n h 0.

Fixpoint n2h (n:nat)(acc:hex)(count:nat) :=
 match count, n with
 | 0, _ => acc
 | _, 0 => acc
 | S count', _ =>
     let (q,r) := diveucl n 16 in
     n2h q (nat2digit r :: acc) count'
 end.

Definition nat2hex n := n2h n nil n.

End HexNat.


(** For binary N numbers, we could simply regroup bits. *)

Module HexN.

Local Open Scope N.

Fixpoint h2p h acc :=
 match h with
 | nil => acc
 | H0 :: h => h2p h (acc~0~0~0~0)
 | H1 :: h => h2p h (acc~0~0~0~1)
 | H2 :: h => h2p h (acc~0~0~1~0)
 | H3 :: h => h2p h (acc~0~0~1~1)
 | H4 :: h => h2p h (acc~0~1~0~0)
 | H5 :: h => h2p h (acc~0~1~0~1)
 | H6 :: h => h2p h (acc~0~1~1~0)
 | H7 :: h => h2p h (acc~0~1~1~1)
 | H8 :: h => h2p h (acc~1~0~0~0)
 | H9 :: h => h2p h (acc~1~0~0~1)
 | HA :: h => h2p h (acc~1~0~1~0)
 | HB :: h => h2p h (acc~1~0~1~1)
 | HC :: h => h2p h (acc~1~1~0~0)
 | HD :: h => h2p h (acc~1~1~0~1)
 | HE :: h => h2p h (acc~1~1~1~0)
 | HF :: h => h2p h (acc~1~1~1~1)
 end%positive.

Fixpoint hex2n h :=
 match h with
 | nil => 0
 | H0 :: h => hex2n h
 | H1 :: h => Npos (h2p h 1)
 | H2 :: h => Npos (h2p h 2)
 | H3 :: h => Npos (h2p h 3)
 | H4 :: h => Npos (h2p h 4)
 | H5 :: h => Npos (h2p h 5)
 | H6 :: h => Npos (h2p h 6)
 | H7 :: h => Npos (h2p h 7)
 | H8 :: h => Npos (h2p h 8)
 | H9 :: h => Npos (h2p h 9)
 | HA :: h => Npos (h2p h 10)
 | HB :: h => Npos (h2p h 11)
 | HC :: h => Npos (h2p h 12)
 | HD :: h => Npos (h2p h 13)
 | HE :: h => Npos (h2p h 14)
 | HF :: h => Npos (h2p h 15)
 end.

Fixpoint p2h p acc :=
  match p with
  | 1 => H1::acc
  | 2 => H2::acc
  | 3 => H3::acc
  | 4 => H4::acc
  | 5 => H5::acc
  | 6 => H6::acc
  | 7 => H7::acc
  | 8 => H8::acc
  | 9 => H9::acc
  | 10 => HA::acc
  | 11 => HB::acc
  | 12 => HC::acc
  | 13 => HD::acc
  | 14 => HE::acc
  | 15 => HF::acc
  | p~0~0~0~0 => p2h p (H0::acc)
  | p~0~0~0~1 => p2h p (H1::acc)
  | p~0~0~1~0 => p2h p (H2::acc)
  | p~0~0~1~1 => p2h p (H3::acc)
  | p~0~1~0~0 => p2h p (H4::acc)
  | p~0~1~0~1 => p2h p (H5::acc)
  | p~0~1~1~0 => p2h p (H6::acc)
  | p~0~1~1~1 => p2h p (H7::acc)
  | p~1~0~0~0 => p2h p (H8::acc)
  | p~1~0~0~1 => p2h p (H9::acc)
  | p~1~0~1~0 => p2h p (HA::acc)
  | p~1~0~1~1 => p2h p (HB::acc)
  | p~1~1~0~0 => p2h p (HC::acc)
  | p~1~1~0~1 => p2h p (HD::acc)
  | p~1~1~1~0 => p2h p (HE::acc)
  | p~1~1~1~1 => p2h p (HF::acc)
  end%positive.

Definition n2hex n :=
 match n with
 | 0 => nil
 | Npos p => p2h p nil
 end.

End HexN.

(** For positive and Z numbers, we simply go through N for the moment. *)

Module HexPos.

Definition hex2pos d :=
 match HexN.hex2n d with
 | N0 => None
 | Npos p => Some p
 end.

Definition pos2hex p := HexN.p2h p nil.

End HexPos.

Module HexZ.

Definition hex2z d :=
 match HexN.hex2n d with
 | N0 => Z0
 | Npos p => Zpos p
 end.

Definition z2hex z :=
 match z with
 | Zpos p => HexN.n2hex (Npos p)
 | _ => nil (* TODO : for now, we discard negative numbers *)
 end.

End HexZ.
