
Require Import Lib BinPosDef BinNatDef BinIntDef DeciTer.

(** Same as [DeciTer], but with tail-recursive operations on Positive
    numbers *)

Module TailLittle.

(** Doubling + mirrorring little-endian numbers *)

Fixpoint rev_double d acc :=
  match d with
  | Stop => acc
  | D0 l => rev_double l (D0 acc)
  | D1 l => rev_double l (D2 acc)
  | D2 l => rev_double l (D4 acc)
  | D3 l => rev_double l (D6 acc)
  | D4 l => rev_double l (D8 acc)
  | D5 l => rev_succ_double l (D0 acc)
  | D6 l => rev_succ_double l (D2 acc)
  | D7 l => rev_succ_double l (D4 acc)
  | D8 l => rev_succ_double l (D6 acc)
  | D9 l => rev_succ_double l (D8 acc)
  end

with rev_succ_double d acc :=
  match d with
  | Stop => D1 acc
  | D0 l => rev_double l (D1 acc)
  | D1 l => rev_double l (D3 acc)
  | D2 l => rev_double l (D5 acc)
  | D3 l => rev_double l (D7 acc)
  | D4 l => rev_double l (D9 acc)
  | D5 l => rev_succ_double l (D1 acc)
  | D6 l => rev_succ_double l (D3 acc)
  | D7 l => rev_succ_double l (D5 acc)
  | D8 l => rev_succ_double l (D7 acc)
  | D9 l => rev_succ_double l (D9 acc)
  end.

End TailLittle.

(** Doubling big-endian numbers *)

Definition double d := TailLittle.rev_double (rev d Stop) Stop.
Definition succ_double d := TailLittle.rev_succ_double (rev d Stop) Stop.

Lemma double_alt d :
 (forall acc, TailLittle.rev_double d acc = rev (Little.double d) acc) /\
 (forall acc, TailLittle.rev_succ_double d acc = rev (Little.succ_double d) acc).
Proof.
 induction d; simpl; auto; split; intros; destruct IHd as (IH1,IH2);
  rewrite ?IH1, ?IH2; auto.
Qed.

Module DecPos.

Local Open Scope positive.

Fixpoint to_dec_acc p acc :=
  match p with
  | 1 => acc
  | p~1 => to_dec_acc p (succ_double acc)
  | p~0 => to_dec_acc p (double acc)
  end.

Definition to_dec p := to_dec_acc (TailPos.rev p xH) (D1 Stop).

Fixpoint of_dec_acc (d:dec)(acc:positive) :=
  match d with
  | Stop => acc
  | D0 l => of_dec_acc l (TailPos.tenfold acc)
  | D1 l => of_dec_acc l (TailPos.add 1 (TailPos.tenfold acc))
  | D2 l => of_dec_acc l (TailPos.add 2 (TailPos.tenfold acc))
  | D3 l => of_dec_acc l (TailPos.add 3 (TailPos.tenfold acc))
  | D4 l => of_dec_acc l (TailPos.add 4 (TailPos.tenfold acc))
  | D5 l => of_dec_acc l (TailPos.add 5 (TailPos.tenfold acc))
  | D6 l => of_dec_acc l (TailPos.add 6 (TailPos.tenfold acc))
  | D7 l => of_dec_acc l (TailPos.add 7 (TailPos.tenfold acc))
  | D8 l => of_dec_acc l (TailPos.add 8 (TailPos.tenfold acc))
  | D9 l => of_dec_acc l (TailPos.add 9 (TailPos.tenfold acc))
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

(*
Time Compute (N.log2 (DecPos.of_dec (DecPos.to_dec (Pos.pow 2 100000)))).
 131.336s contre 92s en version DeciTer (oui ca passe en non tail-rec ?!)
*)