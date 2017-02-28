
(** * Library stuff *)

(** Tail recursive operations on nat *)


Module TailNat.

Fixpoint add n m :=
  match n with
    | O => m
    | S n => add n (S m)
  end.

Fixpoint addmul r n m :=
  match n with
    | O => r
    | S n => addmul (add m r) n m
  end.

Definition mul n m := addmul 0 n m.

Lemma add_spec n m : add n m = n + m.
Proof.
 revert m. induction n as [|n IH]; simpl; auto.
 intros. now rewrite IH, plus_n_Sm.
Qed.

Lemma addmul_spec r n m : addmul r n m = r + n * m.
Proof.
 revert m r. induction n as [| n IH]; simpl; auto.
 intros. rewrite IH, add_spec. clear IH.
 (* we dont have add_assoc + add_comm here ...*)
 generalize (n*m). clear n. revert r.
 induction m; destruct r; simpl; auto. intros.
 now rewrite <- !plus_n_Sm, <- IHm.
Qed.

Lemma mul_spec n m : mul n m = n * m.
Proof.
 unfold mul. now rewrite addmul_spec.
Qed.

End TailNat.

(** Missing euclidean division on nat, doing both div + modulo *)

Definition diveucl x y :=
 match y with
 | 0 => (y,y)
 | S y' =>
   let (q,r) := Nat.divmod x y' 0 y' in
   (q,y'-r)
 end.

Lemma diveucl_spec x y : diveucl x y = (Nat.div x y, Nat.modulo x y).
Proof.
 destruct y; simpl; trivial. now destruct Nat.divmod.
Qed.

(** A datatype for encoding carries.
    This is isomorphic to [bool*A], but with nicer names *)

Inductive carry (A:Type) :=
 | Carry : A -> carry A
 | NoCarry : A -> carry A.

Arguments Carry {A}.
Arguments NoCarry {A}.

Definition carry_proj {A} (c : carry A) :=
  match c with
  | Carry a => a
  | NoCarry a => a
  end.



(** Tail recursive operations on positive *)

Require Import BinPosDef.
Local Open Scope positive.

Module TailPos.

(** NB: even if [a] below has type [positive], its role differ deeply
    from the other (little-endian) numbers around. It is an accumulator
    of binary digits waiting to be "zipped" back on the result
    (via function [rev]).
*)

Fixpoint rev a p :=
  match a with
    | 1 => p
    | a~1 => rev a (p~1)
    | a~0 => rev a (p~0)
  end.

Fixpoint succ p a :=
  match p with
    | p~1 => succ p (a~0)
    | p~0 => rev a (p~1)
    | 1 => rev a (1~0)
  end.

Fixpoint add_tail p q a :=
  match p, q with
    | p~1, q~1 => add_carry p q (a~0)
    | p~1, q~0 => add_tail p q (a~1)
    | p~0, q~1 => add_tail p q (a~1)
    | p~0, q~0 => add_tail p q (a~0)
    | p, 1 => succ p a
    | 1, q => succ q a
  end
with add_carry p q a :=
  match p, q with
    | p~1, q~1 => add_carry p q (a~1)
    | p~1, q~0 => add_carry p q (a~0)
    | p~0, q~1 => add_carry p q (a~0)
    | p~0, q~0 => add_tail p q (a~1)
    | p~1, 1 => succ p (a~1)
    | p~0, 1 => succ p (a~0)
    | 1, q~1 => succ q (a~1)
    | 1, q~0 => succ q (a~0)
    | 1, 1 => rev a 1~1
  end.

Definition add p q := add_tail p q 1.

Definition tenfold p := (add p (p~0~0))~0.

Lemma succ_alt p q : succ p q = rev q (Pos.succ p).
Proof.
 revert q.
 induction p; simpl; auto.
 intros. now rewrite IHp.
Qed.

Lemma add_alt p q a :
  add_tail p q a = rev a (Pos.add p q) /\
  add_carry p q a = rev a (Pos.add_carry p q).
Proof.
 revert q a.
 induction p; destruct q; simpl; auto; intros;
  try destruct (IHp q (a~0)), (IHp q (a~1)); auto; rewrite !succ_alt; auto.
Qed.

Lemma add_equiv p q : add p q = Pos.add p q.
Proof.
 apply add_alt.
Qed.

Lemma tenfold_ok p : tenfold p = Pos.mul 10 p.
Proof.
 unfold tenfold. now rewrite add_equiv.
Qed.

End TailPos.
