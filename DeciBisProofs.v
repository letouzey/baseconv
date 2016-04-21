
Require Import Lib DeciBis Arith Omega NArith PArith ZArith.
Require Deci DeciProofs.

Open Scope list_scope.

(** Correctness proofs for the nat conversions for the ad-hoc
    decimal representation : we show an equivalence with the
    first representation with standard lists. *)

Module NatProofs.

Import DecNat.

Fixpoint tolist (d:dec) : Deci.dec :=
  match d with
  | Stop => nil
  | D0 d => Deci.D0 :: tolist d
  | D1 d => Deci.D1 :: tolist d
  | D2 d => Deci.D2 :: tolist d
  | D3 d => Deci.D3 :: tolist d
  | D4 d => Deci.D4 :: tolist d
  | D5 d => Deci.D5 :: tolist d
  | D6 d => Deci.D6 :: tolist d
  | D7 d => Deci.D7 :: tolist d
  | D8 d => Deci.D8 :: tolist d
  | D9 d => Deci.D9 :: tolist d
  end.

Fixpoint fromlist (d:Deci.dec) : dec :=
  match d with
  | nil => Stop
  | Deci.D0 :: d => D0 (fromlist d)
  | Deci.D1 :: d => D1 (fromlist d)
  | Deci.D2 :: d => D2 (fromlist d)
  | Deci.D3 :: d => D3 (fromlist d)
  | Deci.D4 :: d => D4 (fromlist d)
  | Deci.D5 :: d => D5 (fromlist d)
  | Deci.D6 :: d => D6 (fromlist d)
  | Deci.D7 :: d => D7 (fromlist d)
  | Deci.D8 :: d => D8 (fromlist d)
  | Deci.D9 :: d => D9 (fromlist d)
  end.

Lemma to_from (d:Deci.dec) : tolist (fromlist d) = d.
Proof.
 induction d as [|[ ] IH ]; simpl; f_equal; auto.
Qed.

Lemma from_to (d:dec) : fromlist (tolist d) = d.
Proof.
 induction d; simpl; f_equal; auto.
Qed.

Lemma norm_to (d:dec) : tolist (norm d) = Deci.norm (tolist d).
Proof.
 induction d; auto.
Qed.

Lemma d2n_to d acc :
 d2n d acc = Deci.DecNat.d2n (tolist d) acc.
Proof.
 revert acc.
 induction d; simpl; auto.
Qed.

Lemma dec2nat_to d : dec2nat d = Deci.DecNat.dec2nat (tolist d).
Proof.
 unfold dec2nat. apply d2n_to.
Qed.

Lemma n2d_to n acc c :
 tolist (n2d n acc c) = Deci.DecNat.n2d n (tolist acc) c.
Proof.
 revert n acc.
 induction c; auto.
 intros; destruct n; auto.
 simpl. destruct Nat.divmod.
 rewrite IHc. f_equal.
 destruct n1 as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; auto.
Qed.

Lemma nat2dec_to n :
 tolist (nat2dec n) = Deci.DecNat.nat2dec n.
Proof.
 unfold nat2dec. apply n2d_to.
Qed.

(** We now obtain results about the conversions *)

Lemma nat2dec2nat (n:nat) : dec2nat (nat2dec n) = n.
Proof.
 rewrite dec2nat_to, nat2dec_to.
 apply DeciProofs.NatProofs.nat2dec2nat.
Qed.

Lemma nat2dec_inj n n' : nat2dec n = nat2dec n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (nat2dec2nat n), <- (nat2dec2nat n'), EQ.
Qed.

Lemma dec2nat2dec (d:dec) :
  nat2dec (dec2nat d) = norm d.
Proof.
 rewrite <- (from_to (nat2dec (dec2nat d))).
 rewrite nat2dec_to, dec2nat_to.
 rewrite DeciProofs.NatProofs.dec2nat2dec.
 now rewrite <- norm_to, from_to.
Qed.

Lemma dec2nat_norm d d' : norm d = norm d' ->
 dec2nat d = dec2nat d'.
Proof.
 intros EQ. apply nat2dec_inj. now rewrite !dec2nat2dec.
Qed.

Lemma dec2nat_inj d d' :
 dec2nat d = dec2nat d' -> norm d = norm d'.
Proof.
 intros. rewrite <- !dec2nat2dec. now f_equal.
Qed.

Lemma dec2nat_iff d d' : dec2nat d = dec2nat d' <-> norm d = norm d'.
Proof.
 split. apply dec2nat_inj. apply dec2nat_norm.
Qed.

End NatProofs.
