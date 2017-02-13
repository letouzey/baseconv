
Require Import Lib DeciTer Arith Omega NArith PArith ZArith.

Module NatProofs.

Import DecNat.

(* A direct definition of to_little_dec, non tail-recursive *)

Fixpoint to_ldec n :=
 match n with
 | 0 => Stop
 | S n => Little.succ (to_ldec n)
 end.

Lemma to_little_dec_succ_r n d :
 to_little_dec n (Little.succ d) = Little.succ (to_little_dec n d).
Proof.
 revert d; induction n; simpl; auto.
Qed.

Lemma to_little_dec_alt n :
  to_little_dec n Stop = to_ldec n.
Proof.
 induction n; simpl; auto.
 change (D1 Stop) with (Little.succ Stop).
 rewrite to_little_dec_succ_r. now f_equal.
Qed.

Lemma to_ldec_succ n : to_ldec (S n) = Little.succ (to_ldec n).
Proof.
 reflexivity.
Qed.

(* A direct definition of little-endian [of_dec] *)

Fixpoint of_ldec (d:dec) : nat :=
  match d with
  | Stop => 0
  | D0 d => 10 * of_ldec d
  | D1 d => 1 + 10 * of_ldec d
  | D2 d => 2 + 10 * of_ldec d
  | D3 d => 3 + 10 * of_ldec d
  | D4 d => 4 + 10 * of_ldec d
  | D5 d => 5 + 10 * of_ldec d
  | D6 d => 6 + 10 * of_ldec d
  | D7 d => 7 + 10 * of_ldec d
  | D8 d => 8 + 10 * of_ldec d
  | D9 d => 9 + 10 * of_ldec d
  end.

(* And a one-line characterisation based on [hd] and [tl] helper
   functions. *)

Definition hd d :=
 match d with
 | Stop => 0
 | D0 _ => 0
 | D1 _ => 1
 | D2 _ => 2
 | D3 _ => 3
 | D4 _ => 4
 | D5 _ => 5
 | D6 _ => 6
 | D7 _ => 7
 | D8 _ => 8
 | D9 _ => 9
end.

Definition tl d :=
 match d with
 | Stop => d
 | D0 d => d
 | D1 d => d
 | D2 d => d
 | D3 d => d
 | D4 d => d
 | D5 d => d
 | D6 d => d
 | D7 d => d
 | D8 d => d
 | D9 d => d
end.

Lemma of_ldec_eqn d :
 of_ldec d = hd d + 10 * of_ldec (tl d).
Proof.
 induction d; simpl; auto.
Qed.

Fixpoint dec_size (d:dec) : nat :=
  match d with
  | Stop => 0
  | D0 d => S (dec_size d)
  | D1 d => S (dec_size d)
  | D2 d => S (dec_size d)
  | D3 d => S (dec_size d)
  | D4 d => S (dec_size d)
  | D5 d => S (dec_size d)
  | D6 d => S (dec_size d)
  | D7 d => S (dec_size d)
  | D8 d => S (dec_size d)
  | D9 d => S (dec_size d)
  end.

Lemma little_succ d :
 of_ldec (Little.succ d) = S (of_ldec d).
Proof.
 induction d; simpl; trivial. omega.
Qed.

Lemma of_to_little n :
 of_ldec (to_ldec n) = n.
Proof.
 induction n; simpl; trivial. rewrite little_succ. now f_equal.
Qed.

Ltac helper IH t :=
  rewrite IH;
  rewrite (of_ldec_eqn t); simpl hd; simpl tl;
  rewrite Nat.mul_add_distr_r, Nat.add_assoc; f_equal; [|ring];
  symmetry; apply IH.

Lemma of_ldec_rev d d' :
of_ldec (rev d d') =
 of_ldec (rev d Stop) + of_ldec d' * 10^dec_size d.
Proof.
 revert d'.
 induction d; intros; simpl dec_size; rewrite ?Nat.pow_succ_r'; simpl rev.
 - simpl. omega.
 - helper IHd (D0 d').
 - helper IHd (D1 d').
 - helper IHd (D2 d').
 - helper IHd (D3 d').
 - helper IHd (D4 d').
 - helper IHd (D5 d').
 - helper IHd (D6 d').
 - helper IHd (D7 d').
 - helper IHd (D8 d').
 - helper IHd (D9 d').
Qed.

Lemma of_dec_acc_spec n d :
of_dec_acc d n = of_ldec (rev d Stop) + n * 10^dec_size d.
Proof.
 revert n. induction d; intros;
  simpl of_dec_acc; rewrite ?TailNat.mul_spec, ?IHd;
  simpl rev; simpl dec_size; rewrite ?Nat.pow_succ_r'.
 - simpl. omega.
 - rewrite (of_ldec_rev d (D0 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D1 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D2 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D3 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D4 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D5 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D6 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D7 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D8 Stop)). simpl of_ldec. ring.
 - rewrite (of_ldec_rev d (D9 Stop)). simpl of_ldec. ring.
Qed.

Lemma rev_rev d1 d2 :
 rev (rev d1 d2) Stop = rev d2 d1.
Proof.
 revert d2.
 induction d1; simpl; auto; intros; now rewrite IHd1.
Qed.

Lemma of_to (n:nat) : of_dec (to_dec n) = n.
Proof.
unfold of_dec, to_dec.
rewrite to_little_dec_alt.
rewrite of_dec_acc_spec.
rewrite Nat.mul_0_l, Nat.add_0_r.
rewrite rev_rev. simpl. apply of_to_little.
Qed.

(** The other direction *)

Fixpoint lnorm d :=
 match d with
 | Stop => Stop
 | D0 d => match lnorm d with Stop => Stop | d' => D0 d' end
 | D1 d => D1 (lnorm d)
 | D2 d => D2 (lnorm d)
 | D3 d => D3 (lnorm d)
 | D4 d => D4 (lnorm d)
 | D5 d => D5 (lnorm d)
 | D6 d => D6 (lnorm d)
 | D7 d => D7 (lnorm d)
 | D8 d => D8 (lnorm d)
 | D9 d => D9 (lnorm d)
 end.

Lemma to_tenfold n : n<>0 ->
 to_ldec (10 * n) = D0 (to_ldec n).
Proof.
 induction n.
 - simpl. now destruct 1.
 - intros _.
   destruct (Nat.eq_dec n 0) as [->|H]; simpl; auto.
   rewrite !Nat.add_succ_r.
   simpl.
   change (Nat.iter 10 Little.succ (to_ldec (10*n))
           = D0 (Little.succ (to_ldec n))).
   rewrite (IHn H).
   destruct (to_ldec n); simpl; auto.
Qed.

Lemma of_ldec_0 d : of_ldec d = 0 <-> lnorm d = Stop.
Proof.
 induction d; rewrite of_ldec_eqn; simpl hd; simpl tl; try easy.
 rewrite Nat.add_0_l.
 split; intros.
 - apply Nat.eq_mul_0_r in H; auto. rewrite IHd in H. simpl.
   now rewrite H.
 - simpl in H. destruct (lnorm d); try discriminate.
   destruct IHd as [_ ->]; auto.
Qed.

Lemma to_of_little_tenfold d :
 to_ldec (of_ldec d) = lnorm d ->
 to_ldec (10 * of_ldec d) = lnorm (D0 d).
Proof.
 intro IH.
 destruct (Nat.eq_dec (of_ldec d) 0) as [H|H].
 - rewrite H. simpl. rewrite of_ldec_0 in H. now rewrite H.
 - rewrite to_tenfold; auto. rewrite IH. simpl.
   rewrite of_ldec_0 in H.
   destruct (lnorm d); now simpl.
Qed.

Ltac helper2 :=
 rewrite of_ldec_eqn; simpl hd; simpl tl;
 rewrite ?Nat.add_succ_l, Nat.add_0_l, ?to_ldec_succ,
  to_of_little_tenfold by assumption;
 simpl; destruct lnorm; auto.

Lemma to_of_little d : to_ldec (of_ldec d) = lnorm d.
Proof.
 induction d; try helper2. simpl; auto.
Qed.

Lemma norm_rev_0 d d' : lnorm d = Stop -> norm (rev d d') = norm d'.
Proof.
 revert d'.
 induction d; intros; auto; try discriminate.
 simpl in *.
 destruct (lnorm d) eqn:Eq; try discriminate.
 now rewrite IHd.
Qed.

Lemma dec_stop d : { d = Stop } + { d <> Stop }.
Proof.
 destruct d; (now left) || (now right).
Qed.

Lemma norm_rev d d' : lnorm d <> Stop ->
 norm (rev d d') = rev (lnorm d) d'.
Proof.
 revert d'.
 induction d; intros d' H; simpl in *.
 - now destruct H.
 - destruct (lnorm d) eqn:Eq;
    (now destruct H) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
 - destruct (lnorm d) eqn:Eq;
    (now rewrite norm_rev_0) || (now rewrite IHd).
Qed.

Lemma lnorm_rev d :
  rev (lnorm (rev d Stop)) Stop = norm d.
Proof.
 generalize (rev_rev d Stop). simpl.
 intros Eq. rewrite <- Eq at 2.
 destruct (dec_stop (lnorm (rev d Stop))) as [H|H].
 - rewrite H. simpl. rewrite norm_rev_0; auto.
 - rewrite norm_rev; auto.
Qed.

Lemma to_of (d:dec) : to_dec (of_dec d) = norm d.
Proof.
 unfold of_dec, to_dec.
 rewrite of_dec_acc_spec.
 rewrite Nat.mul_0_l, Nat.add_0_r.
 rewrite to_little_dec_alt.
 rewrite to_of_little.
 apply lnorm_rev.
Qed.

Lemma to_dec_surj d : exists n, to_dec n = norm d.
Proof.
 exists (of_dec d). apply to_of.
Qed.

Lemma of_dec_norm d : of_dec (norm d) = of_dec d.
Proof.
 unfold of_dec.
 induction d; simpl; auto.
Qed.

End NatProofs.