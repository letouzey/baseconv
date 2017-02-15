
Require Import Lib DeciTer Arith Omega NArith PArith ZArith.


Lemma rev_rev d1 d2 :
 rev (rev d1 d2) Stop = rev d2 d1.
Proof.
 revert d2.
 induction d1; simpl; auto; intros; now rewrite IHd1.
Qed.

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

(** Normalization on little-endian numbers *)
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

Module NatProofs.

Import DecNat.

(** A few helper functions used during proofs *)

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

(** A direct definition of [to_little_dec], non tail-recursive *)
Fixpoint to_ldec n :=
 match n with
 | 0 => Stop
 | S n => Little.succ (to_ldec n)
 end.

(** A direct definition of little-endian [of_dec] *)
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


(** Properties of [to_ldec] *)

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

Lemma to_dec_alt n :
 to_dec n = rev (to_ldec n) Stop.
Proof.
 unfold to_dec. f_equal. apply to_little_dec_alt.
Qed.

Lemma to_ldec_succ n : to_ldec (S n) = Little.succ (to_ldec n).
Proof.
 reflexivity.
Qed.

(** Properties of [of_ldec] *)

Lemma of_ldec_eqn d :
 of_ldec d = hd d + 10 * of_ldec (tl d).
Proof.
 induction d; simpl; auto.
Qed.

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

Lemma of_dec_alt d : of_dec d = of_ldec (rev d Stop).
Proof.
 unfold of_dec.
 rewrite of_dec_acc_spec. auto.
Qed.

(** First main bijection result *)

Lemma of_to (n:nat) : of_dec (to_dec n) = n.
Proof.
 rewrite to_dec_alt, of_dec_alt, rev_rev. simpl.
 apply of_to_little.
Qed.

(** The other direction *)

Lemma to_ldec_tenfold n : n<>0 ->
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
 - rewrite to_ldec_tenfold; auto. rewrite IH. simpl.
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

(** Second bijection results *)

Lemma to_of (d:dec) : to_dec (of_dec d) = norm d.
Proof.
 rewrite to_dec_alt, of_dec_alt.
 rewrite to_of_little.
 apply lnorm_rev.
Qed.

(** Usual consequences *)

Lemma to_dec_inj n n' : to_dec n = to_dec n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (of_to n), <- (of_to n'), EQ.
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

Lemma of_inj d d' :
 of_dec d = of_dec d' -> norm d = norm d'.
Proof.
 intros. rewrite <- !to_of. now f_equal.
Qed.

Lemma of_iff d d' : of_dec d = of_dec d' <-> norm d = norm d'.
Proof.
 split. apply of_inj. intros E. rewrite <- of_dec_norm, E.
 apply of_dec_norm.
Qed.

End NatProofs.


(** Conversion results with respect to positive and N *)

Module PosProofs.
Import DecPos.
Local Open Scope positive.

(** A direct definition of little-endian [of_dec] *)

Fixpoint of_ldec (d:dec) : N :=
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
end%N.

Lemma of_ldec_eqn d :
 (of_ldec d = hd d + 10 * (of_ldec (tl d)))%N.
Proof.
 induction d; simpl; auto.
Qed.

Fixpoint dec_size (d:dec) : N :=
  match d with
  | Stop => 0
  | D0 d => N.succ (dec_size d)
  | D1 d => N.succ (dec_size d)
  | D2 d => N.succ (dec_size d)
  | D3 d => N.succ (dec_size d)
  | D4 d => N.succ (dec_size d)
  | D5 d => N.succ (dec_size d)
  | D6 d => N.succ (dec_size d)
  | D7 d => N.succ (dec_size d)
  | D8 d => N.succ (dec_size d)
  | D9 d => N.succ (dec_size d)
  end.

Ltac helper IH f d n :=
  rewrite 2 (IH (f _));
  change (of_ldec (f d)) with (n + 10 * (of_ldec d))%N;
  simpl (of_ldec (f _)); ring.

Lemma of_ldec_rev d d' :
(of_ldec (rev d d') =
  of_ldec (rev d Stop) + of_ldec d' * 10^dec_size d)%N.
Proof.
 revert d'.
 induction d; simpl; intros; rewrite ?N.pow_succ_r'.
 - ring.
 - helper IHd D0 d' (0%N).
 - helper IHd D1 d' (1%N).
 - helper IHd D2 d' (2%N).
 - helper IHd D3 d' (3%N).
 - helper IHd D4 d' (4%N).
 - helper IHd D5 d' (5%N).
 - helper IHd D6 d' (6%N).
 - helper IHd D7 d' (7%N).
 - helper IHd D8 d' (8%N).
 - helper IHd D9 d' (9%N).
Qed.

Ltac helper2 IH n d acc :=
  change (of_dec_acc _ _) with (of_dec_acc d (n + 10 * acc));
  rewrite IH;
  change (N.pos (n + 10*acc)) with (Npos n + 10 * N.pos acc)%N; ring.

Lemma of_dec_acc_rev d acc :
 (Npos (of_dec_acc d acc) =
   of_ldec (rev d Stop) + (Npos acc) * 10^dec_size d)%N.
Proof.
 revert acc.
 induction d; intros; simpl dec_size; rewrite ?N.pow_succ_r';
  simpl rev; try rewrite of_ldec_rev; simpl of_ldec.
 - simpl. f_equal. symmetry. apply Pos.mul_1_r.
 - change (of_dec_acc _ _) with (of_dec_acc d (10 * acc)).
   rewrite IHd.
   change (N.pos (10*acc)) with (10 * N.pos acc)%N. ring.
 - helper2 IHd 1 d acc.
 - helper2 IHd 2 d acc.
 - helper2 IHd 3 d acc.
 - helper2 IHd 4 d acc.
 - helper2 IHd 5 d acc.
 - helper2 IHd 6 d acc.
 - helper2 IHd 7 d acc.
 - helper2 IHd 8 d acc.
 - helper2 IHd 9 d acc.
Qed.

Lemma of_dec_rev d : of_dec d = of_ldec (rev d Stop).
Proof.
 induction d; simpl; auto; rewrite of_ldec_rev; simpl of_ldec;
  try (rewrite of_dec_acc_rev); auto.
 simpl. rewrite IHd. ring.
Qed.

Lemma of_dec_rev' d : of_dec (rev d Stop) = of_ldec d.
Proof.
 rewrite of_dec_rev. now rewrite rev_rev.
Qed.

Ltac helper3 IH :=
 simpl Little.double; simpl Little.succ_double;
 do 3 (rewrite (of_ldec_eqn (_ _)); simpl hd; simpl tl; rewrite ?IH);
 split;ring.

Lemma of_double_gen d :
  of_ldec (Little.double d) = N.double (of_ldec d) /\
  of_ldec (Little.succ_double d) = N.succ_double (of_ldec d).
Proof.
 rewrite N.double_spec, N.succ_double_spec.
 induction d; try destruct IHd as (IH1,IH2).
 - simpl; auto.
 - simpl. rewrite IH1. destruct (of_ldec d); simpl; auto.
 - simpl. rewrite IH1. destruct (of_ldec d); simpl; auto.
 - simpl. rewrite IH1. destruct (of_ldec d); simpl; auto.
 - simpl. rewrite IH1. destruct (of_ldec d); simpl; auto.
 - simpl. rewrite IH1. destruct (of_ldec d); simpl; auto.
 - helper3 IH2.
 - helper3 IH2.
 - helper3 IH2.
 - helper3 IH2.
 - helper3 IH2.
Qed.

Lemma of_double d :
  of_ldec (Little.double d) = N.double (of_ldec d).
Proof.
 apply of_double_gen.
Qed.

Lemma of_succ_double d :
  of_ldec (Little.succ_double d) = N.succ_double (of_ldec d).
Proof.
 apply of_double_gen.
Qed.

Lemma of_to (p:positive) : of_dec (to_dec p) = Npos p.
Proof.
 unfold to_dec.
 rewrite of_dec_rev'.
 induction p; simpl; auto.
 - now rewrite of_succ_double, IHp.
 - now rewrite of_double, IHp.
Qed.

(** The other direction *)

Definition to_ldec n :=
  match n with
  | N0 => Stop
  | Npos p => to_dec_rev p
  end.

Lemma succ_double_alt d :
  Little.succ_double d = Little.succ (Little.double d).
Proof.
 induction d; simpl; auto.
Qed.

Lemma double_succ d :
  Little.double (Little.succ d) =
  Little.succ (Little.succ_double d).
Proof.
 induction d; simpl; f_equal; auto using succ_double_alt.
Qed.

Lemma to_ldec_succ n :
 to_ldec (N.succ n) = Little.succ (to_ldec n).
Proof.
 destruct n; simpl; auto.
 induction p; simpl; rewrite ?IHp;
  auto using succ_double_alt, double_succ.
Qed.

Ltac tac_iter n f i :=
 match eval compute in n with
 | N0 => let x:=i in x
 | _ => tac_iter (N.pred n) f (f i)
 end.

Lemma to_ldec_tenfold p :
 to_ldec (10 * (Npos p)) = D0 (to_ldec (Npos p)).
Proof.
 induction p using Pos.peano_rect.
 - simpl; auto.
 - change (N.pos (Pos.succ p)) with (N.succ (N.pos p)).
   rewrite N.mul_succ_r.
   let n := tac_iter 10%N N.succ N0 in
   change 10%N at 2 with n.
   rewrite !N.add_succ_r, N.add_0_r.
   rewrite !to_ldec_succ.
   rewrite IHp.
   destruct (to_ldec (N.pos p)); simpl; auto.
Qed.

Lemma of_ldec_0 d : of_ldec d = 0%N <-> lnorm d = Stop.
Proof.
 induction d; rewrite of_ldec_eqn; simpl hd; simpl tl; try easy.
 - rewrite N.add_0_l.
   split; intros.
   + apply N.eq_mul_0_r in H. rewrite IHd in H. simpl.
     now rewrite H. easy.
   + simpl in H. destruct (lnorm d); try discriminate.
     destruct IHd as [_ ->]; auto.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
 - split. omega with *. easy.
Qed.

Lemma to_of_little_tenfold d :
 to_ldec (of_ldec d) = lnorm d ->
 to_ldec (10 * of_ldec d) = lnorm (D0 d).
Proof.
 intro IH.
 destruct (N.eq_dec (of_ldec d) 0) as [H|H].
 - rewrite H. simpl. rewrite of_ldec_0 in H. now rewrite H.
 - destruct (of_ldec d) eqn:Eq; [easy| ].
   rewrite to_ldec_tenfold; auto. rewrite IH. simpl.
   rewrite <- Eq in H. rewrite of_ldec_0 in H.
   destruct (lnorm d); now simpl.
Qed.

Ltac helper4 n :=
 rewrite of_ldec_eqn; simpl hd; simpl tl;
 let n' := tac_iter n N.succ N0 in
 change n with n';
 rewrite ?N.add_succ_l, N.add_0_l, ?to_ldec_succ,
  to_of_little_tenfold by assumption;
 simpl; destruct lnorm; auto.

Lemma to_of_little d : to_ldec (of_ldec d) = lnorm d.
Proof.
 induction d.
 - simpl; auto.
 - helper4 0%N.
 - helper4 1%N.
 - helper4 2%N.
 - helper4 3%N.
 - helper4 4%N.
 - helper4 5%N.
 - helper4 6%N.
 - helper4 7%N.
 - helper4 8%N.
 - helper4 9%N.
Qed.

(** Second bijection results *)

Lemma to_of (d:dec) : DecN.to_dec (of_dec d) = norm d.
Proof.
 rewrite of_dec_rev.
 unfold DecN.to_dec, to_dec.
 destruct (of_ldec (rev d Stop)) eqn:H.
 - rewrite of_ldec_0 in H. rewrite <- lnorm_rev. now rewrite H.
 - change (to_dec_rev p) with (to_ldec (N.pos p)).
   rewrite <- H. rewrite to_of_little. apply lnorm_rev.
Qed.

End PosProofs.

Module NProofs.

Import DecN.

Lemma of_to (n:N) : of_dec (to_dec n) = n.
Proof.
 destruct n.
 - simpl; auto.
 - apply PosProofs.of_to.
Qed.

Lemma to_of (d:dec) : to_dec (of_dec d) = norm d.
Proof.
 exact (PosProofs.to_of d).
Qed.

End NProofs.


(** Proofs about [Deci.succ] *)

Import DecNat NatProofs.

Lemma succ_to n :
 succ (to_dec n) = to_dec (S n).
Proof.
 unfold to_dec.
 unfold succ. f_equal. rewrite rev_rev. simpl rev.
 rewrite !to_little_dec_alt.
 apply to_ldec_succ.
Qed.

Lemma lsucc_lnorm d :
 lnorm (Little.succ d) = Little.succ (lnorm d).
Proof.
 induction d; simpl; auto.
 - destruct (lnorm d); simpl; auto.
 - rewrite IHd. destruct (lnorm d); simpl; auto.
Qed.

Lemma succ_norm d :
 norm (succ d) = succ (norm d).
Proof.
 unfold succ. rewrite <- !lnorm_rev, !rev_rev; simpl.
 f_equal. apply lsucc_lnorm.
Qed.

Lemma of_succ d :
  of_dec (succ d) = S (of_dec d).
Proof.
 apply to_dec_inj.
 rewrite <- succ_to. rewrite !to_of.
 apply succ_norm.
Qed.

Lemma succ_inj d d' :
 succ d = succ d' -> norm d = norm d'.
Proof.
 intros. apply of_inj.
 assert (E : S (of_dec d) = S (of_dec d')).
 { rewrite <- !of_succ. now f_equal. }
 now injection E.
Qed.

(** Proofs about [Deci.lt] *)

Lemma to_lt n n' : n < n' -> lt (to_dec n) (to_dec n').
Proof.
 induction 1.
 + rewrite <- succ_to. apply Succ.
 + apply Trans with (to_dec m); trivial.
   rewrite <- succ_to. apply Succ.
Qed.

Lemma of_lt d d' : lt d d' -> of_dec d < of_dec d'.
Proof.
 induction 1.
 + rewrite of_succ. auto.
 + omega.
Qed.

Lemma to_lt_iff n n' :  n < n' <-> lt (to_dec n) (to_dec n').
Proof.
 split; [apply to_lt|].
 intros H. apply of_lt in H. now rewrite !of_to in H.
Qed.

Lemma of_lt_iff d d' :
  of_dec d < of_dec d' <-> lt (norm d) (norm d').
Proof.
 rewrite to_lt_iff. now rewrite !to_of.
Qed.

Lemma lt_norm d d' : lt d d' -> lt (norm d) (norm d').
Proof.
 rewrite <- of_lt_iff. apply of_lt.
Qed.

Lemma lt_irrefl d d' : lt d d' -> norm d <> norm d'.
Proof.
 intros L E.
 apply of_lt in L.
 rewrite <- of_iff in E.
 omega.
Qed.

Lemma lt_antisym d d' : lt d d' -> ~lt d' d.
Proof.
 intros L L'. apply of_lt in L. apply of_lt in L'. omega.
Qed.

Lemma lt_trans d1 d2 d3 : lt d1 d2 -> lt d2 d3 -> lt d1 d3.
Proof.
 apply Trans.
Qed.

Lemma lt_norm_total d d' :
 { lt (norm d) (norm d') } + { norm d = norm d' } + { lt (norm d') (norm d) }.
Proof.
 destruct (CompareSpec2Type (Nat.compare_spec (of_dec d) (of_dec d'))).
 - left; right. now apply of_inj.
 - left; left. now apply of_lt_iff.
 - right; now apply of_lt_iff.
Qed.
