
Require Import Lib DeciBis Arith Omega NArith PArith ZArith.
Require Deci DeciProofs.

Open Scope list_scope.

(** Correctness proofs for the nat conversions for the ad-hoc
    decimal representation : we show an equivalence with the
    first representation with standard lists. *)

Module DeciEquiv.

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

Lemma to_inj (d d':dec) : tolist d = tolist d' -> d = d'.
Proof.
intros.
rewrite <- (from_to d), <- (from_to d'). now f_equal.
Qed.

End DeciEquiv.

Module NatProofs.

Import DecNat DeciEquiv.

(** Equivalence between [Deci.DecNat.dec2nat] and
    [DeciBis.DecNat.dec2nat] *)

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

(** Equivalence between [Deci.DecNat.nat2dec] and
    [DeciBis.DecNat.nat2dec] *)

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

(** We now obtain autonomous results about the conversions *)

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

(** Correctness proofs for the N conversions *)

Module NProofs.

(** First, equivalence results... *)

Import DecN DeciEquiv.
Open Scope N.

Lemma d2n_to d acc :
 d2n d acc = Deci.DecN.d2n (tolist d) acc.
Proof.
 revert acc.
 induction d; simpl; auto.
Qed.

Lemma dec2n_to d : dec2n d = Deci.DecN.dec2n (tolist d).
Proof.
 unfold dec2n. apply d2n_to.
Qed.

Lemma n2d_to n acc c :
 tolist (n2d n acc c) = Deci.DecN.n2d n (tolist acc) c.
Proof.
 revert n acc.
 induction c; auto.
 - intros; destruct n; auto.
   simpl. destruct N.pos_div_eucl.
   rewrite IHc. f_equal.
   destruct n0 as [ |p0]; trivial;
    do 4 (destruct p0 as [p0|p0|]; trivial).
 - intros; destruct n; auto. simpl.
   destruct N.pos_div_eucl.
   rewrite IHc. f_equal.
   destruct n0 as [ |p0]; trivial;
    do 4 (destruct p0 as [p0|p0|]; trivial).
Qed.

Lemma n2dec_to n :
 tolist (n2dec n) = Deci.DecN.n2dec n.
Proof.
 unfold n2dec. apply n2d_to.
Qed.

(** Then autonomous statements *)

Lemma n2dec2n (n:N) : dec2n (n2dec n) = n.
Proof.
 rewrite dec2n_to, n2dec_to.
 apply DeciProofs.NProofs.n2dec2n.
Qed.

Lemma n2dec_inj n n' : n2dec n = n2dec n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (n2dec2n n), <- (n2dec2n n'), EQ.
Qed.

Definition Normal d := norm d = d.

Lemma n2dec_norm n : Normal (n2dec n).
Proof.
 red. apply to_inj. rewrite norm_to.
 rewrite !n2dec_to. apply DeciProofs.NProofs.n2dec_norm.
Qed.

Lemma dec2n2dec (d:dec) :
  n2dec (dec2n d) = norm d.
Proof.
 apply to_inj. rewrite norm_to.
 rewrite n2dec_to, dec2n_to.
 apply DeciProofs.NProofs.dec2n2dec.
Qed.

Lemma dec2n_norm d d' : norm d = norm d' ->
 dec2n d = dec2n d'.
Proof.
 intros EQ. apply n2dec_inj. now rewrite !dec2n2dec.
Qed.

Lemma dec2n_inj d d' :
 dec2n d = dec2n d' -> norm d = norm d'.
Proof.
 intros. rewrite <- !dec2n2dec. now f_equal.
Qed.

Lemma dec2n_iff d d' : dec2n d = dec2n d' <-> norm d = norm d'.
Proof.
 split. apply dec2n_inj. apply dec2n_norm.
Qed.

End NProofs.


(** Correctness proofs for the Positive conversions *)

Module PosProofs.

Import DecPos.

Lemma pos2dec2pos p : dec2pos (pos2dec p) = Some p.
Proof.
 unfold dec2pos, pos2dec.
 now rewrite NProofs.n2dec2n.
Qed.

Lemma dec2pos2dec d p : dec2pos d = Some p -> pos2dec p = norm d.
Proof.
 unfold dec2pos, pos2dec.
 case_eq (DecN.dec2n d); try discriminate.
 intros p' E. injection 1 as ->. rewrite <- E.
 apply NProofs.dec2n2dec.
Qed.

Lemma dec2pos_none d : dec2pos d = None <-> norm d = Stop.
Proof.
 rewrite <- NProofs.dec2n2dec. unfold dec2pos.
 split.
 - now case_eq (DecN.dec2n d).
 - change Stop with (DecN.n2dec 0).
   intros E. apply NProofs.n2dec_inj in E. now rewrite E.
Qed.

End PosProofs.

Module ZProofs.

Import DecZ.
Open Scope Z.

Lemma z2dec2z z : 0<=z -> dec2z (z2dec z) = z.
Proof.
 unfold dec2z, z2dec.
 destruct z; simpl.
 - trivial.
 - now rewrite NProofs.n2dec2n.
 - now destruct 1.
Qed.

Lemma dec2z2dec d : z2dec (dec2z d) = norm d.
Proof.
 unfold z2dec, dec2z.
 case_eq (DecN.dec2n d).
 - rewrite <- NProofs.dec2n2dec. now intros ->.
 - intros p <-. apply NProofs.dec2n2dec.
Qed.

End ZProofs.

(** Proofs concerning [DeciBis.succ] *)

Import DeciEquiv.

Lemma bounded_succ_equiv d :
  match DeciBis.bounded_succ d, Deci.bounded_succ (tolist d) with
  | Carry d, Carry l => l = tolist d
  | NoCarry d, NoCarry l => l = tolist d
  | _, _=> False
  end.
Proof.
 induction d; simpl; auto;
 destruct bounded_succ, Deci.bounded_succ; simpl; subst; intuition.
Qed.

Lemma succ_equiv d :
  tolist (DeciBis.succ d) = Deci.succ (tolist d).
Proof.
 unfold succ, Deci.succ.
 generalize (bounded_succ_equiv d).
 destruct bounded_succ, Deci.bounded_succ; simpl; intuition.
 now subst.
Qed.

Lemma succ_equiv' d :
  fromlist (Deci.succ d) = DeciBis.succ (fromlist d).
Proof.
 rewrite <- (to_from d) at 1.
 rewrite <- succ_equiv.
 apply from_to.
Qed.

Lemma lt_equiv d d' :
 DeciBis.lt d d' <-> Deci.lt (tolist d) (tolist d').
Proof.
 split.
 - induction 1.
   + rewrite succ_equiv. apply Deci.Succ.
   + eapply Deci.Trans; eauto.
 - rewrite <- (from_to d) at 2.
   rewrite <- (from_to d') at 2.
   induction 1.
   + rewrite succ_equiv'. apply DeciBis.Succ.
   + eapply DeciBis.Trans; eauto.
Qed.

Lemma lt_equiv' d d' :
 Deci.lt d d' <-> DeciBis.lt (fromlist d) (fromlist d').
Proof.
 now rewrite lt_equiv, !to_from.
Qed.
