
Require Import Lib Hexa Arith Omega NArith PArith ZArith.

Open Scope list_scope.

(** Correctness proofs for the nat conversions *)

Module NatProofs.

Import HexNat.

Lemma nat2digit2nat n : n < 16 -> digit2nat (nat2digit n) = n.
Proof.
 destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|]]]]]]]]]]]]]]]]; auto; omega.
Qed.

Lemma digit2nat2digit d : nat2digit (digit2nat d) = d.
Proof.
 now destruct d.
Qed.

Lemma h2n_eqn dg d acc :
  h2n (dg::d) acc =
  h2n d (digit2nat dg + 16 * acc).
Proof.
 rewrite <- TailNat.addmul_spec.
 reflexivity.
Qed.

Lemma n2h_eqn n acc count :
  n2h (S n) acc (S count) =
  n2h (S n / 16) (nat2digit (S n mod 16) :: acc) count.
Proof.
 change (n2h (S n) acc (S count)) with
 (let (q,r) := diveucl (S n) 16 in n2h q (nat2digit r :: acc) count).
 now rewrite diveucl_spec.
Qed.

Lemma n2h_eqn' n acc count :
  n2h n acc (S count) =
  if n =? 0 then acc
  else
   n2h (n/16) (nat2digit (n mod 16) :: acc) count.
Proof.
 destruct n. trivial. apply n2h_eqn.
Qed.

Lemma n2h_length n acc count :
  length acc <= length (n2h n acc count).
Proof.
 revert n acc.
 induction count; auto; destruct n; auto.
 intros.
 rewrite n2h_eqn.
 etransitivity; [| eapply IHcount]. simpl. auto.
Qed.

Lemma h2n_add d n p :
 h2n d (n+p) = h2n d n + p * 16^length d.
Proof.
 revert n p.
 induction d.
 - simpl; auto with arith.
 - intros. rewrite !h2n_eqn.
   rewrite Nat.mul_add_distr_l, Nat.add_assoc, IHd.
   f_equal. simpl length.
   rewrite Nat.pow_succ_r', Nat.mul_assoc. f_equal.
   apply Nat.mul_comm.
Qed.

Lemma h2n_alt d acc : h2n d acc = hex2nat d + acc * 16^length d.
Proof.
 apply (h2n_add d 0 acc).
Qed.

Lemma n2h_anycount count count' n acc :
 n <= count -> n <= count' ->
 n2h n acc count = n2h n acc count'.
Proof.
 revert count' n acc.
 induction count; destruct count'; auto.
 - now inversion 1.
 - now inversion 2.
 - intros.
   destruct n; auto.
   rewrite !n2h_eqn.
   destruct (Nat.le_gt_cases 16 (S n)).
   * apply IHcount; apply Nat.div_le_upper_bound; omega.
   * rewrite Nat.div_small; auto. now destruct count, count'.
Qed.

Lemma n2h_mincount count n acc :
 n <= count -> n2h n acc count = n2h n acc n.
Proof.
 intros. now apply n2h_anycount.
Qed.

Lemma n2h_app n d d' count :
 n <= count ->
 n2h n (d++d') count = n2h n d count ++ d'.
Proof.
 revert n d d'.
 induction count.
 - now inversion 1.
 - intros. destruct n.
   + auto.
   + rewrite !n2h_eqn.
     generalize (nat2digit (S n mod 16)); intros dg.
     change (dg :: d ++ d') with ((dg::d)++d').
     destruct (Nat.le_gt_cases 16 (S n)).
     * apply IHcount.
       apply Nat.div_le_upper_bound; omega.
     * rewrite Nat.div_small; simpl; auto.
       destruct count; auto.
Qed.

Lemma n2h_alt n acc count :
 n <= count ->
 n2h n acc count = nat2hex n ++ acc.
Proof.
 intros.
 unfold nat2hex. rewrite (n2h_anycount n count); auto.
 now apply (n2h_app n nil).
Qed.

(*
<n0><... n ...>|d0|
<n0>|      d      |
*)

Lemma n2h2n count n n0 n1 (d0 d : hex) :
 n <= count ->
 d = n2h n d0 count ->
 n1 = n0 * 16^(length d - length d0) ->
 h2n d n0 =
 h2n d0 (n1 + n).
Proof.
 revert n n0 n1 d0 d.
 induction count.
 - inversion 1. simpl. intros; subst. f_equal.
   rewrite Nat.sub_diag. simpl. omega.
 - intros n n0 n1 d0 d LE D N1.
   destruct n.
   + simpl in *. subst. f_equal.
     rewrite Nat.sub_diag. simpl. omega.
   + rewrite n2h_eqn in D.
     remember (S n) as Sn.
     destruct (Nat.le_gt_cases 16 Sn).
     * assert (Sn / 16 <= count).
       { apply Nat.div_le_upper_bound; omega. }
       remember (nat2digit (Sn mod 16)) as dg.
       specialize (IHcount (Sn / 16) n0
                           (n0 * 16 ^ (length d - S (length d0)))
                           (dg::d0) d H0 D eq_refl).
       rewrite h2n_eqn in IHcount.
       rewrite IHcount.
       f_equal.
       subst n1.
       rewrite Nat.mul_add_distr_l.
       rewrite Nat.mul_shuffle3.
       assert (LE' := n2h_length (Sn / 16) (dg :: d0) count).
       rewrite <- D in LE'. simpl in LE'.
       rewrite <- Nat.pow_succ_r; try omega.
       rewrite Nat.add_shuffle3.
       f_equal.
       { f_equal; f_equal. omega. }
       { subst dg. rewrite nat2digit2nat; auto using Nat.mod_upper_bound.
         rewrite Nat.add_comm. symmetry. apply Nat.div_mod; auto. }
     * rewrite Nat.div_small in D by auto.
       rewrite Nat.mod_small in D by auto.
       rewrite n2h_mincount in D by omega. simpl in D.
       subst d.
       rewrite h2n_eqn. f_equal.
       rewrite nat2digit2nat by auto.
       rewrite Nat.add_comm. f_equal.
       subst n1. simpl length.
       replace (S (length d0) - length d0) with 1 by omega.
       simpl; omega.
Qed.

Lemma nat2hex2nat (n:nat) : hex2nat (nat2hex n) = n.
Proof.
 unfold hex2nat.
 remember (nat2hex n) as d.
 change n with (h2n nil (0+n)).
 apply (n2h2n n); auto.
Qed.

Lemma nat2hex_inj n n' : nat2hex n = nat2hex n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (nat2hex2nat n), <- (nat2hex2nat n'), EQ.
Qed.

Lemma n2h_spec dg p d count :
 norm (n2h (digit2nat dg + 16*p) d (S count)) =
 norm (n2h p (dg::d) count).
Proof.
 rewrite n2h_eqn'.
 case Nat.eqb_spec; intros.
 - destruct dg; try discriminate. simpl digit2nat in e.
   replace p with 0 by omega.
   now destruct count.
 - f_equal. f_equal.
   + rewrite Nat.mul_comm, Nat.div_add, Nat.div_small; auto.
     destruct dg; simpl; omega.
   + f_equal.
     rewrite Nat.mul_comm, Nat.mod_add, Nat.mod_small; auto.
     apply digit2nat2digit.
     destruct dg; simpl; omega.
Qed.

(*
<n0>|      d      |d0|
<...        n ...>|d0|
*)

Lemma d2n2d count n n0 (d0 d : hex) :
 n <= count ->
 n = h2n d n0 ->
 norm (n2h n d0 count) =
 norm (n2h n0 (d ++ d0) count).
Proof.
 revert count n n0 d0.
 induction d.
 - intros. simpl in *. now subst.
 - intros count n n0 d0 LT EQ.
   assert (LE' : n <= S count) by omega.
   rewrite (n2h_anycount count (S count)) by auto.
   rewrite h2n_eqn in EQ.
   rewrite (IHd _ _ _ d0 LE' EQ).
   now rewrite n2h_spec.
Qed.

Definition Normal d := norm d = d.

Lemma n2h_norm n count acc :
 0<n<=count -> Normal (n2h n acc count).
Proof.
 revert n acc.
 induction count.
 - intros. omega.
 - intros. destruct n. omega.
   rewrite n2h_eqn.
   destruct (Nat.le_gt_cases 16 (S n)).
   + apply IHcount.
     split. apply Nat.div_str_pos. omega.
     apply Nat.div_le_upper_bound; omega.
   + rewrite Nat.div_small by auto.
     rewrite Nat.mod_small by auto.
     rewrite n2h_mincount by omega.
     remember (nat2digit (S n)) as dg.
     simpl. destruct dg; red; auto.
     generalize (nat2digit2nat (S n) H0).
     rewrite <- Heqdg; simpl. discriminate.
Qed.

Lemma nat2hex_norm n : Normal (nat2hex n).
Proof.
 destruct n.
 - red; auto.
 - apply n2h_norm; omega.
Qed.

Lemma hex2nat2hex (d:hex) :
  nat2hex (hex2nat d) = norm d.
Proof.
 rewrite <- (nat2hex_norm (hex2nat d)).
 unfold nat2hex.
 rewrite d2n2d with (n0:=0)(d:=d); auto.
 rewrite List.app_nil_r.
 rewrite n2h_mincount; auto with arith.
Qed.

Lemma hex2nat_norm d d' : norm d = norm d' ->
 hex2nat d = hex2nat d'.
Proof.
 intros EQ. apply nat2hex_inj. now rewrite !hex2nat2hex.
Qed.

Lemma hex2nat_inj d d' :
 hex2nat d = hex2nat d' -> norm d = norm d'.
Proof.
 intros. rewrite <- !hex2nat2hex. now f_equal.
Qed.

Lemma hex2nat_iff d d' : hex2nat d = hex2nat d' <-> norm d = norm d'.
Proof.
 split. apply hex2nat_inj. apply hex2nat_norm.
Qed.

Lemma nat2hex_eqn n m : n < 16 -> m<>0 ->
 nat2hex (n + 16*m) = nat2hex m ++ nat2digit n::nil.
Proof.
 intros.
 unfold nat2hex.
 rewrite <- n2h_app by auto. simpl app.
 case_eq (n+16*m); [omega|intros p Hp].
 rewrite n2h_eqn.
 rewrite <- Hp.
 rewrite <- Nat.div_unique with (q:=m)(r:=n); auto with arith.
 rewrite <- Nat.mod_unique with (q:=m)(r:=n); auto with arith.
 apply n2h_anycount; auto. omega.
Qed.

Lemma nat2hex_eqn' dg n acc : n<>0 ->
 nat2hex n ++ dg :: acc = nat2hex (digit2nat dg + 16*n) ++ acc.
Proof.
 intros.
 change (dg::acc) with ((dg::nil) ++ acc).
 rewrite <- List.app_ass. f_equal.
 rewrite nat2hex_eqn; auto.
 now rewrite digit2nat2digit.
 destruct dg; simpl; omega.
Qed.

End NatProofs.


(** Correctness proofs for the N conversions *)

Module NProofs.

Import HexN.
Open Scope N.

(** We first state that these N conversions behave like
    the nat conversions *)

Lemma h2p_nat h acc :
 N.pos (h2p h acc) = N.of_nat (HexNat.h2n h (Pos.to_nat acc)).
Proof.
 revert acc.
 induction h as [|d h IH].
 - intros. simpl. now rewrite positive_nat_N.
 - intros.
   destruct d; rewrite NatProofs.h2n_eqn; simpl h2p;
   rewrite IH; f_equal; change 16%nat with (Pos.to_nat 16);
   now rewrite <- Pos2Nat.inj_mul.
Qed.

Lemma hex2n_nat h : hex2n h = N.of_nat (HexNat.hex2nat h).
Proof.
 induction h as [|d h IH].
 - auto.
 - destruct d; simpl; rewrite ?h2p_nat; auto.
Qed.

Lemma p2h_nat p acc :
 p2h p acc = HexNat.nat2hex (Pos.to_nat p) ++ acc.
Proof.
 revert p acc.
 fix 1.
 destruct p as [p|p|]; intros; try reflexivity;
  destruct p as [p|p|]; try reflexivity;
   destruct p as [p|p|]; try reflexivity;
    destruct p as [p|p|]; try reflexivity;
     simpl; rewrite p2h_nat;
     rewrite NatProofs.nat2hex_eqn' by
      (generalize (Pos2Nat.is_pos p); omega); f_equal; f_equal;
     simpl HexNat.digit2nat;
     repeat (rewrite Pos2Nat.inj_xI || rewrite Pos2Nat.inj_xO); omega.
Qed.

Lemma n2hex_nat n : n2hex n = HexNat.nat2hex (N.to_nat n).
Proof.
 destruct n. auto.
 simpl.
 rewrite p2h_nat. apply List.app_nil_r.
Qed.

(** We now state direct correctness results over the N conversions *)

Lemma n2hex2n (n:N) : hex2n (n2hex n) = n.
Proof.
 now rewrite n2hex_nat, hex2n_nat, NatProofs.nat2hex2nat, N2Nat.id.
Qed.

Lemma n2hex_inj n n' : n2hex n = n2hex n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (n2hex2n n), <- (n2hex2n n'), EQ.
Qed.

Definition Normal d := norm d = d.

Lemma n2hex_norm n : Normal (n2hex n).
Proof.
 rewrite n2hex_nat. apply NatProofs.nat2hex_norm.
Qed.

Lemma hex2n2hex (d:hex) :
  n2hex (hex2n d) = norm d.
Proof.
 now rewrite n2hex_nat, hex2n_nat, Nat2N.id, NatProofs.hex2nat2hex.
Qed.

Lemma hex2n_norm d d' : norm d = norm d' ->
 hex2n d = hex2n d'.
Proof.
 intros EQ. apply n2hex_inj. now rewrite !hex2n2hex.
Qed.

Lemma hex2n_inj d d' :
 hex2n d = hex2n d' -> norm d = norm d'.
Proof.
 intros. rewrite <- !hex2n2hex. now f_equal.
Qed.

Lemma hex2n_iff d d' : hex2n d = hex2n d' <-> norm d = norm d'.
Proof.
 split. apply hex2n_inj. apply hex2n_norm.
Qed.

End NProofs.


(** Correctness proofs for the Positive conversions *)

Module PosProofs.

Import HexPos.

Lemma pos2hex2pos p : hex2pos (pos2hex p) = Some p.
Proof.
 unfold hex2pos, pos2hex.
 change (HexN.p2h p nil) with (HexN.n2hex (Npos p)).
 now rewrite NProofs.n2hex2n.
Qed.

Lemma hex2pos2hex d p : hex2pos d = Some p -> pos2hex p = norm d.
Proof.
 unfold hex2pos, pos2hex.
 change (HexN.p2h p nil) with (HexN.n2hex (Npos p)).
 case_eq (HexN.hex2n d); try discriminate.
 intros p' E. injection 1 as ->. rewrite <- E.
 apply NProofs.hex2n2hex.
Qed.

Lemma hex2pos_none d : hex2pos d = None <-> norm d = nil.
Proof.
 rewrite <- NProofs.hex2n2hex. unfold hex2pos.
 split.
 - now case_eq (HexN.hex2n d).
 - change nil with (HexN.n2hex 0).
   intros E. apply NProofs.n2hex_inj in E. now rewrite E.
Qed.

End PosProofs.

Module ZProofs.

Import HexZ.
Open Scope Z.

Lemma z2hex2z z : 0<=z -> hex2z (z2hex z) = z.
Proof.
 unfold hex2z, z2hex.
 destruct z.
 - trivial.
 - now rewrite NProofs.n2hex2n.
 - now destruct 1.
Qed.

Lemma hex2z2hex d : z2hex (hex2z d) = norm d.
Proof.
 unfold z2hex, hex2z.
 case_eq (HexN.hex2n d).
 - rewrite <- NProofs.hex2n2hex. now intros ->.
 - intros p <-. apply NProofs.hex2n2hex.
Qed.

End ZProofs.

