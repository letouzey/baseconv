
Require Import Lib Deci Arith Omega NArith PArith ZArith.

Open Scope list_scope.

(** Correctness proofs for the nat conversions *)

Module NatProofs.

Import DecNat.

Lemma nat2digit2nat n : n < 10 -> digit2nat (nat2digit n) = n.
Proof.
 destruct n as [|[|[|[|[|[|[|[|[|[|]]]]]]]]]]; auto; omega.
Qed.

Lemma digit2nat2digit d : nat2digit (digit2nat d) = d.
Proof.
 now destruct d.
Qed.

(** A naive version of dec2nat, for the proofs *)
Fixpoint of_dec (d:dec) :=
  match d with
  | nil => 0
  | d :: l => of_dec l + digit2nat d * 10^length l
  end.

Lemma d2n_eqn dg d acc :
  d2n (dg::d) acc =
  d2n d (digit2nat dg + 10 * acc).
Proof.
 rewrite <- TailNat.addmul_spec.
 reflexivity.
Qed.

Lemma d2n_add d n p :
 d2n d (n+p) = d2n d n + p * 10^length d.
Proof.
 revert n p.
 induction d.
 - simpl; auto with arith.
 - intros. rewrite !d2n_eqn.
   rewrite Nat.mul_add_distr_l, Nat.add_assoc, IHd.
   f_equal. simpl length.
   rewrite Nat.pow_succ_r', Nat.mul_assoc. f_equal.
   apply Nat.mul_comm.
Qed.

Lemma d2n_alt d acc : d2n d acc = dec2nat d + acc * 10^length d.
Proof.
 apply (d2n_add d 0 acc).
Qed.

Lemma dec2nat_alt d : dec2nat d = of_dec d.
Proof.
 induction d; simpl; auto.
 unfold dec2nat. simpl.
 rewrite <- IHd. unfold dec2nat. now rewrite <- d2n_add.
Qed.

Lemma n2d_eqn n acc count :
  n2d (S n) acc (S count) =
  n2d (S n / 10) (nat2digit (S n mod 10) :: acc) count.
Proof.
 change (n2d (S n) acc (S count)) with
 (let (q,r) := diveucl (S n) 10 in n2d q (nat2digit r :: acc) count).
 now rewrite diveucl_spec.
Qed.

Lemma n2d_eqn' n acc count :
  n2d n acc (S count) =
  if n =? 0 then acc
  else
   n2d (n/10) (nat2digit (n mod 10) :: acc) count.
Proof.
 destruct n. trivial. apply n2d_eqn.
Qed.

Lemma n2d_anycount count count' n acc :
 n <= count -> n <= count' ->
 n2d n acc count = n2d n acc count'.
Proof.
 revert count' n acc.
 induction count; destruct count'; auto.
 - now inversion 1.
 - now inversion 2.
 - intros.
   destruct n; auto.
   rewrite !n2d_eqn.
   destruct (Nat.le_gt_cases 10 (S n)).
   * apply IHcount; apply Nat.div_le_upper_bound; omega.
   * rewrite Nat.div_small; auto. now destruct count, count'.
Qed.

Lemma n2d_mincount count n acc :
 n <= count -> n2d n acc count = n2d n acc n.
Proof.
 intros. now apply n2d_anycount.
Qed.

Lemma n2d_app n d d' count :
 n <= count ->
 n2d n (d++d') count = n2d n d count ++ d'.
Proof.
 revert n d d'.
 induction count.
 - now inversion 1.
 - intros. destruct n.
   + auto.
   + rewrite !n2d_eqn.
     generalize (nat2digit (S n mod 10)); intros dg.
     change (dg :: d ++ d') with ((dg::d)++d').
     destruct (Nat.le_gt_cases 10 (S n)).
     * apply IHcount.
       apply Nat.div_le_upper_bound; omega.
     * rewrite Nat.div_small; simpl; auto.
       destruct count; auto.
Qed.

Lemma n2d_alt n acc count :
 n <= count ->
 n2d n acc count = nat2dec n ++ acc.
Proof.
 intros.
 unfold nat2dec. rewrite (n2d_anycount n count); auto.
 now apply (n2d_app n nil).
Qed.

Lemma of_dec_app d d' :
  of_dec (d ++ d') =
  of_dec d * 10^length d' + of_dec d'.
Proof.
 induction d; simpl; auto.
 rewrite IHd. rewrite List.app_length, Nat.pow_add_r.
 ring.
Qed.

Lemma nat2dec2nat n :
 dec2nat (nat2dec n) = n.
Proof.
 rewrite dec2nat_alt.
 induction n using lt_wf_ind.
 unfold nat2dec.
 destruct n.
 - simpl; auto.
 - rewrite n2d_eqn.
   rewrite n2d_alt by (apply Nat.lt_succ_r, Nat.div_lt; omega).
   rewrite of_dec_app.
   simpl length.
   rewrite H by (apply Nat.div_lt; omega).
   unfold of_dec.
   rewrite nat2digit2nat by (apply Nat.mod_upper_bound; auto).
   simpl length.
   rewrite Nat.pow_1_r, Nat.pow_0_r, Nat.add_0_l, Nat.mul_1_r.
   rewrite Nat.mul_comm. symmetry. now apply Nat.div_mod.
Qed.

Lemma nat2dec_inj n n' : nat2dec n = nat2dec n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (nat2dec2nat n), <- (nat2dec2nat n'), EQ.
Qed.

Lemma n2d_spec dg p d count :
 norm (n2d (digit2nat dg + 10*p) d (S count)) =
 norm (n2d p (dg::d) count).
Proof.
 rewrite n2d_eqn'.
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

Lemma d2n2d count n n0 (d0 d : dec) :
 n <= count ->
 n = d2n d n0 ->
 norm (n2d n d0 count) =
 norm (n2d n0 (d ++ d0) count).
Proof.
 revert count n n0 d0.
 induction d.
 - intros. simpl in *. now subst.
 - intros count n n0 d0 LT EQ.
   assert (LE' : n <= S count) by omega.
   rewrite (n2d_anycount count (S count)) by auto.
   rewrite d2n_eqn in EQ.
   rewrite (IHd _ _ _ d0 LE' EQ).
   now rewrite n2d_spec.
Qed.

Definition Normal d := norm d = d.

Lemma n2d_norm n count acc :
 0<n<=count -> Normal (n2d n acc count).
Proof.
 revert n acc.
 induction count.
 - intros. omega.
 - intros. destruct n. omega.
   rewrite n2d_eqn.
   destruct (Nat.le_gt_cases 10 (S n)).
   + apply IHcount.
     split. apply Nat.div_str_pos. omega.
     apply Nat.div_le_upper_bound; omega.
   + rewrite Nat.div_small by auto.
     rewrite Nat.mod_small by auto.
     rewrite n2d_mincount by omega.
     remember (nat2digit (S n)) as dg.
     simpl. destruct dg; red; auto.
     generalize (nat2digit2nat (S n) H0).
     rewrite <- Heqdg; simpl. discriminate.
Qed.

Lemma nat2dec_norm n : Normal (nat2dec n).
Proof.
 destruct n.
 - red; auto.
 - apply n2d_norm; omega.
Qed.

Lemma dec2nat2dec (d:dec) :
  nat2dec (dec2nat d) = norm d.
Proof.
 rewrite <- (nat2dec_norm (dec2nat d)).
 unfold nat2dec.
 rewrite d2n2d with (n0:=0)(d:=d); auto.
 rewrite List.app_nil_r.
 rewrite n2d_mincount; auto with arith.
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

Import DecN.
Open Scope N.

(** We first state that these N conversions behave like
    the nat conversions *)

Lemma d2n_nat d acc :
 d2n d acc = N.of_nat (DecNat.d2n d (N.to_nat acc)).
Proof.
 revert acc.
 induction d.
 - intros; simpl; now rewrite N2Nat.id.
 - intros. rewrite NatProofs.d2n_eqn.
   replace (DecNat.digit2nat a + 10 * N.to_nat acc)%nat
   with (N.to_nat (digit2n a + 10*acc)).
   rewrite <- IHd; auto.
   rewrite N2Nat.inj_add, N2Nat.inj_mul. f_equal.
   now destruct a.
Qed.

Lemma dec2n_nat d : dec2n d = N.of_nat (DecNat.dec2nat d).
Proof.
 unfold dec2n. now rewrite d2n_nat.
Qed.

(** Complements for N2Nat ... *)

Lemma N2Nat_div n m :
 (N.to_nat (n / m) = N.to_nat n / N.to_nat m)%nat.
Proof.
 case (N.eqb_spec m 0); [ intros -> | intros H ].
 - simpl. destruct n; simpl; auto.
 - apply Nat.div_unique with (N.to_nat (n mod m)).
   + generalize (N.mod_upper_bound n m H).
     unfold N.lt. rewrite N2Nat.inj_compare.
     apply Nat.compare_lt_iff.
   + rewrite <- N2Nat.inj_mul, <- N2Nat.inj_add.
     f_equal. now apply N.div_mod.
Qed.

Lemma N2Nat_mod n m : m<>0 ->
 (N.to_nat (n mod m) = (N.to_nat n) mod (N.to_nat m))%nat.
Proof.
 intros.
 apply Nat.mod_unique with (N.to_nat (n / m)).
 - generalize (N.mod_upper_bound n m H).
   unfold N.lt. rewrite N2Nat.inj_compare.
   apply Nat.compare_lt_iff.
 - rewrite <- N2Nat.inj_mul, <- N2Nat.inj_add.
   f_equal. now apply N.div_mod.
Qed.

Lemma N2Nat_le n m : (N.to_nat n <= N.to_nat m)%nat <-> n<=m.
Proof.
 now rewrite <- Nat.compare_le_iff, <- N2Nat.inj_compare.
Qed.

Lemma N2Nat_lt n m : (N.to_nat n < N.to_nat m)%nat <-> n<m.
Proof.
 now rewrite <- Nat.compare_lt_iff, <- N2Nat.inj_compare.
Qed.

Lemma n2digit_nat n : n < 10 ->
 n2digit n = DecNat.nat2digit (N.to_nat n).
Proof.
 destruct n as [|p]; trivial.
 destruct p as [p|p|]; trivial;
  destruct p as [p|p|]; trivial;
   destruct p as [p|p|]; trivial;
    now destruct p.
Qed.

Lemma n2d_nat n acc count :
 n < Npos count ->
 n2d n acc count = DecNat.n2d (N.to_nat n) acc (Pos.to_nat count).
Proof.
 revert n acc.
 induction count.
 - intros.
   destruct n. auto.
   case_eq (Pos.to_nat (count~1)).
   + generalize (Pos2Nat.is_pos (count~1)); omega.
   + intros c Hc.
     rewrite NatProofs.n2d_eqn'.
     simpl Nat.eqb.
     case Nat.eqb_spec.
     * intros. generalize (Pos2Nat.is_pos p); omega.
     * intros.
       change 10%nat with (N.to_nat 10).
       rewrite <- N2Nat_div, <- N2Nat_mod by discriminate.
       simpl n2d.
       case_eq (N.pos_div_eucl p 10); intros q r Hqr.
       assert (Hq : q = Npos p / 10)
         by (unfold N.div; simpl; now rewrite Hqr).
       assert (Hr : r = Npos p mod 10)
         by (unfold N.modulo; simpl; now rewrite Hqr).
       rewrite <- Hq, <-Hr.
       rewrite IHcount.
       replace (DecNat.nat2digit (N.to_nat r)) with (n2digit r).
       apply NatProofs.n2d_anycount.
       { apply (N2Nat_le q (Npos count)).
         rewrite Hq. apply N.div_le_upper_bound. discriminate.
         zify; omega. }
       { apply Nat.succ_le_mono. rewrite <- Hc.
         rewrite <- N2Nat.inj_succ.
         apply (N2Nat_le (N.succ q) (N.pos (count~1))).
         apply N.le_succ_l.
         rewrite Hq. apply N.div_lt_upper_bound. discriminate.
         zify; omega. }
       { apply n2digit_nat. rewrite Hr. now apply N.mod_lt. }
       { rewrite Hq. apply N.div_lt_upper_bound. discriminate.
         zify; omega. }
 - intros.
   destruct n.
   + simpl. now destruct (Pos.to_nat count~0).
   + case_eq (Pos.to_nat (count~0)).
     * generalize (Pos2Nat.is_pos (count~0)); omega.
     * intros c Hc.
       rewrite NatProofs.n2d_eqn'.
       simpl Nat.eqb.
       case Nat.eqb_spec.
       { intros. generalize (Pos2Nat.is_pos p); omega. }
       { intros.
         change 10%nat with (N.to_nat 10).
         rewrite <- N2Nat_div, <- N2Nat_mod by discriminate.
         simpl n2d.
         case_eq (N.pos_div_eucl p 10); intros q r Hqr.
         assert (Hq : q = Npos p / 10)
           by (unfold N.div; simpl; now rewrite Hqr).
         assert (Hr : r = Npos p mod 10)
           by (unfold N.modulo; simpl; now rewrite Hqr).
         rewrite <- Hq, <-Hr.
         rewrite IHcount.
         replace (DecNat.nat2digit (N.to_nat r)) with (n2digit r).
         apply NatProofs.n2d_anycount.
         { apply (N2Nat_le q (Npos count)).
           rewrite Hq. apply N.div_le_upper_bound. discriminate.
           zify; omega. }
         { apply Nat.succ_le_mono. rewrite <- Hc.
           rewrite <- N2Nat.inj_succ.
           apply (N2Nat_le (N.succ q) (N.pos (count~0))).
           apply N.le_succ_l.
           rewrite Hq. apply N.div_lt_upper_bound. discriminate.
           zify; omega. }
         { apply n2digit_nat. rewrite Hr. now apply N.mod_lt. }
         { rewrite Hq. apply N.div_lt_upper_bound. discriminate.
           zify; omega. }}
 - intros. now replace n with 0 by (zify;omega).
Qed.

Lemma n2dec_nat n : n2dec n = DecNat.nat2dec (N.to_nat n).
Proof.
 unfold n2dec.
 rewrite n2d_nat.
 - apply NatProofs.n2d_anycount; auto.
   destruct n; zify; omega.
 - destruct n; zify; omega.
Qed.

(** We now state direct correctness results over the N conversions *)

Lemma n2dec2n (n:N) : dec2n (n2dec n) = n.
Proof.
 now rewrite n2dec_nat, dec2n_nat, NatProofs.nat2dec2nat, N2Nat.id.
Qed.

Lemma n2dec_inj n n' : n2dec n = n2dec n' -> n = n'.
Proof.
 intro EQ.
 now rewrite <- (n2dec2n n), <- (n2dec2n n'), EQ.
Qed.

Definition Normal d := norm d = d.

Lemma n2dec_norm n : Normal (n2dec n).
Proof.
 rewrite n2dec_nat. apply NatProofs.nat2dec_norm.
Qed.

Lemma dec2n2dec (d:dec) :
  n2dec (dec2n d) = norm d.
Proof.
 now rewrite n2dec_nat, dec2n_nat, Nat2N.id, NatProofs.dec2nat2dec.
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

Lemma dec2pos_none d : dec2pos d = None <-> norm d = nil.
Proof.
 rewrite <- NProofs.dec2n2dec. unfold dec2pos.
 split.
 - now case_eq (DecN.dec2n d).
 - change nil with (DecN.n2dec 0).
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

(** Proofs concerning [Deci.succ] *)

Import DecNat NatProofs.

Lemma bounded_succ_length d :
  length (carry_proj (bounded_succ d)) = length d.
Proof.
 induction d; simpl; auto.
 destruct (bounded_succ d); simpl in *; auto.
 destruct a; simpl; congruence.
Qed.

Lemma bounded_succ_spec d :
 match bounded_succ d with
 | Carry d' => S (dec2nat d) = 10^length d /\ dec2nat d' = 0
 | NoCarry d' => S (dec2nat d) < 10^length d /\ dec2nat d' = S (dec2nat d)
 end.
Proof.
 induction d.
 - simpl; auto.
 - simpl bounded_succ.
   assert (L:=bounded_succ_length d).
   destruct bounded_succ; simpl in L.
   + destruct a;
     rewrite !dec2nat_alt in *; simpl of_dec; simpl length;
     rewrite Nat.pow_succ_r', !Nat.add_0_r, <- ?Nat.add_succ_l, ?L;
     destruct IHd as (->,->); split; auto;
     generalize (Nat.pow_nonzero 10 (length d)); omega.
   + rewrite !dec2nat_alt in *; simpl of_dec; simpl length.
     rewrite L.
     destruct IHd as (IH,->). split; auto.
     rewrite Nat.pow_succ_r'.
     rewrite <- Nat.add_succ_l.
     assert (digit2nat a * 10 ^ length d <= 9 * 10 ^ length d).
     { apply Nat.mul_le_mono_nonneg_r; auto with arith.
       destruct a; simpl; auto with arith. }
     omega.
Qed.

Lemma norm_length d : length (norm d) <= length d.
Proof.
 induction d; simpl; auto.
 destruct a; auto.
Qed.

Lemma bounded_succ_norm d :
 match bounded_succ d with
 | Carry d' => Normal d
 | NoCarry d' => Normal d -> Normal d'
 end.
Proof.
 destruct d as [|a d']; simpl; auto. reflexivity.
 destruct (bounded_succ d'); destruct a; unfold Normal; simpl; auto.
 intros.
 generalize (norm_length d'). rewrite H. simpl. omega.
Qed.

Lemma succ_norm d : norm (succ d) = succ (norm d).
Proof.
 induction d as [|a d IH].
 - simpl; auto.
 - unfold succ.
   assert (L := bounded_succ_length (a::d)).
   assert (H := bounded_succ_spec (a::d)).
   assert (N := bounded_succ_norm (a::d)).
   destruct (bounded_succ (a::d)) eqn:E.
   + now rewrite N, E.
   + simpl in E, L.
     unfold succ in IH.
     destruct (bounded_succ d) eqn:E'.
     * destruct a; simpl; try discriminate;
       rewrite ?E'; now injection E as <-.
     * injection E as <-.
       destruct a; simpl; auto; now rewrite E'.
Qed.

Lemma succ_to n : succ (nat2dec n) = nat2dec (S n).
Proof.
 unfold succ.
 assert (L := bounded_succ_length (nat2dec n)).
 assert (H := bounded_succ_spec (nat2dec n)).
 assert (N := bounded_succ_norm (nat2dec n)).
 destruct (bounded_succ (nat2dec n)); simpl in *.
 - destruct H as (H,H').
   rewrite nat2dec2nat in H.
   change (D1 :: l) with (norm (D1 :: l)).
   rewrite <- nat2dec_norm.
   apply dec2nat_inj.
   rewrite nat2dec2nat. rewrite H.
   rewrite dec2nat_alt in *. simpl. rewrite H', L. omega.
 - rewrite nat2dec2nat in H.
   rewrite <- (N (nat2dec_norm n)), <- (nat2dec_norm (S n)).
   apply dec2nat_inj.
   now rewrite nat2dec2nat.
Qed.

Lemma of_succ d : dec2nat (succ d) = S (dec2nat d).
Proof.
 apply nat2dec_inj.
 rewrite <- succ_to.
 rewrite !dec2nat2dec.
 apply succ_norm.
Qed.

Lemma succ_inj d d' :
 succ d = succ d' -> norm d = norm d'.
Proof.
 intros. apply dec2nat_inj.
 assert (E : S (dec2nat d) = S (dec2nat d')).
 { rewrite <- !of_succ. now f_equal. }
 now injection E.
Qed.

(** Proofs concerning [Deci.succ] *)

Lemma to_lt n n' : n < n' -> lt (nat2dec n) (nat2dec n').
Proof.
 induction 1.
 + rewrite <- succ_to. apply Succ.
 + apply Trans with (nat2dec m); trivial.
   rewrite <- succ_to. apply Succ.
Qed.

Lemma of_lt d d' : lt d d' -> dec2nat d < dec2nat d'.
Proof.
 induction 1.
 + rewrite of_succ. auto.
 + omega.
Qed.

Lemma to_lt_iff n n' :  n < n' <-> lt (nat2dec n) (nat2dec n').
Proof.
 split; [apply to_lt|].
 intros H. apply of_lt in H. now rewrite !nat2dec2nat in H.
Qed.

Lemma of_lt_iff d d' :
  dec2nat d < dec2nat d' <-> lt (norm d) (norm d').
Proof.
 rewrite to_lt_iff. now rewrite !dec2nat2dec.
Qed.

Lemma lt_norm d d' : lt d d' -> lt (norm d) (norm d').
Proof.
 rewrite <- of_lt_iff. apply of_lt.
Qed.

Lemma lt_irrefl d d' : lt d d' -> norm d <> norm d'.
Proof.
 intros L E.
 apply of_lt in L.
 apply dec2nat_norm in E.
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
 destruct (CompareSpec2Type (Nat.compare_spec (dec2nat d) (dec2nat d'))).
 - left; right. now apply dec2nat_inj.
 - left; left. now apply of_lt_iff.
 - right; now apply of_lt_iff.
Qed.
