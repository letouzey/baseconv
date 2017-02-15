
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
