
Require Import Deci Ascii String.

(** * Conversion between dec and string *)

(** Pretty straightforward, which is precisely the point of the
    [dec] datatype. The only catch is that [nil] means ["0"],
    not the empty string, so we don't have a perfect bijection. *)

Definition to_char (d:digit) :=
 match d with
 | D0 => "0"
 | D1 => "1"
 | D2 => "2"
 | D3 => "3"
 | D4 => "4"
 | D5 => "5"
 | D6 => "6"
 | D7 => "7"
 | D8 => "8"
 | D9 => "9"
 end%char.

Fixpoint to_string_rec (dl:dec) :=
 match dl with
 | nil => EmptyString
 | d::dl => String (to_char d) (to_string_rec dl)
 end.

Definition to_string (dl:dec) :=
 match dl with
 | nil => "0"%string
 | _ => to_string_rec dl
 end.

Definition of_char (a:ascii) :=
 match a with
 | "0" => Some D0
 | "1" => Some D1
 | "2" => Some D2
 | "3" => Some D3
 | "4" => Some D4
 | "5" => Some D5
 | "6" => Some D6
 | "7" => Some D7
 | "8" => Some D8
 | "9" => Some D9
 | _ => None
 end%char.

Definition ocons (od:option digit)(ol:option dec) :=
 match od, ol with
 | Some d, Some dl => Some (d::dl)
 | _,_ => None
 end.

Fixpoint of_string_rec s :=
 match s with
 | EmptyString => Some nil
 | String a s => ocons (of_char a) (of_string_rec s)
 end.

Definition of_string s :=
 match s with
 | EmptyString => None
 | _ => of_string_rec s
 end.

(* Compute of_string "123456890123456890123456890123456890". *)

Lemma of_to_char d : of_char (to_char d) = Some d.
Proof.
 now destruct d.
Qed.

Lemma of_to_rec d : of_string_rec (to_string_rec d) = Some d.
Proof.
 induction d; simpl; rewrite ?IHd, ?of_to_char; simpl; auto.
Qed.

Lemma of_to d : d<>nil -> of_string (to_string d) = Some d.
Proof.
 destruct d. now destruct 1. intros _. apply of_to_rec.
Qed.

Lemma of_to_nil : of_string (to_string nil) = Some (D0::nil).
Proof.
 reflexivity.
Qed.

Lemma of_to_gen d :
  of_string (to_string d) = Some d \/
  of_string (to_string d) = Some (D0::d).
Proof.
 destruct d.
 - now right.
 - left. now apply of_to.
Qed.

Lemma to_of_char c d : of_char c = Some d -> to_char d = c.
Proof.
 destruct c as [[|] [|] [|] [|] [|] [|] [|] [|]];
  discriminate || injection 1 as <-; auto.
Qed.

Lemma to_of_rec s d : of_string_rec s = Some d -> to_string_rec d = s.
Proof.
 revert d.
 induction s; simpl.
 - now injection 1 as <-.
 - destruct (of_char a) eqn:Ha; try discriminate.
   destruct (of_string_rec s) eqn:Hs; try discriminate.
   simpl. injection 1 as <-. simpl. f_equal; auto using to_of_char.
Qed.

Lemma of_non_nil s : of_string s <> Some nil.
Proof.
 destruct s.
 - now simpl.
 - simpl.
   now destruct of_char, of_string_rec.
Qed.

Lemma to_of s d : of_string s = Some d -> to_string d = s.
Proof.
 destruct s; try discriminate.
 intros H.
 assert (d<>nil).
 { intros ->. apply (of_non_nil _ H). }
 apply to_of_rec in H.
 now destruct d.
Qed.
