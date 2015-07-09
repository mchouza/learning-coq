(** Exercise 9.1 **)

Fixpoint extract
  (A:Set) (P:A->Prop) (p:sig P): A :=
  match p with
  | exist x q => x
  end.

Inductive even: nat -> Prop :=
  | even_0: even 0
  | even_SSn:
      forall n:nat, even n -> even (S (S n)).

Lemma even2: even 2.
Proof.
  apply even_SSn, even_0.
Qed.

Definition my_sig_even := exist even 2 even2.

Check my_sig_even.

Compute extract nat even my_sig_even.

Lemma ex_9_1:
  forall (A:Set) (P:A->Prop) (y:{x:A|P x}),
  P (extract A (fun x:A => P x) y).
Proof.
  induction y; simpl; auto.
Qed.

(** Exercise 9.2 **)

(* Given *)

Require Import ZArith.

Open Scope Z_scope.

Variable div_pair: 
  forall a b:Z, 0 < b ->
  { p:Z*Z | a = (fst p)*b + snd p /\
            0 <= snd p < b }.

Definition div_pair' 
  (a:Z)(x:{ b:Z | 0 < b }): Z*Z :=
  match x with
  | exist b h => 
      let (v, _) := div_pair a b h in v
  end.

(* To do *)

Definition gt0 (a:Z) := (0 < a).

Definition div_pair''
  (a:Z)(x:{ b:Z | 0 < b }) :=
  match x with
  | exist _ h =>
      div_pair a (extract Z gt0 x)
  end.  

Check div_pair''.

(** Exercise 9.3 *)

Definition sig_rec_simple
  (A:Set) (P:A->Prop) (B:Set)
  (h:forall x:A, P x -> B) (p:sig P) :=
  match p with
  | exist a q => h a q
  end.

Check sig_rec_simple.