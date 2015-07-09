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