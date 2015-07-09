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

Close Scope Z_scope.

(** Exercise 9.4 **)

Definition S_O :=
  fun (n:nat) (H:S n = 0) =>
  O_S n (eq_sym H).

SearchAbout S.

Definition conv_S_eq_dec (x y:nat)
(ed:{x=y}+{x<>y}): {S x=S y}+{S x<>S y} :=
  match ed with
  | left eqxy =>
      left _ (eq_S x y eqxy)
  | right ineqxy =>
      right _ (not_eq_S x y ineqxy)
  end.

Fixpoint eq_dec_nat (x y:nat): {x=y}+{x<>y} :=
  match x, y return {x=y}+{x<>y} with
  | 0, 0 => left _ (eq_refl 0)
  | S u, 0 => right _ (S_O u)
  | 0, S v => right _ (O_S v)
  | S u, S v =>
      conv_S_eq_dec u v (eq_dec_nat u v)
  end.

(** Exercise 9.5 **)

Require Import List.

Fixpoint count_occurrences
  (l:list nat) (n:nat): nat :=
  match l with
  | nil => 0
  | m :: l' =>
      match eq_dec_nat n m with
      | left _ => S (count_occurrences l' n)
      | right _ => count_occurrences l' n
      end
  end.

Compute count_occurrences (1::2::3::2::nil) 1.
Compute count_occurrences (1::2::3::2::nil) 2.
Compute count_occurrences (1::2::3::2::nil) 3.
Compute count_occurrences (1::2::3::2::nil) 5.

(** Exercise 9.6 **)

Fixpoint div3 (n:nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | S (S (S p)) => S (div3 p)
  end.

Compute div3 0.
Compute div3 2.
Compute div3 100.
Compute div3 101.
Compute div3 102.

Lemma div3_le: forall n:nat, div3 n <= n.
Proof.
  intros n.
  cut (div3 n <= n /\ div3 (S n) <= S n /\
       div3 (S (S n)) <= S (S n)).
  tauto.
  induction n.
  simpl; auto.
  destruct IHn as [H1 [H2 H3]].
  split; [auto | split; auto].
  simpl; auto with arith.
Qed.

(** Exercise 9.7 **)

(* Given *)

Fixpoint div2 (n:nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.

(* To do *)

Fixpoint mod2 (n:nat) :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S m) => mod2 m
  end.

Theorem ex_9_7:
  forall n:nat, n = 2 * (div2 n) + (mod2 n).
Proof.
  intros n.
  cut (n = 2 * (div2 n) + (mod2 n) /\
       S n = 2 * (div2 (S n)) + (mod2 (S n))).
  tauto.
  induction n.
  simpl; tauto.
  destruct IHn as [IHn1 IHn2].
  split; auto.
  simpl; apply f_equal.
  simpl in IHn1.
  rewrite <-plus_n_Sm; simpl; auto.
Qed.

(** Exercise 9.8 **)

Fixpoint fib (n:nat) :=
  match n with
  | 0 => 1
  | 1 => 1
  | S p => (fib p) + match p with
                     | 0 => 1
                     | S q => fib q
                     end
  end.

Compute (fib 5).
Compute (fib 10).

Fixpoint fib' (n:nat) :=
  match n with
  | 0 => (1, 1)
  | S p => let (fp, f) := fib' p in
           (f, fp + f)
  end.

Compute (fib' 5).
Compute (fib' 10).

Lemma fib_prop:
  forall n:nat,
  fib n + fib (S n) = fib (S (S n)).
Proof.
  intros n.
  simpl; apply plus_comm.
Qed.

Lemma fib'_prop1:
  forall n:nat,
  fst (fib' (S n)) = snd (fib' n).
Proof.
  intros n.
  simpl.
  elim (fib' n).
  auto.
Qed.

Lemma fib'_prop2:
  forall n:nat,
  snd (fib' (S n)) =
  fst (fib' n) + snd (fib' n).
Proof.
  intros n.
  simpl.
  elim (fib' n).
  simpl; auto.
Qed.

Lemma fib'_prop3:
  forall n:nat,
  fst (fib' (S (S n))) =
  fst (fib' (S n)) + fst (fib' n).
Proof.
  intros n.
  rewrite fib'_prop1, fib'_prop2, fib'_prop1.
  apply plus_comm.
Qed.

Lemma fib'_prop4:
  forall n:nat,
  snd (fib' (S (S n))) =
  snd (fib' (S n)) + snd (fib' n).
Proof.
  intros n.
  repeat rewrite <-fib'_prop1.
  apply fib'_prop3.
Qed.

Lemma fib_fib'_fst_eq:
  forall n:nat, fst (fib' n) = fib n.
Proof.
  intros n.
  cut (fst (fib' n) = fib n /\
       fst (fib' (S n)) = fib (S n)).
  tauto.
  induction n.
  simpl; auto.
  destruct IHn as [IHn1 IHn2].
  split; auto.
  rewrite <-fib_prop.
  rewrite fib'_prop3.
  rewrite IHn1, IHn2.
  apply plus_comm.
Qed.

Lemma fib_fib'_snd_eq:
  forall n:nat, snd (fib' n) = fib (S n).
Proof.
  intros n.
  rewrite <-fib'_prop1, fib_fib'_fst_eq.
  auto.
Qed.

Theorem ex_9_8:
  forall n:nat,
  (fib n, fib (S n)) = fib' n.
Proof.
  intros n.
  rewrite <-fib_fib'_fst_eq, <-fib_fib'_snd_eq.
  elim (fib' n).
  auto.
Qed.