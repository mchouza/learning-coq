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

(** Exercise 9.9 **)

Theorem nat_3_ind:
  forall P:nat->Prop,
  P 0 -> P 1 -> P 2 ->
  (forall n:nat, P n -> P (S (S (S n)))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 P2 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n))).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 [IHn2 IHn3]].
  auto.
Qed.

Theorem nat_4_ind:
  forall P:nat->Prop,
  P 0 -> P 1 -> P 2 -> P 3 ->
  (forall n:nat, P n -> P (S (S (S (S n))))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 P2 P3 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n)) /\
       P (S (S (S n)))).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 [IHn2 [IHn3 IHn4]]].
  auto.
Qed.

(** Exercise 9.10 **)

Theorem fib_ind:
  forall P:nat->Prop, P 0 -> P 1 ->
  (forall n:nat,
   P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 IHn2].
  auto.
Qed.

Compute fib (3 + 2 + 2).
Compute (fib (3 + 1)) * (fib (2 + 1)) +
        (fib 3) * (fib 2).

Lemma fib_prod:
  forall (n p:nat),
  fib (S(S(n + p))) =
  (fib (S n)) * (fib (S p)) +
  (fib n) * (fib p).
Proof.
  intros n.
  elim n using fib_ind.
  simpl; auto.
  intros p.
  simpl; repeat rewrite <-plus_n_O.
  rewrite plus_comm, plus_assoc; auto.
  clear n.
  intros n IHn1 IHn2 p.
  specialize IHn1 with (p := p).
  specialize IHn2 with (p := p).
  rewrite <-fib_prop.
  repeat rewrite plus_Sn_m in *.
  rewrite IHn1, IHn2.
  repeat rewrite <-fib_prop.
  repeat rewrite mult_plus_distr_r.
  repeat rewrite <-plus_assoc.
  apply f_equal.
  rewrite plus_comm, <-plus_assoc, <-plus_assoc.
  do 2 apply f_equal.
  rewrite plus_comm; auto.
Qed.

(** Exercise 9.11 **)

Lemma div3_le': forall n:nat, div3 n <= n.
Proof.
  intros n.
  elim n using nat_3_ind; simpl; auto.
  intros n' Hrec.
  do 2 apply le_S; apply le_n_S; exact Hrec.
Qed.

Theorem nat_2_ind:
  forall P:nat->Prop,
  P 0 -> P 1 ->
  (forall n:nat, P n -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 IHn2].
  auto.
Qed.

Theorem ex_9_7':
  forall n:nat, n = 2 * (div2 n) + (mod2 n).
Proof.
  intros n.
  elim n using nat_2_ind; simpl; auto.
  intros n' Hrec.
  rewrite <-plus_n_Sm, plus_Sn_m.
  do 2 apply f_equal; exact Hrec.
Qed.

(* ex 9.8 skipped because it's too long *)

(** Exercise 9.12 **)

Definition mult2 (n:nat) := n + n.

(*
Fixpoint div2_mod2 (n:nat):
  {q:nat & {r:nat | n = (mult2 q) + r /\
                    r <= 1}}.
*)
(* FIXME: TO BE DONE *)

(** Exercise 9.13 **)

(* Given *)

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with
  | 0 => n
  | S p => S (plus' n p)
  end.

(* To do *)

Lemma plus'_assoc:
  forall n m p:nat,
  (plus' n (plus' m p)) = (plus' (plus' n m) p).
Proof.
  intros n m p.
  induction p.
  simpl; auto.
  simpl.
  apply f_equal, IHp.
Qed.

(** Exercise 9.14 **)

(* Given *)

Fixpoint plus'' (n m:nat){struct m} : nat :=
  match m with
  | 0 => n
  | S p => plus'' (S n) p
  end.

(* To do *)

Lemma plus''_Sn_m:
  forall n m:nat,
  plus'' (S n) m = S(plus'' n m).
Proof.
  intros n m.
  generalize n.
  induction m.
  simpl; auto.
  intros n'.
  simpl.
  rewrite IHm.
  auto.
Qed.

Lemma plus''_assoc:
  forall n m p:nat,
  (plus'' n (plus'' m p)) =
  (plus'' (plus'' n m) p).
Proof.
  intros n m p.
  generalize n m.
  induction p.
  simpl; auto.
  intros n' m'.
  simpl.
  rewrite plus''_Sn_m; simpl.
  repeat rewrite plus''_Sn_m.
  rewrite IHp; auto.
Qed.

(** Exercise 9.15 **)

Fixpoint _tr_fib_aux (f1 f2 c:nat) :=
  match c with
  | 0 => f1
  | S d => _tr_fib_aux f2 (f1 + f2) d
  end.

Definition tail_rec_fib (n:nat) :=
  _tr_fib_aux 1 1 n.

Compute tail_rec_fib 10.

Lemma trf_equiv:
  forall n:nat, tail_rec_fib n = fib n.
(* IN PROGRESS *)