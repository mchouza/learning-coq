(** Exercise 7.1 **)

(* Given *)

Definition divides (n m:nat) :=
  exists p:nat, p * n = m.

(* To do *)

Lemma divides_0: forall n:nat, divides n 0.
Proof.
  unfold divides.
  intros n.
  exists 0; simpl; reflexivity.
Qed.

Lemma divides_plus:
  forall n m:nat,
  divides n m -> divides n (n + m).
Proof.
  unfold divides.
  intros n m H1.
  destruct H1 as [p H1].
  exists (S p); simpl.
  rewrite H1; reflexivity.
Qed.

Lemma sum_zero_implies_zero:
  forall n m:nat, n + m = 0 -> n = 0.
Proof.
  intros n m H.
  induction n.
  reflexivity.
  discriminate.
Qed.

Lemma sum_comm:
  forall n m:nat, n + m = m + n.
Proof.
  intros n m.
  induction n.
  simpl; apply plus_n_O.
  rewrite <-plus_n_Sm with (m := n).
  simpl; apply f_equal; exact IHn.
Qed.

Lemma succ_pred_identity:
  forall n:nat, n<>0 -> n = S (pred n).
Proof.
  intros n H1.
  induction n.
  assert (0 = 0) as H2.
  reflexivity.
  contradiction.
  simpl.
  reflexivity.
Qed.

Lemma sum_cancel:
  forall n m p:nat, n + p = m + p -> n = m.
Proof.
  induction p.
  repeat rewrite <-plus_n_O.
  intro H; exact H.
  repeat rewrite <-plus_n_Sm.
  intro H.
  apply IHp.
  apply eq_add_S; exact H.
Qed.

Lemma not_divides_plus:
  forall n m:nat,
  ~divides n m -> ~divides n (n + m).
Proof.
  unfold divides.
  intros n m H1 H2.
  destruct H2 as [q H2].
  assert (exists p: nat, p * n = m).
  exists (pred q).
  assert (q <> 0) as H3.
  intros H4.
  assert (q * n = 0) as H5.
  rewrite H4; simpl; reflexivity.
  assert (m = 0) as H6.
  apply sum_zero_implies_zero with (n := m) (m := n).
  symmetry.
  rewrite sum_comm.
  rewrite <-H5; exact H2.
  assert (exists p: nat, p * n = m) as H7.
  exists 0.
  simpl; rewrite H6; reflexivity.
  contradiction.
  assert (q = S (pred q)) as H4.
  apply succ_pred_identity; exact H3.
  assert (S (pred q) * n = n + m) as H5.
  rewrite <-H4; exact H2.
  assert (S (pred q) * n =
    pred q * n + n) as H6.
  simpl.
  rewrite sum_comm; reflexivity.
  rewrite H6 in H5.
  apply sum_cancel with (p := n).
  assert (m + n = n + m) as H7.
  apply sum_comm.
  rewrite H7; exact H5.
  contradiction.
Qed.

(* Now I use the 'Arith' module, otherwise I
   would get lost proving auxiliary lemmas *)
Require Import Arith.

Lemma not_divides_lt:
  forall n m:nat,
  0 < m -> m < n -> ~divides n m.
Proof.
  unfold divides.
  intros n m H1 H2 H3.
  destruct H3 as [p H3].
  assert (0 < n) as H4.
  apply lt_trans with (m := m); assumption.
  assert (0 < p) as H5.
  assert (0 <> p) as H6.
  intro H7.
  rewrite <-H7 in H3.
  simpl in H3.
  rewrite <-H3 in H1.
  apply lt_irrefl with (n:=0); exact H1.
  apply neq_0_lt; exact H6.
  assert (m * p < n * p) as H6.
  apply mult_lt_compat_r with (n := m).
  exact H2.
  exact H5.
  rewrite mult_comm in H3.
  rewrite H3 in H6.
  assert (1 <= p) as H7.
  apply H5.
  assert (1 * m <= p * m) as H8.
  apply mult_le_compat_r; exact H7.
  rewrite mult_1_l in H8.
  rewrite mult_comm in H8.
  apply le_not_lt with (n := m) (m := m * p).
  exact H8.
  exact H6.
Qed.