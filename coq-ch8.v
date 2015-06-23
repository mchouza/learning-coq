(** Exercise 8.1 **)

Require Import List.

Inductive last
  (A:Type) (a:A) : list A -> Prop :=
  | last_b : last A a (a :: nil)
  | last_i : forall (b:A) (l:list A),
             last A a l -> last A a (b :: l).

Implicit Arguments last [A].

Fixpoint last_fun
  (A:Type) (l:list A): option A :=
  match l with
  | nil => None
  | a :: nil => Some a
  | a :: tail => last_fun A tail
  end.

Implicit Arguments last_fun [A].

Compute (last_fun (1 :: 2 :: 3 :: 4 :: nil)).
Compute (last_fun (1 :: nil)).
Compute (last_fun (A := nat) nil).

Lemma last_ex_1:
  last 3 (1 :: 2 :: 3 :: nil).
Proof.
  do 2 apply last_i.
  apply last_b.
Qed.

Lemma last_elem_implies_pos_len:
  forall (A:Type) (a:A) (l:list A),
  last a l -> 1 <= length l.
Proof.
  intros A a l H1.
  elim H1.
  simpl; apply le_n.
  intros b l' H2 H3.
  simpl.
  apply le_S; exact H3.
Qed.

Require Import Arith.

Lemma last_ex_2:
  ~last 4 nil.
Proof.
  intro H.
  apply le_Sn_0 with (n := 0).
  apply last_elem_implies_pos_len
    with (l := nil) (a := 4).
  exact H.
Qed.

Lemma len_1_list_is_base:
  forall (A:Type) (a:A) (l:list A),
  last a l /\ length l = 1 -> l = a :: nil.
Proof.
  intros A a b H1.
  destruct H1 as [H1 H2].
  destruct H1 as [| b].
  reflexivity.
  assert (1 <= length l) as H3.
  apply last_elem_implies_pos_len
    with (a := a) (l := l); exact H1.
  assert (2 <= length(b :: l)) as H4.
  simpl; apply le_n_S; exact H3.
  rewrite H2 in H4.
  assert False.
  apply le_Sn_n with (n:=1); exact H4.
  contradiction.
Qed.

Lemma only_last_matters:
  forall (A:Type) (a b c:A) (l:list A),
  last a (b :: c :: l) -> last a (c :: l).
Proof.
  intros A a b c l H.
  inversion H.
  exact H1.
Qed.

Lemma last_ex_3:
  ~last 4 (1 :: 2 :: 3 :: nil).
Proof.
  intros H1.
  assert (last 4 (3 :: nil)) as H2.
  apply only_last_matters with (b := 2).
  apply only_last_matters with (b := 1).
  exact H1.
  assert (3 :: nil = 4 :: nil) as H3.
  apply len_1_list_is_base.
  split.
  exact H2.
  simpl; reflexivity.
  discriminate.
Qed.  

Theorem last_equiv:
  forall (A:Type) (a:A) (l:list A),
  last a l <-> last_fun l = Some a.
Proof.
  intros A a l.
  split.
  intros H1.
  induction l.
  assert (1 <= 0) as H2.
  apply last_elem_implies_pos_len
    with (a := a) (l := nil).
  exact H1.
  apply False_ind.
  apply le_Sn_0 with (n := 0); exact H2.
  destruct l.
  assert (a = a0) as H2.
  assert (a0 :: nil = a :: nil) as H3.
  apply len_1_list_is_base.
  split.
  exact H1.
  simpl; reflexivity.
  injection H3.
  intro H4.
  rewrite H4; reflexivity.
  rewrite <-H2.
  simpl; reflexivity.
  assert (last a (a1 :: l)) as H2.
  apply only_last_matters with (b := a0).
  exact H1.
  simpl.
  apply IHl; exact H2.
  induction l.
  simpl.
  intro H1.
  discriminate.
  destruct l.
  simpl.
  intro H2.
  assert (a = a0) as H3.
  injection H2.
  intro H3.
  rewrite H3; reflexivity.
  rewrite <-H3.
  constructor.
  intro H1.
  apply last_i.
  apply IHl.
  rewrite <-H1.
  simpl.
  reflexivity.
Qed.
