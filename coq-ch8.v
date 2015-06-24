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

(** Exercise 8.2 **)

Inductive split_last (A:Type):
  list A -> list A -> A -> Prop :=
  | split_last_s: 
      forall a:A, 
      split_last A (a :: nil) nil a
  | split_last_i:
      forall (a b:A) (l l':list A),
      split_last A l l' a ->
      split_last A (b :: l) (b :: l') a.

Implicit Arguments split_last [A].

Lemma sl_ex_1: split_last (3 :: nil) nil 3.
Proof.
  constructor.
Qed.

Lemma sl_ex_2: 
  split_last (3 :: 4 :: nil) (3 :: nil) 4.
Proof.
  repeat constructor.
Qed.

Lemma sl_ex_3: ~split_last nil nil 5.
Proof.
  intro H.
  inversion H.
Qed.

Lemma sl_ex_4: 
  ~split_last (3 :: 4 :: nil) (3 :: nil) 5.
Proof.
  intro H.
  inversion H.
  inversion H4.
Qed.

Lemma sl_ex_5: 
  ~split_last (3 :: 4 :: nil) (2 :: nil) 4.
Proof.
  intro H.
  inversion H.
Qed.

Inductive palindrome (A:Type): list A -> Prop :=
  | palindrome_e: palindrome A nil
  | palindrome_s: 
      forall a:A, palindrome A (a :: nil)
  | palindrome_i:
      forall (a:A) (l l':list A),
      palindrome A l /\ split_last l' l a ->
      palindrome A (a :: l').


Implicit Arguments palindrome [A].

Lemma pal_ex_1: palindrome (A := nat) nil.
Proof.
  constructor.
Qed.

Lemma pal_ex_2: palindrome (3 :: nil).
Proof.
  constructor.
Qed.

Lemma pal_ex_3: palindrome (4 :: 4 :: nil).
Proof.
  apply palindrome_i 
    with (l' := 4 :: nil) (l := nil).
  split; repeat constructor.
Qed.

Lemma pal_ex_4:
 palindrome (4 :: 6 :: 5 :: 6:: 4 :: nil).
Proof.
  apply palindrome_i 
    with (l' := 6 :: 5 :: 6:: 4 :: nil)
         (l := 6 :: 5 :: 6:: nil)
         (a := 4).
  split.
  apply palindrome_i
    with (l' := 5 :: 6 :: nil) 
         (l := 5 :: nil)
         (a := 6).
  split; repeat constructor.
  repeat constructor.
Qed.

Lemma pal_ex_5: ~palindrome (4 :: 3 :: nil).
Proof.
  intro H.
  inversion H.
  destruct H1 as [_ H1].
  inversion H1.
  inversion H7.
Qed.

Lemma no_split_nil:
  forall (A:Type) (a:A) (l:list A),
  ~split_last nil l a.
Proof.
  intros A a l H.
  inversion H.
Qed.

Lemma no_nil_when_splitting_big_lists:
  forall (A:Type) (a b c:A) (l:list A),
  ~split_last (a :: b :: l) nil c.
Proof.
  intros A a b c l H.
  inversion H.
Qed.

Lemma split_1st_doesnt_matter:
  forall (A:Type) (a b c:A) (l l':list A),
  split_last (a :: b :: l) (a :: l') c ->
  split_last (b :: l) l' c.
Proof.
  intros A a b c l l' H.
  inversion H.
  exact H4.
Qed.

Lemma pal_ex_6:
 ~palindrome (4 :: 6 :: 5 :: 7:: 4 :: nil).
Proof.
  intro H1.
  inversion H1.
  clear H H2 a l'.
  destruct H0 as [H2 H3].
  inversion H3.
  inversion H6.
  inversion H11.
  inversion H16.
  rewrite <-H8, <-H13, <-H17 in H0.
  rewrite <-H0 in H2.
  clear - H2.
  inversion H2.
  destruct H0 as [H3 H4].
  inversion H4.
  inversion H8.
  apply no_split_nil with (l := l'1) (a := 6).
  assumption.
  apply no_split_nil with (l := l'2) (a := 4).
  assumption.
Qed.

(** Exercise 8.3 **)

(* TO BE DONE *)

(** Exercise 8.4 **)

Inductive transp_two (A:Type) : 
  list A -> list A -> Prop :=
  | transp_two_f:
    forall (a b:A) (l:list A),
    transp_two A (a :: b :: l) (b :: a :: l)
  | transp_two_i:
    forall (a:A) (l l':list A),
    transp_two A l l' ->
    transp_two A (a :: l) (a :: l').

Implicit Arguments transp_two [A].

Lemma transp_two_ex1:
  ~transp_two (1 :: 2 :: nil) (1 :: 2 :: nil).
Proof.
  intro H.
  inversion H.
  inversion H1.
  inversion H5.
Qed.

Lemma transp_two_ex2:
  transp_two (1 :: 2 :: nil) (2 :: 1 :: nil).
Proof.
  constructor.
Qed.

Lemma transp_two_ex3:
  ~transp_two (1 :: 2 :: 3 :: nil)
              (3 :: 1 :: 2 :: nil).
Proof.
  intro H.
  inversion H.
Qed.

Lemma transp_two_ex4:
  transp_two (1 :: 2 :: 3 :: nil)
             (1 :: 3 :: 2 :: nil).
Proof.
  repeat constructor.
Qed.

Lemma transp_two_ex5:
  ~transp_two (5 :: 1 :: 2 :: 3 :: nil)
              (1 :: 5 :: 3 :: 2 :: nil).
Proof.
  intro H.
  inversion H.
Qed.

Lemma transp_two_ex6:
  transp_two (5 :: 1 :: 2 :: 3 :: nil)
             (1 :: 5 :: 2 :: 3 :: nil).
Proof.
  repeat constructor.
Qed.

Inductive permuted (A:Type) :
  list A -> list A -> Prop :=
  | permuted_t:
    forall (l l':list A),
    transp_two l l' -> permuted A l l'
  | permuted_i:
    forall (l l' l'':list A),
    permuted A l l' -> permuted A l' l'' ->
    permuted A l l''.

Implicit Arguments permuted [A].

Lemma permuted_ex1:
  permuted (1 :: 2 :: nil) (1 :: 2 :: nil).
Proof.
  assert (transp_two (1 :: 2 :: nil)
                     (2 :: 1 :: nil)) as H1.
  repeat constructor.
  assert (transp_two (2 :: 1 :: nil)
                     (1 :: 2 :: nil)) as H2.
  repeat constructor.
  apply permuted_i
    with (l := (1 :: 2 :: nil))
         (l' := (2 :: 1 :: nil)).
  constructor; assumption.
  constructor; assumption.
Qed.

Lemma permuted_ex2:
  ~permuted (2 :: 2 :: nil) (1 :: 2 :: nil).
Proof.
  intro H.
  inversion H.
  inversion H0.
  inversion H0.
  inversion H1.
  inversion H4.
  rewrite <-H10 in H7.
  clear - H7.
  inversion H7.
  inversion H13.
  inversion H17.
  (* PROOF IN PROGRESS *)