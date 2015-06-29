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

Fixpoint list_count_f
  (A:Type) (l:list A) (f:A->bool) : nat :=
  match l with
  | nil => 0
  | h :: t =>
      if (f h)
      then S (list_count_f A t f)
      else list_count_f A t f
  end.

Implicit Arguments list_count_f [A].

Lemma transp_two_doesnt_change_f_counts:
  forall (A:Type) (l l':list A) (f:A->bool),
  transp_two l l' ->
  list_count_f l f = list_count_f l' f.
Proof.
  intros A l l' f H.
  induction H.
  simpl.
  case (f a), (f b); auto.
  simpl.
  case (f a); auto.
Qed.

Implicit Arguments
  transp_two_doesnt_change_f_counts [A].

Lemma permuted_doesnt_change_f_counts:
  forall (A:Type) (l l':list A) (f:A->bool),
  permuted l l' ->
  list_count_f l f = list_count_f l' f.
Proof.
  intros A l l' f H.
  induction H.
  apply transp_two_doesnt_change_f_counts;
    assumption.
  apply eq_trans
    with (y := list_count_f l' f);
    assumption.
Qed.

Lemma permuted_ex2:
  ~permuted (2 :: 2 :: nil) (1 :: 2 :: nil).
Proof.
  intro H.
  cut (0 = 1).
  apply O_S.
  cut (list_count_f (2 :: 2 :: nil)
                    (beq_nat 1) =
       list_count_f (1 :: 2 :: nil)
                    (beq_nat 1)).
  simpl; auto.
  apply permuted_doesnt_change_f_counts; 
    assumption.
Qed.

Lemma permuted_ex3:
  ~permuted (1 :: 2 :: nil) 
            (1 :: 2 :: 3 :: nil).
Proof.
  intro H.
  cut (2 = 3).
  apply n_Sn.
  cut (list_count_f (1 :: 2 :: nil)
                    (fun _ => true) =
       list_count_f (1 :: 2 :: 3 ::nil)
                    (fun _ => true)).
  simpl; auto.
  apply permuted_doesnt_change_f_counts; 
    assumption.
Qed.

Lemma permuted_refl:
  forall (A:Type) (l:list A),
  length l >= 2 -> permuted l l.
Proof.
  intros A l H.
  induction l.
  inversion H.
  induction l.
  inversion H.
  inversion H1.
  clear.
  apply permuted_i 
    with (l' := (a0 :: a :: l)).
  repeat constructor.
  repeat constructor.
Qed.

Lemma transp_two_symm:
  forall (A:Type) (l l':list A),
  transp_two l l' <-> transp_two l' l.
Proof.
  intros A l l'.
  split.
  intros H.
  induction H.
  constructor.
  constructor; assumption.
  intros H.
  induction H.
  constructor.
  constructor; assumption.
Qed.

Lemma permuted_symm:
  forall (A:Type) (l l':list A),
  permuted l l' <-> permuted l' l.
Proof.
  intros A l l'.
  split.
  intros H.
  induction H.
  constructor.
  apply transp_two_symm; assumption.
  apply permuted_i with (l' := l');
    assumption.
  intros H.
  induction H.
  constructor.
  apply transp_two_symm; assumption.
  apply permuted_i with (l' := l');
    assumption.
Qed.

Lemma permuted_trans:
  forall (A:Type) (l l' l'':list A),
  permuted l l' -> permuted l' l'' ->
  permuted l l''.  
Proof.
  intros A l l' l'' H1 H2.
  apply permuted_i with (l' := l');
    assumption.
Qed.

(** Exercise 8.5 **)

(* Given *)

Inductive par : Set := open | close.

(* To do *)

Inductive wp: list par -> Prop :=
  | wp_e: wp nil
  | wp_p: forall l:list par,
      wp l -> wp (open :: (l ++ (close :: nil)))
  | wp_c: forall (l l':list par),
      wp l -> wp l' -> wp (l ++ l').

Lemma wp_ex1: wp nil.
Proof.
  constructor.
Qed.

Lemma wp_even_len: 
  forall l:list par, 
  wp l -> exists p:nat, length l = p + p.
Proof.
  intros l H.
  induction H.
  exists 0; auto.
  destruct IHwp as [p H2].
  exists (S(p)); simpl.
  rewrite app_length, H2; simpl.
  rewrite <-plus_n_Sm, <-plus_n_O.
  rewrite <-plus_n_Sm; reflexivity.
  destruct IHwp1 as [p H1].
  destruct IHwp2 as [p' H2].
  exists (p + p').
  rewrite app_length, H1, H2.
  repeat rewrite plus_assoc.
  rewrite plus_comm with (n := p + p) (m := p').
  rewrite plus_comm with (n := p) (m := p').
  repeat rewrite plus_assoc; reflexivity.
Qed.

Lemma wp_ex2: ~wp (open :: nil).
Proof.
  intros H1.
  cut (exists p, length (open :: nil) = p + p).
  simpl.
  intros [p H2].
  induction p.
  discriminate.
  rewrite <-plus_n_Sm in H2.
  simpl in H2.
  assert (0 = S(p + p)) as H3.
  apply eq_add_S; assumption.
  discriminate H3.
  apply wp_even_len; assumption.
Qed.

Lemma wp_oc: wp (cons open (cons close nil)).
Proof.
  apply wp_p with (l := nil); constructor.
Qed.

Lemma cons_as_list_cat:
  forall (A:Type) (a:A) (l:list A),
  a :: l = (a :: nil) ++ l.
Proof.
  intros A a l.
  auto.
Qed.

Lemma wp_o_head_c:
  forall l1 l2:list par,
  wp l1 -> wp l2 ->
  wp (cons open (app l1 (cons close l2))).
Proof.
  intros l1 l2 H1 H2.
  assert (close :: l2 = (close :: nil) ++ l2)
    as H3.
  auto.
  rewrite H3.
  rewrite app_assoc; auto.
  apply wp_c
    with (l := open :: (l1 ++ close :: nil))
         (l' := l2).
  rewrite app_comm_cons.
  apply wp_p.
  exact H1.
  exact H2.
Qed.

Lemma wp_o_tail_c:
  forall (l1 l2:list par),
  wp l1 -> wp l2 ->
  wp (app l1 
          (cons open
                (app l2 (cons close nil)))).
Proof.
  intros l1 l2 H1 H2.
  rewrite app_comm_cons.
  apply wp_c.
  exact H1.
  apply wp_p.
  exact H2.
Qed.

(** Exercise 8.6 **)

(* Given *)

Inductive bin : Set := 
| L : bin
| N : bin -> bin -> bin.

Fixpoint bin_to_string (t:bin) : list par :=
  match t with
  | L => nil
  | N u v =>
      cons open
           (app (bin_to_string u)
                (cons close (bin_to_string v)))
  end.

(* To do *)

Lemma ex_8_6: 
  forall t:bin, wp (bin_to_string t).
Proof.
  intros t.
  induction t.
  simpl; apply wp_e.
  simpl; apply wp_o_head_c; assumption.
Qed.

(** Exercise 8.7 **)

(* Given *)

Fixpoint bin_to_string' (t:bin) : list par :=
  match t with
  | L => nil
  | N u v =>
      app (bin_to_string' u)
          (cons open
                (app (bin_to_string' v)
                     (cons close nil)))
  end.

(* To do *)

Lemma ex_8_7:
  forall t:bin, wp (bin_to_string' t).
Proof.
  intros t.
  induction t.
  simpl; apply wp_e.
  simpl; apply wp_o_tail_c; assumption.
Qed.

(** Exercise 8.8 **)

Require Import JMeq.

Lemma ex_8_8:
  forall x y z:nat, JMeq (x+(y+z)) ((x+y)+z).
  intros x y z.
  rewrite plus_assoc.
  apply JMeq_refl.
Qed.

(** Exercise 8.9 **)

(* Given *)

Inductive even: nat->Prop :=
  | O_even: even 0
  | plus_2_even: 
      forall n:nat, even n -> even (S (S n)).

(* To do *)

Lemma ex_8_9:
  forall n:nat, 
  even n -> exists m:nat, n = m + m.
Proof.
  intros n H.
  induction H.
  exists 0; auto.
  destruct IHeven as [m IH].
  exists (S m); rewrite <-plus_n_Sm; simpl.
  repeat apply f_equal; assumption.
Qed.

(** Exercise 8.10 **)

Lemma ex_8_10:
  forall n:nat, even (n + n).
Proof.
  intros n.
  induction n.
  simpl; constructor.
  rewrite <-plus_n_Sm; simpl.
  constructor; assumption.
Qed.

(** Exercise 8.11 **)

Theorem lt_le:
  forall n p:nat, n < p -> n <= p.
Proof.
  unfold lt.
  intros n p H.
  apply le_Sn_le; assumption.
Qed.

(** Exercise 8.12 **)

(* Given *)

Definition my_le (n p:nat) :=
  forall P:nat -> Prop,
  P n -> (forall q:nat, P q -> P (S q)) -> P p.

(* To do *)

Lemma le_my_le:
  forall n p:nat, n <= p -> my_le n p.
Proof.
  unfold my_le.
  intros n p H.
  induction H.
  intros P H1 H2; exact H1.
  intros P H1 H2.
  apply H2, IHle; assumption.
Qed.

(** Exercise 8.13 **)

Lemma le_trans':
  forall n p q:nat, n <= p -> p <= q -> n <= q.
Proof.
  intros n p q H1 H2.
  induction H2.
  assumption.
  apply le_S; assumption.
Qed.

Lemma my_le_trans:
  forall n p q:nat, 
  my_le n p -> my_le p q -> my_le n q.
Proof.
  unfold my_le.
  intros n p q H1 H2.
  apply H2.
  assumption.
  intros r H3 P H5 H6.
  apply H6, H3; assumption.
Qed.

(** Exercise 8.14 **)

(* Given *)

Inductive le_diff (n m:nat) : Prop :=
  le_d: forall x:nat, x + n = m -> le_diff n m.

(* To do *)

Theorem le_equiv_le_diff:
  forall n m:nat, n <= m <-> le_diff n m.
Proof.
  intros n m.
  split.
  intros H1.
  induction H1.
  apply le_d with (x := 0); auto.
  destruct IHle as [x H2].
  apply le_d with (x := S x).
  simpl; rewrite H2; auto.
  intros H1.
  destruct H1 as [x H1].
  generalize m H1.
  clear H1 m.
  induction x.
  intros m H1.
  simpl in H1; rewrite H1; apply le_n.
  intros m H1.
  assert (m = S (pred m)) as H2.
  destruct m.
  simpl in H1; discriminate.
  simpl; auto.
  rewrite H2.
  apply le_S.
  apply IHx with (m := pred m).
  apply eq_add_S.
  rewrite <-H2.
  rewrite <-plus_Sn_m.
  exact H1.
Qed.

(** Exercise 8.15 **)

(* Given *)

Inductive le': nat -> nat -> Prop :=
  | le'_0_p: forall p:nat, le' 0 p
  | le'_Sn_Sp: 
      forall n p:nat, 
      le' n p -> le' (S n) (S p).

(* To do *)

Lemma le'_le_equiv:
  forall n m: nat, le' n m <-> le n m.
Proof.
  intros n m.
  split.
  intros H.
  induction H.
  apply le_0_n.
  apply le_n_S; assumption.
  intros H1.
  induction H1.
  induction n.
  constructor.
  constructor; assumption.
  cut (forall n m p:nat,
       le' n m -> le' (n + p) (m + p)).
  intros H2.
  cut (S m = (S m) - n + n).
  intros H3.
  rewrite H3, <-plus_O_n at 1.
  apply H2; constructor.
  rewrite plus_comm.
  apply le_plus_minus, le_S; assumption.
  intros n' m' p H2.
  induction p.
  repeat rewrite <-plus_n_O; exact H2.
  repeat rewrite <-plus_n_Sm.
  constructor; exact IHp.
Qed.

(* TO BE DONE *)

(** Exercise 8.16 **)

(* TO BE DONE *)

(** Exercise 8.17 **)

(* TO BE DONE *)

(** Exercise 8.18 **)

Section weird_induc_proof.

  Variable P: nat -> Prop.
  Variable f: nat -> nat.

  Hypothesis f_strict_mono:
    forall n p:nat, lt n p -> lt (f n) (f p).
  Hypothesis f_0: lt 0 (f 0).

  Hypothesis P0: P 0.
  Hypothesis P_Sn_n: 
    forall n:nat, P (S n) -> P n.
  Hypothesis f_P: forall n:nat, P n -> P (f n).

  Lemma sub_le_implies_equal:
    forall n m:nat, 
    n <= m /\ m - n = 0 -> n = m.
  Proof.
    intros n m [H1 H2].
    rewrite plus_n_O, <-H2 at 1.
    rewrite le_plus_minus_r;
      [reflexivity | assumption].
  Qed.

  Lemma minus_minus_le:
    forall n m:nat, n <= m -> n = m - (m - n).
  Proof.
    intros n m H1.
    apply plus_minus.
    rewrite plus_comm, <-le_plus_minus.
    reflexivity.
    assumption.
  Qed.

  Lemma lt_or_not_lt:
    forall n m:nat, n < m \/ ~(n < m).
  Proof.
    intros n m.
    cut (n < m \/ m <= n).
    intros [H1 | H2].
    left; exact H1.
    right; apply le_not_lt; exact H2.
    apply or_comm, le_or_lt.
  Qed.

  Lemma sub_succ_rel:
    forall n m:nat,
    S(m - S n) = m - n \/ m - S n = 0.
  Proof.
    intros n m.
    assert (n < m -> S(m - S n) = m - n) as H1.
    intros H1.
    rewrite minus_Sn_m.
    simpl; reflexivity.
    apply H1.
    assert (~(n < m) -> m - S n = 0) as H2.
    intros H2.
    apply not_le_minus_0; exact H2.
    cut ((n < m) \/ ~(n < m)).
    intros [H3 | H4].
    left; apply H1; exact H3.
    right; apply H2; exact H4.
    apply lt_or_not_lt.
  Qed.

  Lemma rev_induc_le:
    forall n m:nat,
    (n <= m /\ P m) -> P n.
  Proof.
    intros n m [H1 H2].
    cut (forall p:nat, P m -> P (m - p)).
    intros H3.
    rewrite minus_minus_le with (m := m).
    apply H3 with (p := m - n); assumption.
    assumption.
    induction p.
    intros H3.
    rewrite <-minus_n_O; assumption.
    cut (P(m - p)).
    intros H3 H4.
    cut (S(m - S p) = m - p \/ m - S p = 0).
    intros [H5 | H6].
    apply P_Sn_n.
    rewrite H5; apply H3.
    rewrite H6; apply P0.
    apply sub_succ_rel.
    apply IHp; apply H2.
  Qed.

  Lemma f_is_bigger:
    forall p:nat, p < f p.
  Proof.
    induction p.
    exact f_0.
    cut (S p <= f p /\ f p < f (S p)).
    intros [H1 H2].
    apply le_lt_trans with (m := f p);
      assumption.
    split.
    exact IHp.
    apply f_strict_mono, lt_n_Sn.
  Qed.

  Lemma induc_hyp:
    forall n:nat, P n -> P (S n).
  Proof.
    intros n H1.
    cut (S n <= f n).
    intros H2.
    apply rev_induc_le with (m := f n); split.
    assumption.
    apply f_P; assumption.
    apply f_is_bigger.
  Qed.

  Theorem weird_induc: forall n:nat, P n.
  Proof.
    induction n.
    apply P0.
    apply induc_hyp; exact IHn.
  Qed.

End weird_induc_proof.

(** Exercise 8.19 **)

Inductive wp': list par -> Prop :=
  | wp'_nil: wp' nil
  | wp'_cons: 
      forall (l1 l2:list par),
      wp' l1 -> wp' l2 ->
      wp' (cons open
                (app l1
                     (cons close l2))).

Lemma wp_has_first_par_comp:
  forall l: list par, 
  l <> nil -> wp l ->
  exists l1:list par,
  exists l2:list par,
  l = open :: l1 ++ close :: l2 /\ 
  wp l1 /\ wp l2.
Proof.
  intros l H1 H2.
  induction H2.
  apply False_ind, H1; reflexivity.
  exists l.
  exists nil.
  split.
  reflexivity.
  split.
  assumption.
  constructor.
  induction l.
  simpl.
  apply IHwp2.
  apply H1.
  assert (exists l1 : list par,
          exists l2 : list par,
          a :: l =
          open :: l1 ++
          close :: l2 /\
          wp l1 /\
          wp l2) as H3.
  apply IHwp1.
  discriminate.
  destruct H3 as [l3 [l4 [H3 [H4 H5]]]].
  assert (wp (l4 ++ l')) as H6.
  apply wp_c; assumption.
  exists l3.
  exists (l4 ++ l').
  rewrite H3.
  split.
  repeat rewrite app_comm_cons.
  repeat rewrite app_assoc.
  reflexivity.
  split; assumption.
Qed.

Lemma a_le_sum:
  forall a b:nat, a <= a + b.
Proof.
  intros a b.
  induction b.
  rewrite <-plus_n_O; apply le_n.
  rewrite <-plus_n_Sm; apply le_S; exact IHb.
Qed.

Lemma sum_le: 
  forall a b c:nat, 
  a + b <= c -> (a <= c) /\ (b <= c).
Proof.
  intros a b c H.
  cut ((a <= a + b) /\ (b <= a + b)).
  intros [H1 H2].
  split;
    apply le_trans
      with (m := a + b) (p := c);
    assumption.
  split.
  apply a_le_sum.
  rewrite plus_comm.
  apply a_le_sum with (a := b).
Qed.

Lemma wp_equiv_wp':
  forall l:list par, wp l <-> wp' l.
  cut (forall (n:nat) (l:list par),
       (length l <= n -> (wp l <-> wp' l))).
  intros H l.
  apply H with (n := S (length l)).
  apply le_S, le_n.
  intros n.
  induction n.
  intros l H.
  induction l.
  split; intros; constructor.
  simpl in H.
  apply False_ind; 
    apply le_Sn_0 with (n := length l);
    assumption.
  intros l H.
  split.
  intros H2.
  induction H2.
  constructor.
  apply wp'_cons.
  apply IHwp.
  cut (length (open :: l ++ close :: nil) =
       S(S(length l))).
  intros H3.
  do 2 apply le_S_n.
  rewrite <-H3.
  do 2 apply le_S.
  apply H.
  simpl.
  rewrite app_length; simpl.
  rewrite <-plus_n_Sm, <-plus_n_O.
  do 2 apply f_equal; reflexivity.
  constructor.
  cut (l ++ l' = nil \/
       (exists l1:list par,
        exists l2:list par,
        l ++ l' = open :: l1 ++ close :: l2 /\ 
        wp l1 /\ wp l2)).
  intros [H4 | H3].
  rewrite H4; constructor.
  destruct H3 as [l1 [l2 [H3 [H4 H5]]]].
  rewrite H3.
  cut (length l1 <= n /\ length l2 <= n).
  intros [H6 H7].
  apply wp'_cons.
  apply IHn; [exact H6 | exact H4].
  apply IHn; [exact H7 | exact H5].
  cut (length(open :: l1 ++ close :: l2) =
       S(S(length l1 + length l2))).
  intros H6.
  rewrite H3, H6 in H.
  cut (length l1 + length l2 <= n).
  intros H7.
  apply sum_le; exact H7.
  do 2 apply le_S_n.
  apply le_S; exact H.
  simpl.
  apply f_equal.
  rewrite app_length.
  simpl.
  rewrite <-plus_n_Sm.
  reflexivity.
  cut ((l ++ l' = nil) \/ (l ++ l' <> nil)).
  intros [H3 | H4].
  left; exact H3.
  right.
  apply wp_has_first_par_comp.
  exact H4.
  apply wp_c; assumption.
  case (l ++ l').
  left; reflexivity.
  intros p l0.
  right; discriminate.
  intros H2.
  induction H2.
  constructor.
  cut ((length l1 <= n) /\ (length l2 <= n)).
  intros [H3 H4].
  cut (open :: l1 ++ close :: l2 =
       (open :: l1 ++ close :: nil) ++ l2).
  intros H5.
  rewrite H5.
  apply wp_c.
  apply wp_p.
  apply IHn; [exact H3 | exact H2_].
  apply IHn; [exact H4 | exact H2_0].
  cut (forall (p:par) (l:list par),
       p :: l = (p :: nil) ++ l).
  intros H5. 
  rewrite H5 with (p := close) (l := l2).
  rewrite H5
    with (p := open) 
         (l := l1 ++ (close :: nil) ++ l2).
  rewrite H5
    with (p := open) 
         (l := l1 ++ (close :: nil)).
  repeat rewrite app_assoc.
  reflexivity.
  intros p l; simpl; reflexivity.
  cut (length (open :: l1 ++ close :: l2) =
       S(S(length l1 + length l2))).
  intros H3.
  apply sum_le.
  do 2 apply le_S_n.
  rewrite <-H3.
  apply le_S; exact H.
  simpl; apply f_equal.
  rewrite app_length; simpl.
  rewrite plus_n_Sm; reflexivity.
Qed.

(* A VERY BIG AND COMPLEX PROOF. IT CAN PROBABLY
   BE IMPROVED A LOT... *)

(** Exercise 8.20 **)

(* Given *)

Inductive wp'': list par -> Prop :=
  | wp''_nil: wp'' nil
  | wp''_cons:
      forall l1 l2:list par,
      wp'' l1 -> wp'' l2 ->
      wp'' (app l1
                (cons open
                      (app l2
                           (cons close nil)))).

Lemma wp_has_last_par_comp:
  forall l: list par, 
  l <> nil -> wp l ->
  exists l1:list par,
  exists l2:list par,
  l = l1 ++ open :: l2 ++ close :: nil /\
  wp l1 /\ wp l2.
Proof.
  intros l H1 H2.
  induction H2.
  apply False_ind, H1; reflexivity.
  exists nil.
  exists l.
  split; [auto | split; auto]; apply wp_e.
  induction l'.
  rewrite app_nil_r.
  apply IHwp1.
  rewrite app_nil_r in H1; exact H1.
  remember (a :: l') as l''.
  cut (exists l1:list par,
       exists l2:list par,
       (l'' =
        l1 ++ open :: l2 ++ close :: nil) /\
       wp l1 /\ wp l2).
  intros [l1 [l2 [H3 [H4 H5]]]].
  exists (l ++ l1).
  exists l2.
  split.
  rewrite H3.
  apply app_assoc.
  split; [apply wp_c; assumption | assumption].
  apply IHwp2.
  rewrite Heql''; discriminate.
Qed.

Lemma len_le_zero_is_nil:
  forall l:list par, length l <= 0 <-> l = nil.
Proof.
  intros l.
  case l.
  split; intros;
    [reflexivity | simpl; apply le_n].
  simpl; split; intros.
  apply False_ind; 
    apply le_Sn_O with (n := length l0);
    assumption.
  discriminate.
Qed.

Lemma cons_lens_equiv:
  forall l l1 l2:list par,
  l = l1 ++ (open :: l2) ++ close :: nil ->
  length l = S(S(length l1 + length l2)).
Proof.
  intros l l1 l2 H.
  rewrite H.
  repeat rewrite app_length; simpl.
  repeat rewrite <-plus_n_Sm.
  rewrite <-plus_n_O.
  reflexivity.
Qed.

Lemma comp_len_val:
  forall l l1 l2 l3:list par,
  l = l1 ++ (open :: nil) ++ l2 ++
      (close :: nil) ++ l3 ->
  length l = 
  S(S(length l1 + length l2 + length l3)).
Proof.
  intros l l1 l2 l3 H.
  rewrite H.
  repeat rewrite app_length; simpl.
  repeat rewrite <-plus_n_Sm.
  repeat rewrite plus_assoc.
  reflexivity.
Qed.

Lemma sum_3_le: 
  forall n m p: nat, n <= n + m + p.
Proof.
  intros n m p.
  cut (0 <= m + p).
  intros H.
  rewrite plus_n_O with (n := n) at 1.
  rewrite <-plus_assoc.
  apply plus_le_compat_l; exact H.
  apply le_O_n.
Qed.

Lemma comp_len_ineq:
  forall l l1 l2 l3:list par,
  l = l1 ++ (open :: nil) ++ l2 ++
      (close :: nil) ++ l3 ->
  length l1 < length l /\
  length l2 < length l /\
  length l3 < length l.
Proof.
  intros l l1 l2 l3 H1.
  cut (length l = 
       S(S(length l1 + length l2 + length l3))).
  intros H2.
  rewrite H2; unfold lt.
  split.
  apply le_n_S, le_S.
  apply sum_3_le.
  split.
  rewrite plus_comm with (n := length l1).
  apply le_n_S, le_S.
  apply sum_3_le.
  rewrite plus_comm.
  apply le_n_S, le_S.
  rewrite plus_assoc.
  apply sum_3_le.
  apply comp_len_val; exact H1.
Qed.

Lemma le_drop:
  forall n m p:nat, n + m <= p -> n <= p.
Proof.
  intros n m p H.
  induction m.
  rewrite plus_n_O with (n := n); exact H.
  apply IHm, le_Sn_le.
  rewrite plus_n_Sm; exact H.
Qed.

Lemma wp_equiv_wp'':
  forall l:list par, wp l <-> wp'' l.
Proof.
  (* we need to get a stronger induction
     hypothesis *)
  cut (forall (n:nat) (l:list par),
       (length l <= n -> (wp l <-> wp'' l))).
  (* first we get the desired result from the
     induction hypothesis *)
  intros H l.
  apply H with (n := length l); apply le_n.
  intros n.
  (* then we do the induction *)
  induction n.
  (* the nil case is very easy *)
  intros l H.
  cut (l = nil).
  intros.
  split; intros; rewrite H0; constructor.
  apply len_le_zero_is_nil; assumption.
  (* now we need to do the inductive step *)
  intros l H1.
  split.
  intros H2.
  (* we use structural induction *)
  induction H2.
  (* the nil case of wp is trivial *)
  constructor.
  (* we handle the single parenthesized
     expression using a nil prefix *)
  apply wp''_cons with (l1 := nil).
  constructor.
  (* now we just have to find a way to apply
     the structural recursion *)
  cut (length l <= S n).
  exact IHwp.
  cut (length (open :: l ++ close :: nil) =
       S(S(length l))).
  intros H3.
  do 2 apply le_S_n.
  rewrite <-H3.
  do 2 apply le_S.
  exact H1.
  (* now it's just a question of relating the
     list lengths *)
  rewrite app_comm_cons.
  rewrite app_length; simpl.
  rewrite <-plus_n_Sm, <-plus_n_O.
  reflexivity.
  (* for the concatenation case, we use the fact
     that, if l' is not nil, it should have
     a well-parenthesized expression as a 
     suffix *)
  (* let's start by disposing of the nil case *)
  induction l'.
  rewrite app_nil_r.
  apply IHwp1.
  rewrite app_nil_r in H1.
  exact H1.
  remember (a :: l') as l''.
  cut (l'' <> nil).
  intros H3.
  (* now we can assume that l'' is not nil *)
  (* let's start with the fact that it ends with
     a well-parenthesized expression *)
  cut (exists l1:list par,
       exists l2:list par,
       l'' = l1 ++
             open :: l2 ++
             close :: nil /\
             wp l1 /\ wp l2).
  intros [l1 [l2 [H4 [H5 H6]]]].
  rewrite H4.
  rewrite app_assoc.
  (* now it's ready to apply the constructor *)
  apply wp''_cons.
  (* we can only apply the inductive hypothesis
     over the term lengths here *)
  cut (length (l ++ l1) <= n).
  intros H7.
  apply IHn.
  exact H7.
  apply wp_c; assumption.
  (* now it's boring length inequalities 
     again... *)
  cut (length (l ++ l1 ++ open :: l2 ++
               close :: nil) <= S n).
  intros H7.
  repeat rewrite app_length in H7.
  simpl in H7.
  rewrite app_length; simpl.
  repeat rewrite <-plus_n_Sm in H7.
  assert (length l +
          (length l1 +
           length (l2 ++ close :: nil)) <= n)
    as H8.
  apply le_S_n; exact H7.
  rewrite plus_assoc in H8.
  apply le_drop 
    with (m := length (l2 ++ close :: nil)).
  exact H8.
  rewrite H4 in H1.
  exact H1.
  (* now we need to do the same with the other
     term *)
  cut (length l2 <= n).
  intros H7.
  apply IHn.
  exact H7.
  exact H6.
  cut (length l'' <= S n).
  intros H7.
  cut (length l'' =
       S(S(length l1 + length l2))).
  intros H8.
  rewrite H8 in H7.
  apply le_drop with (m := length l1).
  rewrite plus_comm.
  apply le_Sn_le, le_S_n; exact H7.
  rewrite H4.
  rewrite app_comm_cons.
  repeat rewrite app_length; simpl.
  repeat rewrite <-plus_n_Sm.
  rewrite <-plus_n_O; reflexivity.
  apply le_drop with (m := length l).
  rewrite plus_comm.
  rewrite <-app_length; exact H1.
  apply wp_has_last_par_comp.
  exact H3.
  exact H2_0.
  rewrite Heql''.
  discriminate.
  (* now we need to do the other direction,
     it should be easier *)
  intros H2.
  induction H2.
  apply wp_e.
  set (l1 ++ open :: l2 ++ close :: nil) as l.
  cut (length l1 < length l /\
       length l2 < length l /\
       length nil (A := par) < length l).
  intros [H3 [H4 _]].
  apply wp_c;
    [apply IHwp''1 | apply wp_p; apply IHwp''2];
    apply lt_le_weak; 
    apply lt_le_trans
      with (m := length l) (p := S n);
    assumption.
  apply comp_len_ineq.
  rewrite app_nil_r; reflexivity.
Qed.

(** Exercise 8.21 **)

(* Given *)

Fixpoint recognize (n:nat) (l:list par)
  {struct l}: bool :=
  match l with
  | nil => match n with
           | 0 => true
           | _ => false
           end
  | cons open l' => recognize (S n) l'
  | cons close l' => match n with
                     | 0 => false
                     | S n' => recognize n' l'
                     end
  end.

(* To do *)

Theorem recognize_complete_aux:
  forall l:list par, wp l ->
  forall (n:nat) (l':list par),
  recognize n (app l l') = recognize n l'.
Proof.
  intros l H.
  induction H.
  intros; rewrite app_nil_l; reflexivity.
  intros; simpl.
  rewrite <-app_assoc, IHwp; reflexivity.
  intros; simpl.
  rewrite <-app_assoc, IHwp1, IHwp2; reflexivity.
Qed.

Theorem recognize_complete:
  forall l:list par,
  wp l -> recognize 0 l = true.
Proof.
  intros l H.
  rewrite <-app_nil_r with (l := l),
          recognize_complete_aux 
            with (l' := nil); auto.
Qed.

(** Exercise 8.22 **)

Theorem recognize_sound:
  forall l:list par,
  recognize 0 l = true -> wp l.
  