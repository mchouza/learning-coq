(** Definition **)

Inductive month : Set :=
| January   | February | March    | April
| May       | June     | July     | August
| September | October  | November | December.

(** Exercise 6.1 **)

Inductive season : Set :=
| Winter | Spring | Summer | Autumn.

Definition assign_season (m:month) : season :=
  match m with
  | January => Summer   | February => Summer
  | March => Summer     | April => Autumn
  | May => Autumn       | June => Autumn
  | July => Winter      | August => Winter
  | September => Winter | October => Spring
  | November => Spring  | December => Spring
  end.

Definition assign_season_2 (m:month) :=
  month_rec (fun m:month => season)
  Summer Summer Summer
  Autumn Autumn Autumn
  Winter Winter Winter
  Spring Spring Spring.

(** Exercise 6.2 **)

(* bool_ind should be
   forall P:bool->Prop,
   P false -> P true ->
   forall b:bool, P b. *)
Check bool_ind.

(* bool_rec should be the same with Set 
   replacing Prop *)
Check bool_rec.

(** Exercise 6.3 **)

(* bool_ind : 
   forall P : bool -> Prop,
   P true -> P false ->
   forall b : bool, P b *)

(* so, to construct our proof term, we need to
   find our P, that should have type
   bool -> Prop and applied over b should have
   the result b = true \/ b = false *)

Check (fun b:bool => b = true \/ b = false).

(* now we need to build a proof that P true *)
(* it will have type
   true = true \/ true = false *)
Check (or_introl (true=false)
                 (eq_refl true)).

(* finally, we need a proof that P false *)
Check (or_intror (false=true)
                 (eq_refl false)).

(* putting all together *)
Check (bool_ind (fun b:bool =>
                 b = true \/ b = false)
                (or_introl (true=false)
                 (eq_refl true))
                (or_intror (false=true)
                 (eq_refl false))).

Theorem bool_equal_1: 
  forall b:bool, b = true \/ b = false.
Proof bool_ind (fun b:bool =>
                b = true \/ b = false)
               (or_introl (true=false)
                          (eq_refl true))
               (or_intror (false=true)
                          (eq_refl false)).

Theorem bool_equal_2:
  forall b:bool, b = true \/ b = false.
Proof.
  apply bool_ind.
  left; reflexivity.
  right; reflexivity.
Qed.

(** Exercise 6.4 **)

(* Already done that way *)

(** Exercise 6.5 **)

Definition even_days (m:month) (leap:bool) :=
  match m with
  | February => if leap then false else true
  | April => true     | June => true
  | September => true | November => true
  | _ => false
  end.

(** Exercise 6.6 **)

Definition bool_xor (b1 b2:bool) : bool :=
  match b1, b2 with
  | false, false => false
  | false, true => true
  | true, false => true
  | true, true => false
  end.

Definition bool_and (b1 b2:bool) : bool :=
  match b1, b2 with
  | true, true => true
  | _, _ => false
  end.

Definition bool_or (b1 b2:bool) : bool :=
  match b1, b2 with
  | false, false => false
  | _, _ => true
  end.

Definition bool_eq (b1 b2:bool) : bool :=
  match b1, b2 with
  | false, false => true
  | true, true => true
  | _, _ => false
  end.

Definition bool_not (b:bool) : bool :=
  match b with
  | false => true
  | true => false
  end.

Theorem ex_6_6_1:
  forall b1 b2:bool,
  bool_xor b1 b2 = bool_not (bool_eq b1 b2).
Proof.
  intros b1 b2.
  elim b1; elim b2; simpl; reflexivity.
Qed.

Theorem ex_6_6_2:
  forall b1 b2:bool,
  bool_not (bool_and b1 b2) =
  bool_or (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2.
  elim b1; elim b2; simpl; reflexivity.
Qed.

Theorem ex_6_6_3:
  forall b:bool, bool_not (bool_not b) = b.
Proof.
  intro b.
  elim b; simpl; reflexivity.
Qed.

Theorem ex_6_6_4:
  forall b:bool, bool_or b (bool_not b) = true.
Proof.
  intro b.
  elim b; simpl; reflexivity.
Qed.

Theorem ex_6_6_5:
  forall b1 b2:bool,
  bool_eq b1 b2 = true -> b1 = b2.
Proof.
  intros b1 b2.
  elim b1; elim b2; simpl; auto.
Qed.

Theorem ex_6_6_6:
  forall b1 b2:bool,
  b1 = b2 -> bool_eq b1 b2 = true.
Proof.
  intros b1 b2.
  elim b1; elim b2; simpl; auto.
Qed.

Theorem ex_6_6_7:
  forall b1 b2:bool,
  bool_not (bool_or b1 b2) =
  bool_and (bool_not b1) (bool_not b2).
Proof.
  intros b1 b2.
  elim b1; elim b2; simpl; reflexivity.
Qed.

Theorem ex_6_6_8:
  forall b1 b2 b3:bool,
  bool_or (bool_and b1 b3) (bool_and b2 b3) =
  bool_and (bool_or b1 b2) b3.
Proof.
  intros b1 b2 b3.
  elim b1; elim b2; elim b3; simpl; reflexivity.
Qed.

(** Exercise 6.7 **)

(* Definitions *)

Require Import ZArith.

Record plane : Set := 
  point { abscissa : Z; ordinate : Z }.

(* To solve *)

(* The type of plane_rec should be
   forall P:plane -> Set,
     (forall abscissa ordinate:Z, 
      P (point abscissa ordinate)) ->
     (forall p:plane, P p) *)
Check plane_rec.
(* Seem similar *)

(** Exercise 6.8 **)

Definition manhattan (p q:plane) : Z :=
  Zplus
  (Zabs ((abscissa p) - (abscissa q)))
  (Zabs ((ordinate p) - (ordinate q))).

Eval compute in (manhattan (point 5 8)
                           (point 1 34)).

(** Exercise 6.9 **)

(* Given *)

Inductive vehicle : Set :=
    bicycle : nat -> vehicle 
  | motorized : nat -> nat -> vehicle.

(* Solve *)

(* The type of vehicle_rec should be
   forall P:vehicle -> Set,
     (forall n:nat, P (bicycle n)) ->
     (forall n n0:nat, P (motorized n n0)) ->
   forall v:vehicle, P v *)

Definition nb_seats (v:vehicle) :=
  (vehicle_rec (fun v:vehicle => nat)
               (fun n:nat => n)
               (fun n _:nat => n)) v.

Eval compute in (nb_seats (bicycle 3)).
Eval compute in (nb_seats (motorized 4 5)).

(** Exercise 6.10 **)

Check month_rect.

Definition is_January (m:month) :=
  month_rect (fun m:month => Prop)
  True  False False False False False
  False False False False False False
  m.

Eval compute in (is_January January).

Eval compute in (is_January October).

(** Exercise 6.11 **)

Theorem false_is_not_true: true <> false.
Proof.
  unfold not; intros.
  change ((fun b:bool => match b with
           | true => True
           | false => False
           end) false).
  rewrite <-H.
  trivial.
Qed.

(** Exercise 6.12 **)

Theorem bicycles_are_not_motorized:
  forall m n1 n2:nat,
  bicycle m <> motorized n1 n2.
Proof.
  unfold not; intros.
  change ((fun v:vehicle => 
           match v with
           | bicycle m => True
           | _ => False
           end) (motorized n1 n2)).
  rewrite <-H.
  trivial.
Qed.

(** Exercise 6.13 **)

Require Import Arith.

(* COMMENTED BECAUSE TO AVOID LEAVING False
   PROVED

Record RatPlus : Set :=
  mkRat {top:nat; bottom:nat; 
         bottom_condition: bottom <> 0}.

Axiom eq_RatPlus : 
  forall r r':RatPlus,
    top r * bottom r' = top r' * bottom r ->
    r = r'.

Theorem tnt: False.
Proof.
  assert (2<>0) as H1; auto.
  assert (4<>0) as H2; auto.
  assert ((mkRat 1 2 H1) = (mkRat 2 4 H2))
         as H3.
  apply eq_RatPlus; simpl; auto.
  assert ((mkRat 1 2 H1) <> (mkRat 2 4 H2))
         as H4.
  discriminate.
  apply H4; assumption.
Qed.

*)

(** Exercise 6.14 **)

(*
(mult 0 0) -> 0 (first rule)
(mult 0 m) -> 0 (first rule)
(mult (S n) 0) -> 0 + mult n 0 (second rule)
(mult 0 (S m)) -> 0 (first rule)
(mult (S n) m) -> m + mult n m (second rule)
(mult (S(S n)) m) -> m + mult (S n) m 
  (second rule)
*)

(** Exercise 6.15 **)

Fixpoint true_if_lt_3 (n:nat) : bool :=
  match n with
  | S (S (S p)) => false
  | _ => true
  end.

Eval compute in (true_if_lt_3 0).
Eval compute in (true_if_lt_3 1).
Eval compute in (true_if_lt_3 2).
Eval compute in (true_if_lt_3 3).
Eval compute in (true_if_lt_3 4).

(** Exercise 6.16 **)

Fixpoint add_2nd (n m:nat) : nat :=
  match m with
  | 0 => n
  | S p => S(add_2nd n p)
  end.

Eval compute in (add_2nd 0 0).
Eval compute in (add_2nd 4 0).
Eval compute in (add_2nd 0 3).
Eval compute in (add_2nd 3 2).

(** Exercise 6.17 **)

Require Import Znat.

Fixpoint sum_f (n:nat) (f:nat->Z) : Z :=
  match n with
  | 0 => f 0
  | S p => Zplus (f (S p)) (sum_f p f)
  end.

Eval compute in
  (sum_f 5 
         (fun p:nat => Z_of_nat(p * p + 1))).
Eval compute in (1+2+5+10+17+26).
(* 61 = 1 + 2 + 5 + 10 + 17 + 26 *)

(** Exercise 6.18 **)

Fixpoint two_power (n:nat) : nat :=
  match n with
  | 0 => 1
  | S p => 2 * (two_power p)
  end.

Eval compute in (two_power 0).
Eval compute in (two_power 1).
Eval compute in (two_power 2).
Eval compute in (two_power 7).
Eval compute in (two_power 9).

(** Exercise 6.19 **)

(* 1000 = 512 + 256 + 128 + 64 + 32 + 8 *)
Eval compute in (xO (xO (xO (xI (xO (xI (xI
                (xI (xI xH))))))))).

(* 25 = 16 + 8 + 1 *)
Eval compute in (xI (xO (xO (xI xH)))).

(* 512 = 512 *)
Eval compute in (xO (xO (xO (xO (xO (xO (xO
                (xO (xO xH))))))))).

(** Exercise 6.20 **)

Definition pos_even_bool (n:positive) : bool :=
  match n with
  | xO p => true
  | _ => false
  end.

Eval compute in (pos_even_bool 391372%positive).
Eval compute in (pos_even_bool 757575%positive).
Eval compute in (pos_even_bool 1%positive).

(** Exercise 6.21 **)

Definition pos_div_4 (n:positive) : Z :=
  match n with
  | xO ( xO p ) => Zpos p
  | xO ( xI p ) => Zpos p
  | xI ( xO p ) => Zpos p
  | xI ( xI p ) => Zpos p
  | _ => 0%Z
  end.

Eval compute in (pos_div_4 100).
Eval compute in (pos_div_4 101).
Eval compute in (pos_div_4 102).
Eval compute in (pos_div_4 103).
Eval compute in (pos_div_4 104).
Eval compute in (pos_div_4 1).
Eval compute in (pos_div_4 2).
Eval compute in (pos_div_4 3).
Eval compute in (pos_div_4 4).

(** Exercise 6.22 **)

Definition pos_mult(n m:positive) : positive :=
  match Zmult (Zpos n) (Zpos m) with
  | Zpos p => p
  | _ => 1%positive (* WON'T HAPPEN *)
  end.

Eval compute in 
  (pos_mult 30%positive 41%positive).

Definition Z_new_mult(n m:Z) : Z :=
  match n, m with
  | Zpos p, Zpos q => Zpos (pos_mult p q)
  | Z0, _ => 0%Z
  | _, Z0 => 0%Z
  | Zneg p, Zneg q => Zpos (pos_mult p q)
  | Zpos p, Zneg q => Zneg (pos_mult p q)
  | Zneg p, Zpos q => Zneg (pos_mult p q)
  end.

Eval compute in (Z_new_mult 0 0).
Eval compute in (Z_new_mult 23 0).
Eval compute in (Z_new_mult 23 23).
Eval compute in (Z_new_mult 0 23).
Eval compute in (Z_new_mult 0 (-23)).
Eval compute in (Z_new_mult (-23) 0).
Eval compute in (Z_new_mult (-23) (-23)).
Eval compute in (Z_new_mult (-23) 23).
Eval compute in (Z_new_mult 23 (-23)).

(** Exercise 6.23 **)

Inductive L : Set :=
  | L_False
  | L_True
  | L_and : L -> L -> L
  | L_or : L -> L -> L
  | L_implies : L -> L -> L
  | L_not : L -> L.

Check (L_and (L_not L_False) 
             (L_or L_True L_False)).

(** Exercise 6.24 **)

Inductive my_Rat : Set :=
  | mrOne
  | mrN : my_Rat -> my_Rat
  | mrD : my_Rat -> my_Rat.

(** Exercise 6.25 **)

(* Definition *)

Inductive Z_btree : Set :=
  | Z_leaf : Z_btree
  | Z_bnode : Z -> Z_btree -> Z_btree -> Z_btree.

(* To do *)

Fixpoint value_present 
         (value:Z) (tree:Z_btree) : bool :=
  match tree with
  | Z_leaf => false
  | Z_bnode v l r =>
    if (Zeq_bool value v)
    then true
    else 
      if (value_present value l)
      then true
      else (value_present value r)
  end.

Eval compute in 
(value_present 
  3
  (Z_bnode 5
    (Z_bnode 3 Z_leaf Z_leaf)
    (Z_bnode 4 Z_leaf Z_leaf))).

Eval compute in 
(value_present 
  4
  (Z_bnode 5
    (Z_bnode 3 Z_leaf Z_leaf)
    (Z_bnode 4 Z_leaf Z_leaf))).

Eval compute in 
(value_present 
  7
  (Z_bnode 5
    (Z_bnode 3 Z_leaf Z_leaf)
    (Z_bnode 4 Z_leaf Z_leaf))).

(** Exercise 6.26 **)

Fixpoint power (base:Z) (exp:nat) : Z :=
  match exp with
  | O => 1%Z
  | S p => Zmult base (power base p)
  end.

Eval compute in (power (-2) 5).

Fixpoint discrete_log (p:positive) : nat :=
  match p with
  | xO q => 1 + discrete_log q
  | xI q => 1 + discrete_log q
  | xH => 0
  end.

Eval compute in (discrete_log 1).
Eval compute in (discrete_log 2).
Eval compute in (discrete_log 3).
Eval compute in (discrete_log 4).
Eval compute in (discrete_log 7).
Eval compute in (discrete_log 8).
Eval compute in (discrete_log 1023).
Eval compute in (discrete_log 1024).
Eval compute in (discrete_log 1025).

(** Exercise 6.27 **)

(* Given *)

Inductive Z_fbtree : Set :=
  | Z_fleaf : Z_fbtree
  | Z_fnode : Z->(bool->Z_fbtree)->Z_fbtree.

(* To do *)

Fixpoint fzero_present (t:Z_fbtree) : bool :=
  match t with
  | Z_fleaf => false
  | Z_fnode v f => 
      if (Zeq_bool v 0) 
      then true 
      else
        if fzero_present (f true)
        then true
        else fzero_present (f false)
  end.

(* to easily build functions from bool to 
   trees *)
Definition bbf (t f:Z_fbtree) :
           (bool -> Z_fbtree) :=
  bool_rec (fun b:bool => Z_fbtree) t f.

Eval compute in
  (fzero_present 
     (Z_fnode 
       3
       (bbf Z_fleaf
            (Z_fnode
              5
              (bbf Z_fleaf Z_fleaf))))).

Eval compute in
  (fzero_present 
     (Z_fnode 
       3
       (bbf Z_fleaf
            (Z_fnode
              0
              (bbf Z_fleaf Z_fleaf))))).

(** Exercise 6.28 **)

(* Given *)

Inductive Z_inf_branch_tree : Set :=
  | Z_inf_leaf : Z_inf_branch_tree
  | Z_inf_node :
      Z->(nat->Z_inf_branch_tree)->
        Z_inf_branch_tree.

(* To do *)

Fixpoint n_check_if_true
  (n:nat) (f:nat->bool) : bool :=
  match n with
  | O => f O
  | S m => if f (S m)
           then true
           else n_check_if_true m f
  end.

Fixpoint n_zero_present
  (n:nat) (t:Z_inf_branch_tree) : bool :=
  match t with
  | Z_inf_leaf => false
  | Z_inf_node v f =>
      if (Zeq_bool v 0)
      then true
      else
        (n_check_if_true
           n
           (fun x:nat => 
            n_zero_present n (f x)))
  end.

(* TODO: ADD TESTS!!! *)

(** Exercise 6.29 **)

Theorem plus_n_O: forall n:nat, n = n + 0.
Proof.
  intros n.
  elim n.
  simpl; reflexivity.
  intros m H.
  simpl.
  apply f_equal.
  apply H.
Qed.

(** Exercise 6.30 **)

(* TO BE DONE AFTER UPLOADING 6.27 & 6.28 *)

(** Exercise 6.31 **)

(* Given *)

Fixpoint mult2 (n:nat) : nat :=
  match n with
  | 0 => 0
  | S p => S (S (mult2 p))
  end.

(* To be done *)

Theorem mult_2_eq_add_itself:
  forall n:nat, (mult2 n) = n + n.
Proof.
  intros n.
  elim n.
  simpl; reflexivity.
  intros n0 H.
  simpl.
  rewrite plus_comm.
  simpl; repeat apply f_equal.
  exact H.
Qed.

(** Exercise 6.32 **)

(* Given *)

Fixpoint sum_n (n:nat) : nat :=
  match n with
  | 0 => 0
  | S p => S p + sum_n p
  end.

(* To be done *)

Eval compute in (sum_n 5).

Lemma plus_n_Sm:
  forall n m:nat, n + S m = S(n + m).
Proof.
  intros n m.
  rewrite plus_comm.
  simpl; apply f_equal; apply plus_comm.
Qed.

Theorem sum_arith_prog:
  forall n:nat, 2 * sum_n n = n * n + n.
Proof.
  intros n.
  elim n.
  simpl; reflexivity.
  intros p H.
  simpl; apply f_equal.
  rewrite <-plus_n_O.
  rewrite mult_comm; simpl.
  rewrite <-plus_assoc.
  repeat rewrite plus_n_Sm; apply f_equal.
  rewrite plus_comm with (n := p) (m := p * p).
  rewrite <-H.
  simpl; rewrite <-plus_n_O.
  rewrite plus_comm with (n := p) (m := sum_n p).
  repeat rewrite plus_assoc; reflexivity.
Qed.

(* there is probably a much shorter proof... *)

(** Exercise 6.33 **)

Lemma le_rem_S:
  forall n m: nat, n <= m -> S n <= S m.
Proof.
  intros n m H.
  elim H.
  apply le_n.
  intros p H2 H3.
  apply le_S.
  exact H3.
Qed.

Lemma le_add_right:
  forall n m p:nat, n <= m -> n <= m + p.
Proof.
  intros n m p H.
  elim p.
  rewrite <-plus_n_O; exact H.
  intros q H2.
  rewrite plus_n_Sm; apply le_S; exact H2.
Qed.

Lemma ex_6_33: forall n:nat, n <= sum_n n.
Proof.
  intros n.
  elim n.
  simpl; apply le_n.
  intros m H.
  simpl.
  apply le_rem_S.
  rewrite plus_comm.
  apply le_add_right; exact H.
Qed.

(** Exercise 6.34 **)

Require Import List.

Definition first_two_elems {A:Set} (l:list A) :=
  match l with
  | f :: s :: tail => f :: s :: nil
  | _ => nil
  end.

Compute first_two_elems (1 :: 2 :: 3 :: nil).
Compute first_two_elems (1 :: 2 :: nil).
Compute first_two_elems (1 :: nil).
Compute first_two_elems (nil (A:=nat)).

(** Exercise 6.35 **)

Fixpoint first_n_elems {A:Set} (l:list A) (n:nat) : list A :=
  match n, l with
  | O, _ => nil
  | _, nil => nil
  | S p, h :: t => h :: first_n_elems t p
  end.

Compute first_n_elems (1 :: 2 :: 3 :: nil) 2.
Compute first_n_elems (1 :: 2 :: 3 :: nil) 3.
Compute first_n_elems (1 :: 2 :: 3 :: nil) 4.

(** Exercise 6.36 **)

Fixpoint sum_integer_list (l:list Z) : Z :=
  match l with
  | nil => 0%Z
  | h :: t => Zplus h (sum_integer_list t)
  end.

Compute sum_integer_list (nil (A:=Z)).
Compute sum_integer_list (1%Z :: 2%Z :: 3%Z :: nil).

(** Exercise 6.37 **)

Fixpoint list_n_ones (n:nat) : list nat :=
  match n with
  | O => nil
  | S p => 1 :: list_n_ones p
  end.

Compute list_n_ones 0.
Compute list_n_ones 1.
Compute list_n_ones 2.
Compute list_n_ones 3.

(** Exercise 6.38 **)

Fixpoint _list_n_arith_aux (n m:nat) : list nat :=
  match n with
  | O => nil
  | S p => ((m + 1) - n) :: _list_n_arith_aux p m
  end.

Definition list_n_arith (n:nat) : list nat :=
  _list_n_arith_aux n n.

Compute list_n_arith 0.
Compute list_n_arith 1.
Compute list_n_arith 3.
Compute list_n_arith 5.

(** Exercise 6.39 **)

(* Given *)

Fixpoint nth_option (A:Set)(n:nat)(l:list A)
  {struct l} :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

(* To do *)

Fixpoint nth_option' (A:Set)(n:nat)(l:list A)
  {struct n} :=
  match n, l with
  | O, cons a tl => Some a
  | S p, cons a tl => nth_option A p tl
  | n, nil => None
  end.

Theorem nth_option_equiv:
  forall (A:Set) (n:nat) (l:list A),
  nth_option A n l = nth_option' A n l.
Proof.
  intros A n l.
  elim n.
  elim l; simpl; reflexivity.
  intros m H.
  elim l; simpl; reflexivity.
Qed.

(** Exercise 6.40 **)

(* TO BE DONE *)

(** Exercise 6.41 **)

Fixpoint ex_6_41 (A:Set) (f:A->bool) 
  (l:list A) : option A :=
  match l with
  | nil => None
  | h :: t => if (f h) 
              then Some h
              else ex_6_41 A f t
  end.

Compute (ex_6_41 Z
                 (fun (n:Z) => (Zeq_bool n 7))
                 (1 :: 9 :: 5 :: 6 :: nil)%Z).

Compute (ex_6_41 Z
                 (fun (n:Z) => (Zeq_bool n 7))
                 (1 :: 9 :: 7 :: 6 :: nil)%Z).


(** Exercise 6.42 **)

Fixpoint map (A B:Set) (l:list A) (f:A->B) :=
  match l with
  | h :: t => (f h) :: (map A B t f)
  | nil => nil
  end.

Fixpoint split (A B:Set) (l:list (A*B)):
  list A * list B :=
  (map (A*B) A l (fst (A := A) (B := B)),
   map (A*B) B l (snd (A := A) (B := B))).

Fixpoint combine 
  (A B:Set) (la:list A) (lb:list B):
  list (A*B) :=
  match la, lb with
  | nil, _ => nil
  | _, nil => nil
  | ha :: ta, hb :: tb =>
    (ha, hb) :: combine A B ta tb
  end.

Lemma pair_first_snd:
  forall (A B:Set) (ab:(A*B)),
  ab = (fst ab, snd ab).
Proof.
  intros A B ab.
  elim ab.
  intros a b.
  simpl; reflexivity.
Qed.

Lemma split_first_as_map:
  forall (A B:Set) (lab:list (A*B)),
  fst (split A B lab) =
    map (A*B) A lab (fst (A:=A) (B:=B)).
Proof.
  intros A B lab.
  elim lab.
  simpl; reflexivity.
  intros a l H.
  simpl.
  reflexivity.
Qed.

Lemma split_second_as_map:
  forall (A B:Set) (lab:list (A*B)),
  snd (split A B lab) =
    map (A*B) B lab (snd (A:=A) (B:=B)).
Proof.
  intros A B lab.
  elim lab.
  simpl; reflexivity.
  intros a l H.
  simpl.
  reflexivity.
Qed.

Theorem split_combine:
  forall (A B:Set) (lab:list (A*B)),
  lab = combine A B (fst (split A B lab))
                    (snd (split A B lab)).
Proof.
  intros A B lab.
  elim lab.
  simpl; reflexivity.
  intros a l H.
  unfold combine, split, map.
  simpl.
  fold map.
  fold combine.
  rewrite <-pair_first_snd with (ab := a).
  rewrite <-split_first_as_map.
  rewrite <-split_second_as_map.
  rewrite <-H.
  reflexivity.
Qed.

(** Exercise 6.43 **)

Inductive btree (A:Set) : Set :=
  | btree_leaf : (btree A)
  | btree_node :
      A -> (btree A) -> (btree A) -> (btree A).

Fixpoint z_btree_from_polym (t:btree Z) := 
  match t with
  | btree_leaf => Z_leaf
  | btree_node v l r =>
      Z_bnode v 
              (z_btree_from_polym l)
              (z_btree_from_polym r)
  end.

Fixpoint polym_from_z_btree (t:Z_btree) :=
  match t with
  | Z_leaf => (btree_leaf Z)
  | Z_bnode v l r =>
      (btree_node Z
                  v
                  (polym_from_z_btree l)
                  (polym_from_z_btree r))
  end.

Theorem btree_translation:
  forall (t:Z_btree),
  z_btree_from_polym (polym_from_z_btree t) = t.
Proof.
  intros t.
  elim t.
  simpl; reflexivity.
  intros z t2 H1 t3 H2.
  simpl.
  rewrite H1, H2.
  reflexivity.
Qed.

(** Exercise 6.44 **)

(* N(x) = 1 + x *)
(* D(x) = 1 / (1 + 1/x) *)
(* if we use x = p/q *)
(* N(p/q) = 1 + p/q = (p+q)/q *)
(* D(p/q) = 1/(1+1/(p/q)) = 1/(1+q/p)
          = 1/((q+p)/p) = p/(q+p) *)

Fixpoint get_num_denom (r:my_Rat) : (nat*nat) :=
  match r with
  | mrOne => (1, 1)
  | mrN r' =>
      let (p, q) := get_num_denom r' in
        (p + q, q)
  | mrD r' =>
      let (p, q) := get_num_denom r' in
        (p, q + p)
  end.

(** Exercise 6.45 **)

(* Given *)

Inductive cmp : Set :=
  | Less : cmp
  | Equal : cmp
  | Greater : cmp.

(* To do *)

Fixpoint three_way_compare (a b:nat) : cmp :=
  match a, b with
  | 0, 0 => Equal
  | S c, 0 => Greater
  | 0, S d => Less
  | S c, S d => three_way_compare c d
  end.

Compute (three_way_compare 3 3).
Compute (three_way_compare 1 3).
Compute (three_way_compare 5 3).
Compute (three_way_compare 0 3).
Compute (three_way_compare 3 0).
Compute (three_way_compare 0 0).

Fixpoint update_primes (k:nat)
  (pml:list (nat*nat)) :
    ((list (nat*nat))*bool) :=
  match pml with
  | nil => (nil, false)
  | (p, m) :: t =>
    let (nt, found) := update_primes k t in
      match three_way_compare m k with
      | Equal => ((p, m + p) :: nt, true)
      | _ => ((p, m) :: nt, found)
      end
  end.

Compute (update_primes 15
         ((2, 14) :: (3, 15) :: (5, 15) ::
          (7, 14) :: nil)).

Fixpoint prime_sieve (k:nat) : list (nat*nat) :=
  match k with
  | 0 => nil
  | 1 => nil
  | S p =>
      let (upd_prime_list, upd) :=
        update_primes k (prime_sieve p) in
        match upd with
        | true => upd_prime_list
        | false => (k, k + k) :: upd_prime_list
        end
  end.

Compute (prime_sieve 2).
Compute (prime_sieve 3).
Compute (prime_sieve 20).
Compute (prime_sieve 100).
Compute (prime_sieve 97).

Definition prime (k:nat) : Prop :=
  forall d m:nat,
  (2 <= k) /\ (2 <= d < k -> m * d <> k).

Fixpoint prime_in_list 
  (p:nat) (pl:list (nat*nat)) :=
  match pl with
  | nil => False
  | (q, _) :: t =>
      match three_way_compare q p with
      | Equal => True
      | _ => prime_in_list p t
      end
  end.

Compute (prime_in_list 7
         ((2, 14) :: (3, 15) :: (5, 15) ::
          (7, 14) :: nil)).

Compute (prime_in_list 11
         ((2, 14) :: (3, 15) :: (5, 15) ::
          (7, 14) :: nil)).

Lemma nat_le_zero_is_zero:
  forall n:nat, n <= 0 -> n = 0.
Proof.
  intros n H.
  apply le_antisym.
  exact H.
  apply le_0_n.
Qed.

(* TO BE PROVED:

Theorem sieve_works:
  forall k p:nat,
  (prime p) /\ (p <= k) ->
  (prime_in_list p (prime_sieve k)).

*)

(** Exercise 6.46 **)

(* Given *)

Inductive htree (A:Set) : nat->Set :=
  | hleaf : A -> htree A 0
  | hnode : 
     forall n:nat,
     A -> htree A n -> htree A n ->
     htree A (S n).
  
(* To do *)

Lemma some_htree_inj:
  forall (n:nat) (t1 t2 t3 t4:htree nat n),
  hnode nat n 0 t1 t2 = hnode nat n 0 t3 t4 ->
  t1 = t3.
Proof.
  intros n t1 t2 t3 t4 H.
  change (let phi :=
          fun (A:Set)(n:nat)(t:htree A (S n)) =>
          match t with
          | hnode A n t' _ => t'
          | _ => t2
          end in 
          phi nat n (hnode nat n 0 t1 t2) =
          phi nat n (hnode nat n 0 t3 t4)).
  rewrite H.
  reflexivity.
Qed.

(** Exercise 6.47 **)

Fixpoint fixed_height_tree_builder (n:nat) :
  (htree nat n) :=
  match n return htree nat n with
  | S p => hnode nat
                 p
                 (n + p)
                 (fixed_height_tree_builder p)
                 (fixed_height_tree_builder p)
  | 0 => hleaf nat 0
  end.

Compute (fixed_height_tree_builder 3).
Compute (fixed_height_tree_builder 0).
Compute (fixed_height_tree_builder 1).

(** Exercise 6.48 **)

Inductive binary_word : nat -> Set :=
  | bw_x : binary_word 0
  | bw_1 : 
      forall n:nat,
      binary_word n -> binary_word (S n)
  | bw_0 : 
      forall n:nat,
      binary_word n -> binary_word (S n).
Implicit Arguments bw_1 [n].
Implicit Arguments bw_0 [n].

Compute (bw_x).
Compute (bw_1 bw_x).
Compute (bw_1 (bw_0 (bw_1 bw_x))).

Fixpoint binary_word_concat {n m:nat}
  (b1:binary_word n) (b2:binary_word m) :=
  match b1 in binary_word n
  return binary_word (n+m) with
  | bw_x => b2
  | bw_1 _ t => bw_1 (binary_word_concat t b2)
  | bw_0 _ t => bw_0 (binary_word_concat t b2)
  end.

Compute (binary_word_concat
         (bw_1 bw_x)
         (bw_1 (bw_0 (bw_1 bw_x)))).

(** Exercise 6.49 **)

Fixpoint binary_word_or {n:nat}
  (b1:binary_word n) (b2:binary_word n):
  binary_word n := b1.

(* IN PROGRESS *)