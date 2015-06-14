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