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