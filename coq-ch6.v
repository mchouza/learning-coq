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

