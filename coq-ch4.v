Require Import Arith.

Parameters (prime_divisor : nat->nat)
           (prime : nat->Prop)
           (divides : nat->nat->Prop).

Check (prime (prime_divisor 220)).

(** Exercise 4.1 **)

(* Assuming known that nat : Set and 
   Prop : Type,
   Prod with A := nat and B := nat gives us
   nat->nat : Set
   Prod-dep with A := nat->nat and B := Prop
   gives us (nat->nat)->Prop : Type *)
Check ((nat->nat)->Prop).

(* We know that nat->nat : Set and
   (nat->nat)->Prop : Type.
   Applying Prod-dep with A := nat->nat and
   B := (nat->nat)->Prop gives us
   (nat->nat)->(nat->nat)->Prop : Type *)
Check ((nat->nat)->(nat->nat)->Prop).

(* As we know that Set : Type and nat : Set,
   applying Prod-dep with A := nat and B := Set
   we get nat->Set : Type
   Applying Prod-dep with the same A and
   B := nat->Set we get
   nat->nat->Set : Type *)
Check (nat->nat->Set).

(** Exercise 4.2 **)

(** POSTPONED **)

(** Exercise 4.3 **)

Section A_declared.
  Variable (A:Set)(P Q:A->Prop)(R:A->A->Prop).

  Theorem all_perm :
    (forall a b:A, R a b)->
    (forall a b:A, R b a).
  Proof (fun (H : (forall a b:A, R a b))
             (a b : A) =>
         H b a). 

  Theorem all_imp_digits :
    (forall a:A, P a -> Q a) ->
    (forall a:A, P a) ->
    (forall a:A, Q a).
  Proof fun (H1 : (forall a:A, P a -> Q a))
            (H2 : (forall a:A, P a))
            (a : A) =>
        H1 a (H2 a).

  Theorem all_delta :
    (forall a b:A, R a b)->
    forall a:A, R a a.
  Proof fun (H : forall a b:A, R a b)
            (a:A) =>
        H a a.
End A_declared.

(** Exercise 4.4 **)

Check (forall A:Set, A->A).

Definition id (A:Set)(a:A) := a.

Check id.

Check (forall A B:Set, (A->A->B)->A->B).

Definition diag (A B:Set) (op:A->A->B) :=
  fun (a:A) => op a a.

Check diag.

Check (forall A B C:Set,
       (A->B->C)->B->A->C).

Definition permute (A B C:Set) (f:A->B->C)
                   (b:B) (a:A) :=
  f a b.

Check permute.

Require Import ZArith.

Check (forall A:Set, (nat->A)->Z->A).

Definition f_nat_Z (A:Set) (nf:nat->A)
                   (a:Z) :=
  nf (Zabs_nat a).

Check f_nat_Z.

(** Exercise 4.5 **)

Theorem all_perm_new :
  forall (A:Type)(P:A->A->Prop),
  (forall x y:A, P x y)->
  (forall x y:A, P y x).
Proof.
  intros A P H x y.
  apply H.
Qed.

Theorem resolution:
  forall (A:Type)(P Q R S:A->Prop),
  (forall a:A, Q a -> R a -> S a) ->
  (forall b:A, P b -> Q b) ->
  (forall c:A, P c -> R c -> S c).
Proof.
  intros A P Q R S H1 H2 c H3 H4.
  apply H1; [apply H2 | idtac];
    assumption.
Qed.