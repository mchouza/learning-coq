Require Import Arith.
Require Import ZArith.
Require Import Bool.

(** Exercise 2.1 **)

Open Scope nat_scope.

(* The type is going to be nat -> nat
   because of rule App applied with A = nat,
   B = nat -> nat *)
Check (plus 3).

(* The type is going to be Z -> Z for the same 
   reason, replacing nat by Z *)
Check (Zmult(-5)).

(* The type is going to be Z -> nat because the
   function is defined to convert integers to
   natural numbers *)
Check Zabs_nat.

(* The type is going to be nat, because plus has
   type nat -> nat -> nat and it's applied to
   two value *)
Check (5 + Zabs_nat(5 - 19)).

(** Exercise 2.2 **)

(* The type is going to be Z -> Z -> Z -> Z,
   because it's "a function that takes three
   integers and returns one" *)

Check fun a b c:Z => (b*b-4*a*c)%Z.

(** Exercise 2.3 **)

(** It's possible and its type is going to be
    (nat -> nat) -> (nat -> nat) -> nat -> nat
    because it takes two function from naturals}
    to naturals and returns a single one. The
    last parenthesis is not necessary because of
    right associativity *)

Check fun (f g:nat->nat)(n:nat) => g (f n).

(** Exercise 2.4 **)

(* Two applications of Lam give us the type 
   - Lam: whole expression, nat -> ???
     - Lam: whole expression, nat -> nat -> ???
       - Let-in
         App: n - p, nat
         - Let-in
           App: diff*diff, nat
           App: square + n, nat
           App: square * (square + n), nat
           inner let, nat
         outer let, nat
*)
  
Check fun n p: nat =>
  (let diff := n-p in
   let square := diff*diff in
       square * (square + n)).

(** Exercise 2.5 **)

Definition sum5 a b c d e:Z :=
  (a + b + c + d + e)%Z.

(** Exercise 2.6 **)

Section defNewSum5.
  Variables a b c d e:Z.
  Definition newSum5 := (a + b + c + d + e)%Z.
End defNewSum5.

Print newSum5.

(** Exercise 2.7 **)

Definition poly27 :=
  fun x:Z => Zplus (Zplus (Zmult 2%Z
                                 (Zmult x x))
                          (Zmult 3%Z x))
                   3%Z.

Eval compute in (poly27 2).
Eval compute in (poly27 3).
Eval compute in (poly27 4).