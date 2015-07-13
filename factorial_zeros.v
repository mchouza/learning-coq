Require Import Arith.

Fixpoint pow (b e:nat) :=
  match e with
  | 0 => 1
  | S f => b * pow b f
  end.

Fixpoint aux_div n m a :=
  match m, a with
  | _, 0 => None (* NOT REACHED *)
  | 0, _ => None
  | S q, S b =>
      match lt_dec n m with
      | left _ => Some 0
      | right _ => 
          match aux_div (n - m) m b with
          | None => None (* NOT REACHED *)
          | Some k => Some (S k)
          end
      end
  end.

Definition div (n m:nat) := aux_div n m n.

Fixpoint sum_series
  (f:nat->option nat) (a n:nat) :=
  match n with
  | 0 => Some 0
  | S m => 
      match (f a), (sum_series f (S a) m) with
      | Some fa, Some s => Some (fa + s)
      | _, _ => None
      end
  end.

Theorem num_zeros_end_fact:
  forall n m p q:nat,
  fact n = p * (pow 10 m) /\
  ~exists q, fact n = q * (pow 10 (S m)) ->
  sum_series
    (fun i:nat => (div n (pow 5 i))) 1 n =
  Some m.