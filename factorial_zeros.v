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

Definition div (n m:nat) := aux_div n m (S n).

Lemma nat_strong_ind (P:nat->Prop):
  P 0 ->
  (forall n m:nat, (m < n -> P m) -> P n) ->
  (forall n:nat, P n).
Proof.
  intros P0 Hrec n.
  cut (forall n m:nat, m < n -> P m).
  intros Hcut.
  apply Hcut with (n := S n).
  auto.
  clear n.
  induction n.
  intros m m_imp.
  apply False_ind, lt_n_O with (n := m), m_imp.
  intros m mainH.
  cut (m < n \/ m = n).
  intros [baseH | stepH].
  apply IHn, baseH.
  rewrite stepH.
  apply Hrec with (m := m), IHn.
  apply le_lt_or_eq.
  apply le_S_n, mainH.
Qed.

Lemma S_exchange:
  forall a b:nat,
  S a + b * S a = S b + a * S b.
Proof.
  intros a b.
  rewrite mult_comm with (n := b),
          mult_comm with (n := a).
  simpl.
  repeat rewrite plus_assoc.
  rewrite mult_comm, plus_comm with (n := a).
  reflexivity.
Qed.

Lemma not_lt_le:
  forall n m:nat, ~ n < m -> m <= n.
Proof.
  intros n m H.
  cut (m <= n \/ n < m).
  tauto.
  apply le_or_lt.
Qed.

Lemma div_works:
  forall n d:nat,
  d <> 0 ->
  exists q:nat, div n d = Some q /\
  d * q <= n < d * S q.
Proof.
  unfold div.
  cut (forall n d k:nat,
       d <> 0 -> n < k ->
       exists q:nat,
       aux_div n d k = Some q /\
       d * q <= n < d * S q).
  intros Hcut n d d_ne_0.
  apply Hcut with (k := S n); auto.
  intros n.
  elim n using nat_strong_ind.
  intros d k d_ne_0 k_gt_0.
  destruct d as [|d'], k as [|k'].
  apply False_ind; auto.
  apply False_ind; auto.
  apply False_ind, lt_irrefl with (n := 0); auto.
  exists 0; simpl.
  rewrite mult_0_r; split; split;
    [auto | apply lt_0_Sn].
  clear n.
  intros n m Hrec.
  intros d k d_ne_0 k_gt_n.
  destruct d as [|d'], k as [|k'].
  apply False_ind; auto.
  apply False_ind; auto.
  apply False_ind, lt_n_O with (n := n); auto.
  simpl.
  destruct lt_dec with (n := n) (m := (S d'))
           as [n_lt_d | n_ge_d].
  exists 0.
  rewrite mult_0_r, plus_0_l, plus_0_l,
          mult_1_r.
  split; split; auto.
  apply le_0_n.
  cut (exists q':nat,
       aux_div (n - S d') (S d') k' = Some q' /\
       S d' * q' <= n - S d' < S d' * S q').
  intros [q' [HrecI1 [HrecI2 HrecI3]]].
  exists (S q').
  rewrite HrecI1.
  split; auto.
  split.
  cut (S d' * q' + S d' <= n).
  intros n_lo_bound.
  rewrite S_exchange, mult_comm, plus_comm; auto.
  rewrite le_plus_minus 
    with (n := S d') (m := n).
  rewrite plus_comm with (n := S d').
  apply plus_le_compat_r; auto.
  apply not_lt_le; auto.
  (* FIXME: PROVE *)
  admit.
  admit.
Qed.

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