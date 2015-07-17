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

Definition rem (n m:nat) :=
  match div n m with
  | None => None
  | Some q => Some (n - q * m)
  end.

Lemma nat_strong_ind (P:nat->Prop):
  P 0 ->
  (forall n:nat,
   (forall m:nat, m < n -> P m) -> P n) ->
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
  apply Hrec with (n := n), IHn.
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

Lemma minus_to_plus:
  forall n m p:nat,
  p <= m -> n = m - p -> m = n + p.
Proof.
  intros n m p p_le_m H.
  rewrite H, plus_comm.
  symmetry.
  apply le_plus_minus_r, p_le_m.
Qed.

Lemma n_le_0:
  forall n:nat, n <= 0 -> n = 0.
Proof.
  intros n n_le_0.
  destruct n.
  reflexivity.
  absurd (S n <= 0).  
  apply le_Sn_0.
  assumption.
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
  intros n Hrec.
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
  cut (n - S d' + S d' < S d' * S q' + S d').
  intros n_hi_bound.
  rewrite <-le_plus_minus_r
    with (n := S d') (m := n).
  rewrite plus_comm.
  rewrite <-plus_Sn_m, S_exchange.
  rewrite plus_comm with (n := S d').
  rewrite mult_comm; auto.
  apply not_lt_le; auto.
  apply plus_lt_compat_r; auto.
  apply Hrec.
  assert (n - S d' < n) as sub_is_lt.
  apply lt_minus.
  apply not_lt_le; auto.
  apply lt_O_Sn.
  auto.
  auto.
  apply lt_le_trans with (m := n).
  apply lt_minus.
  apply not_lt_le; auto.
  apply lt_0_Sn.
  apply lt_n_Sm_le; auto.
Qed.

Lemma d_q_step:
  forall q q' d:nat,
  q < q' -> d * S q <= d * q'.
Proof.
  intros q q' d q_lt_q'.
  apply mult_le_compat_l, q_lt_q'.
Qed.

Lemma div_unique:
  forall n d q:nat,
  d * q <= n < d * S q -> div n d = Some q.
Proof.
  intros n d q [Hlo Hhi].
  destruct d as [|d'].
  simpl in Hhi.
  absurd (n < 0).
  apply lt_n_O.
  assumption.
  cut (exists q:nat,
       div n (S d') = Some q /\
       S d' * q <= n < S d' * S q).
  intros [q' [EHq' [Hq'lo Hq'hi]]].
  cut (q' < q \/ q = q' \/ q' > q).
  intros [Hqrel | [Hqrel | Hqrel]].
  absurd (S d' * S q' <= S d' * q).
  apply lt_not_le, le_lt_trans with (m := n);
    assumption.
  apply d_q_step; assumption.
  rewrite EHq', Hqrel; reflexivity.
  absurd (S d' * S q <= S d' * q').
  apply lt_not_le, le_lt_trans with (m := n);
    assumption.
  apply d_q_step; assumption.
  cut (q <= q' \/ q' < q).
  intros [Hqle | Hq'lt].
  right.
  unfold gt.
  rewrite or_comm.
  apply le_lt_or_eq; assumption.
  left; assumption.
  apply le_or_lt.
  apply div_works.
  discriminate.
Qed.

Lemma rem_works:
  forall n d:nat,
  d <> 0 ->
  exists q:nat, div n d = Some q /\
  exists r:nat, rem n d = Some r /\
  n = d * q + r.
Proof.
  intros n d d_ne_0.
  cut (exists q:nat, div n d = Some q /\
       d * q <= n < d * S q).
  intros [q [div_result [div_lo_bound 
                         div_hi_bound]]]. 
  cut (exists r:nat, rem n d = Some r).
  intros [r rem_result].
  exists q.
  split.
  apply div_result.
  exists r.
  split.
  apply rem_result.
  unfold rem in rem_result.
  rewrite div_result in rem_result.
  injection rem_result.
  intros div_rem_rel.
  rewrite plus_comm.
  apply minus_to_plus.
  apply div_lo_bound.
  rewrite <-div_rem_rel, mult_comm.
  reflexivity.
  unfold rem.
  rewrite div_result.
  exists (n - q * d).
  reflexivity.
  apply div_works, d_ne_0.
Qed.

Lemma rem_unique:
  forall n d q r:nat,
  (d * q <= n < d * S q /\ r = n - d * q) ->
  rem n d = Some r.
Proof.
  intros n d q r [Hbounds Hrel].
  unfold rem.
  rewrite div_unique with (q := q).
  rewrite Hrel, mult_comm; reflexivity.
  assumption.  
Qed.

Lemma div_ge:
  forall n m:nat,
  m <> 0 -> m <= n ->
  exists q, div n m = Some q /\ 1 <= q.
Proof.
  intros n m m_ne_0 m_le_n.
  cut (exists q:nat,
       div n m = Some q /\
       m * q <= n < m * S q).
  intros [q [EHq [Hblo Hbhi]]].
  exists q.
  split; [assumption | ..].  
  destruct q as [|q'].
  rewrite mult_1_r in Hbhi.
  absurd (n < m).
  apply le_not_lt; assumption.
  assumption.
  apply le_n_S, le_0_n.
  apply div_works; assumption.
Qed.

(*

Extended GCD adapted from

egcd :: Natural -> Natural -> (Natural,(Natural,Natural))
egcd a 0 = (a,(1,0))
egcd a b =
    if c == 0
    then (b, (1, a `div` b - 1))
    else (g, (u, t + (a `div` b) * u))
  where
    c = a `mod` b
    (g,(s,t)) = egcd c (b `mod` c)
    u = s + (b `div` c) * t

obtained from

https://gilith.wordpress.com/2015/06/24/
natural-number-greatest-common-divisor/

*)

Fixpoint egcd_aux (a b x:nat) :=
  match a, b, x with
  | S _, 0, _ => Some (a, 1, 0)
  | S _, S _, S y =>
    match rem a b, div a b with
    | Some c, Some a_div_b =>
      match c with
      | 0 => Some (b, 1, a_div_b - 1)
      | _ =>
        match rem b c with
        | Some rem_b_c =>
          match egcd_aux c rem_b_c y with
          | Some (g, s, t) =>
            match div b c with
            | Some b_div_c =>
              let u := s + b_div_c * t in
              Some (g, u, t + a_div_b * u)
            | _ => None
            end
          | None => None
          end
        | None => None
        end
      end
      | _, _ => None
    end
  | _, _, _ => None
  end.

Definition egcd (n m:nat) :=
  egcd_aux n m (S(m + n)).

Lemma egcd_works:
  forall n m:nat,
  m <= n -> m <> 0 ->
  exists g, exists s, exists t,
  Some (g, s, t) = egcd n m /\
  rem n g = Some 0 /\
  rem m g = Some 0 /\
  s * n = t * m + g.
Proof.
  (* let's start by generalizing the auxiliary
     parameter *)
  cut (forall n m x:nat,
       m <= n -> m <> 0 -> n + m < x ->
       exists g, exists s, exists t,
       Some (g, s, t) = egcd_aux n m x /\
       rem n g = Some 0 /\
       rem m g = Some 0 /\
       s * n = t * m + g).
  intros Hgen n m m_le_n m_ne_0.
  unfold egcd.
  apply Hgen; auto.
  rewrite plus_comm.
  apply lt_n_Sn.

  (* starts the strong induction *)
  intros n.
  elim n using nat_strong_ind.
  
  (* eliminates the n = 0 case *)
  intros m x m_le_0 m_ne_0 _.
  absurd (m = 0).
  assumption.
  apply n_le_0; assumption.

  (* starts introducing the strong induction
     hypothesis *)
  clear n.
  intros n Hrec.
  intros m x m_le_n m_ne_0 n_p_m_lt_x.

  (* unfolding the definitions gives us a
     cluttered result *)
  (* let's isolate the right branch *)
  destruct n as [|n'].
  absurd (m = 0).
  assumption.
  apply n_le_0; assumption.
  simpl.
  destruct m as [|m'].
  absurd (0 = 0).
  assumption.
  reflexivity.
  simpl.
  destruct x as [|x'].
  absurd (S n' + S m' < 0).
  apply lt_n_O.
  assumption.
  simpl.
  cut (exists c, rem (S n') (S m') = Some c).
  intros [c EHc].
  rewrite EHc.
  cut (exists a_div_b,
       div (S n') (S m') = Some a_div_b).
  intros [a_div_b EHa_div_b].
  rewrite EHa_div_b.
  
  (* now we have two different cases, depending
     if c is 0 *)

  (* the c = 0 case is quite simple *)
  destruct c as [|c'].
  exists (S m'), 1, (a_div_b - 1).
  rewrite rem_unique
    with (q := a_div_b) (r := 0).
  rewrite rem_unique
    with (q := 1) (r := 0).
  split.
  reflexivity.
  split.
  reflexivity.
  split.
  reflexivity.
  rewrite mult_minus_distr_r.
  repeat rewrite mult_1_l.
  rewrite plus_comm, le_plus_minus_r.
  cut (exists q:nat,
       div (S n') (S m') = Some q /\
       exists r:nat,
       rem (S n') (S m') = Some r /\
       (S n') = (S m') * q + r).
  intros [q [EHq [r [EHr Hqr]]]].
  rewrite EHc in EHr.
  injection EHr.
  intros r_eq_0.
  rewrite <-r_eq_0 in Hqr.
  rewrite EHq in EHa_div_b.
  injection EHa_div_b.
  intros q_eq_a_div_b.
  rewrite plus_0_r, q_eq_a_div_b,
          mult_comm in Hqr.
  assumption.
  apply rem_works.
  assumption.
  rewrite <-mult_1_l at 1.
  apply mult_le_compat_r.
  cut (exists q,
       div (S n') (S m') = Some q /\
       1 <= q).
  intros [q [q_is_quot quot_ge_1]].
  rewrite EHa_div_b in q_is_quot. 
  injection q_is_quot.
  intros q_is_a_div_b.
  rewrite q_is_a_div_b; assumption.
  apply div_ge.
  assumption.
  assumption.
  split.
  split.
  rewrite mult_1_r; apply le_n.
  rewrite mult_comm.
  unfold mult.
  rewrite plus_0_r, <-plus_0_l at 1.
  apply plus_lt_compat_r, lt_0_Sn.
  rewrite mult_1_r, <-minus_n_n; reflexivity.
  (* FIXME: ADMIT *)
  admit.

  (* we start the other case by asssuming the
     existence of some terms *)
  cut (exists rem_b_c,
       rem (S m') (S c') = Some rem_b_c).
  intros [rem_b_c EHrem_b_c].
  rewrite EHrem_b_c.
  cut (exists b_div_c,
       div (S m') (S c') = Some b_div_c).
  intros [b_div_c EHb_div_c].
  rewrite EHb_div_c.

  (* FIXME: INCLUDE THE PROOF IN THE UNFOLDING *)
  admit.
  admit.
  admit.
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