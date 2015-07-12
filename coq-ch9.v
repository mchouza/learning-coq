(** Exercise 9.1 **)

Fixpoint extract
  (A:Set) (P:A->Prop) (p:sig P): A :=
  match p with
  | exist x q => x
  end.

Inductive even: nat -> Prop :=
  | even_0: even 0
  | even_SSn:
      forall n:nat, even n -> even (S (S n)).

Lemma even2: even 2.
Proof.
  apply even_SSn, even_0.
Qed.

Definition my_sig_even := exist even 2 even2.

Check my_sig_even.

Compute extract nat even my_sig_even.

Lemma ex_9_1:
  forall (A:Set) (P:A->Prop) (y:{x:A|P x}),
  P (extract A (fun x:A => P x) y).
Proof.
  induction y; simpl; auto.
Qed.

(** Exercise 9.2 **)

(* Given *)

Require Import ZArith.

Open Scope Z_scope.

Variable div_pair: 
  forall a b:Z, 0 < b ->
  { p:Z*Z | a = (fst p)*b + snd p /\
            0 <= snd p < b }.

Definition div_pair' 
  (a:Z)(x:{ b:Z | 0 < b }): Z*Z :=
  match x with
  | exist b h => 
      let (v, _) := div_pair a b h in v
  end.

(* To do *)

Definition gt0 (a:Z) := (0 < a).

Definition div_pair''
  (a:Z)(x:{ b:Z | 0 < b }) :=
  match x with
  | exist _ h =>
      div_pair a (extract Z gt0 x)
  end.  

Check div_pair''.

(** Exercise 9.3 *)

Definition sig_rec_simple
  (A:Set) (P:A->Prop) (B:Set)
  (h:forall x:A, P x -> B) (p:sig P) :=
  match p with
  | exist a q => h a q
  end.

Check sig_rec_simple.

Close Scope Z_scope.

(** Exercise 9.4 **)

Definition S_O :=
  fun (n:nat) (H:S n = 0) =>
  O_S n (eq_sym H).

SearchAbout S.

Definition conv_S_eq_dec (x y:nat)
(ed:{x=y}+{x<>y}): {S x=S y}+{S x<>S y} :=
  match ed with
  | left eqxy =>
      left _ (eq_S x y eqxy)
  | right ineqxy =>
      right _ (not_eq_S x y ineqxy)
  end.

Fixpoint eq_dec_nat (x y:nat): {x=y}+{x<>y} :=
  match x, y return {x=y}+{x<>y} with
  | 0, 0 => left _ (eq_refl 0)
  | S u, 0 => right _ (S_O u)
  | 0, S v => right _ (O_S v)
  | S u, S v =>
      conv_S_eq_dec u v (eq_dec_nat u v)
  end.

(** Exercise 9.5 **)

Require Import List.

Fixpoint count_occurrences
  (l:list nat) (n:nat): nat :=
  match l with
  | nil => 0
  | m :: l' =>
      match eq_dec_nat n m with
      | left _ => S (count_occurrences l' n)
      | right _ => count_occurrences l' n
      end
  end.

Compute count_occurrences (1::2::3::2::nil) 1.
Compute count_occurrences (1::2::3::2::nil) 2.
Compute count_occurrences (1::2::3::2::nil) 3.
Compute count_occurrences (1::2::3::2::nil) 5.

(** Exercise 9.6 **)

Fixpoint div3 (n:nat) :=
  match n with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | S (S (S p)) => S (div3 p)
  end.

Compute div3 0.
Compute div3 2.
Compute div3 100.
Compute div3 101.
Compute div3 102.

Lemma div3_le: forall n:nat, div3 n <= n.
Proof.
  intros n.
  cut (div3 n <= n /\ div3 (S n) <= S n /\
       div3 (S (S n)) <= S (S n)).
  tauto.
  induction n.
  simpl; auto.
  destruct IHn as [H1 [H2 H3]].
  split; [auto | split; auto].
  simpl; auto with arith.
Qed.

(** Exercise 9.7 **)

(* Given *)

Fixpoint div2 (n:nat) : nat :=
  match n with
  | 0 => 0
  | 1 => 0
  | S (S p) => S (div2 p)
  end.

(* To do *)

Fixpoint mod2 (n:nat) :=
  match n with
  | 0 => 0
  | 1 => 1
  | S (S m) => mod2 m
  end.

Theorem ex_9_7:
  forall n:nat, n = 2 * (div2 n) + (mod2 n).
Proof.
  intros n.
  cut (n = 2 * (div2 n) + (mod2 n) /\
       S n = 2 * (div2 (S n)) + (mod2 (S n))).
  tauto.
  induction n.
  simpl; tauto.
  destruct IHn as [IHn1 IHn2].
  split; auto.
  simpl; apply f_equal.
  simpl in IHn1.
  rewrite <-plus_n_Sm; simpl; auto.
Qed.

(** Exercise 9.8 **)

Fixpoint fib (n:nat) :=
  match n with
  | 0 => 1
  | 1 => 1
  | S p => (fib p) + match p with
                     | 0 => 1
                     | S q => fib q
                     end
  end.

Compute (fib 5).
Compute (fib 10).

Fixpoint fib' (n:nat) :=
  match n with
  | 0 => (1, 1)
  | S p => let (fp, f) := fib' p in
           (f, fp + f)
  end.

Compute (fib' 5).
Compute (fib' 10).

Lemma fib_prop:
  forall n:nat,
  fib n + fib (S n) = fib (S (S n)).
Proof.
  intros n.
  simpl; apply plus_comm.
Qed.

Lemma fib'_prop1:
  forall n:nat,
  fst (fib' (S n)) = snd (fib' n).
Proof.
  intros n.
  simpl.
  elim (fib' n).
  auto.
Qed.

Lemma fib'_prop2:
  forall n:nat,
  snd (fib' (S n)) =
  fst (fib' n) + snd (fib' n).
Proof.
  intros n.
  simpl.
  elim (fib' n).
  simpl; auto.
Qed.

Lemma fib'_prop3:
  forall n:nat,
  fst (fib' (S (S n))) =
  fst (fib' (S n)) + fst (fib' n).
Proof.
  intros n.
  rewrite fib'_prop1, fib'_prop2, fib'_prop1.
  apply plus_comm.
Qed.

Lemma fib'_prop4:
  forall n:nat,
  snd (fib' (S (S n))) =
  snd (fib' (S n)) + snd (fib' n).
Proof.
  intros n.
  repeat rewrite <-fib'_prop1.
  apply fib'_prop3.
Qed.

Lemma fib_fib'_fst_eq:
  forall n:nat, fst (fib' n) = fib n.
Proof.
  intros n.
  cut (fst (fib' n) = fib n /\
       fst (fib' (S n)) = fib (S n)).
  tauto.
  induction n.
  simpl; auto.
  destruct IHn as [IHn1 IHn2].
  split; auto.
  rewrite <-fib_prop.
  rewrite fib'_prop3.
  rewrite IHn1, IHn2.
  apply plus_comm.
Qed.

Lemma fib_fib'_snd_eq:
  forall n:nat, snd (fib' n) = fib (S n).
Proof.
  intros n.
  rewrite <-fib'_prop1, fib_fib'_fst_eq.
  auto.
Qed.

Theorem ex_9_8:
  forall n:nat,
  (fib n, fib (S n)) = fib' n.
Proof.
  intros n.
  rewrite <-fib_fib'_fst_eq, <-fib_fib'_snd_eq.
  elim (fib' n).
  auto.
Qed.

(** Exercise 9.9 **)

Theorem nat_3_ind:
  forall P:nat->Prop,
  P 0 -> P 1 -> P 2 ->
  (forall n:nat, P n -> P (S (S (S n)))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 P2 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n))).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 [IHn2 IHn3]].
  auto.
Qed.

Theorem nat_4_ind:
  forall P:nat->Prop,
  P 0 -> P 1 -> P 2 -> P 3 ->
  (forall n:nat, P n -> P (S (S (S (S n))))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 P2 P3 Hrec n.
  cut (P n /\ P (S n) /\ P (S (S n)) /\
       P (S (S (S n)))).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 [IHn2 [IHn3 IHn4]]].
  auto.
Qed.

(** Exercise 9.10 **)

Theorem fib_ind:
  forall P:nat->Prop, P 0 -> P 1 ->
  (forall n:nat,
   P n -> P (S n) -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 IHn2].
  auto.
Qed.

Compute fib (3 + 2 + 2).
Compute (fib (3 + 1)) * (fib (2 + 1)) +
        (fib 3) * (fib 2).

Lemma fib_prod:
  forall (n p:nat),
  fib (S(S(n + p))) =
  (fib (S n)) * (fib (S p)) +
  (fib n) * (fib p).
Proof.
  intros n.
  elim n using fib_ind.
  simpl; auto.
  intros p.
  simpl; repeat rewrite <-plus_n_O.
  rewrite plus_comm, plus_assoc; auto.
  clear n.
  intros n IHn1 IHn2 p.
  specialize IHn1 with (p := p).
  specialize IHn2 with (p := p).
  rewrite <-fib_prop.
  repeat rewrite plus_Sn_m in *.
  rewrite IHn1, IHn2.
  repeat rewrite <-fib_prop.
  repeat rewrite mult_plus_distr_r.
  repeat rewrite <-plus_assoc.
  apply f_equal.
  rewrite plus_comm, <-plus_assoc, <-plus_assoc.
  do 2 apply f_equal.
  rewrite plus_comm; auto.
Qed.

(** Exercise 9.11 **)

Lemma div3_le': forall n:nat, div3 n <= n.
Proof.
  intros n.
  elim n using nat_3_ind; simpl; auto.
  intros n' Hrec.
  do 2 apply le_S; apply le_n_S; exact Hrec.
Qed.

Theorem nat_2_ind:
  forall P:nat->Prop,
  P 0 -> P 1 ->
  (forall n:nat, P n -> P (S (S n))) ->
  forall n:nat, P n.
Proof.
  intros P P0 P1 Hrec n.
  cut (P n /\ P (S n)).
  tauto.
  induction n.
  auto.
  destruct IHn as [IHn1 IHn2].
  auto.
Qed.

Theorem ex_9_7':
  forall n:nat, n = 2 * (div2 n) + (mod2 n).
Proof.
  intros n.
  elim n using nat_2_ind; simpl; auto.
  intros n' Hrec.
  rewrite <-plus_n_Sm, plus_Sn_m.
  do 2 apply f_equal; exact Hrec.
Qed.

(* ex 9.8 skipped because it's too long *)

(** Exercise 9.12 **)

Definition mult2 (n:nat) := n + n.

Definition d2m2_0:
  {q:nat & {r:nat | 0 = (mult2 q) + r /\
                    r <= 1}}.
  exists 0, 0.
  simpl; auto.
Defined.

Definition d2m2_1:
  {q:nat & {r:nat | 1 = (mult2 q) + r /\
                    r <= 1}}.
  exists 0, 1.
  simpl; auto.
Defined.

Lemma d2m2_rec:
  forall n:nat,
  {q:nat & {r:nat | n = (mult2 q) + r /\
                    r <= 1}} ->
  {q:nat & {r:nat | S (S n) = (mult2 q) + r /\
                    r <= 1}}.
Proof.
  intros n [q [r [H1 H2]]].
  exists (S q), r.
  split; auto.
  simpl.
  rewrite <-plus_n_Sm, plus_Sn_m.
  do 2 apply f_equal.
  apply H1.
Defined.

Fixpoint div2_mod2 (n:nat):
  {q:nat & {r:nat | n = (mult2 q) + r /\
                    r <= 1}} :=
  match n return
  {q:nat & {r:nat | n = (mult2 q) + r /\
                    r <= 1}}
  with
  | 0 => d2m2_0
  | 1 => d2m2_1
  | S (S n) => d2m2_rec n (div2_mod2 n)
  end.

Compute div2_mod2 3.

(** Exercise 9.13 **)

(* Given *)

Fixpoint plus' (n m:nat){struct m} : nat :=
  match m with
  | 0 => n
  | S p => S (plus' n p)
  end.

(* To do *)

Lemma plus'_assoc:
  forall n m p:nat,
  (plus' n (plus' m p)) = (plus' (plus' n m) p).
Proof.
  intros n m p.
  induction p.
  simpl; auto.
  simpl.
  apply f_equal, IHp.
Qed.

(** Exercise 9.14 **)

(* Given *)

Fixpoint plus'' (n m:nat){struct m} : nat :=
  match m with
  | 0 => n
  | S p => plus'' (S n) p
  end.

(* To do *)

Lemma plus''_Sn_m:
  forall n m:nat,
  plus'' (S n) m = S(plus'' n m).
Proof.
  intros n m.
  generalize n.
  induction m.
  simpl; auto.
  intros n'.
  simpl.
  rewrite IHm.
  auto.
Qed.

Lemma plus''_assoc:
  forall n m p:nat,
  (plus'' n (plus'' m p)) =
  (plus'' (plus'' n m) p).
Proof.
  intros n m p.
  generalize n m.
  induction p.
  simpl; auto.
  intros n' m'.
  simpl.
  rewrite plus''_Sn_m; simpl.
  repeat rewrite plus''_Sn_m.
  rewrite IHp; auto.
Qed.

(** Exercise 9.15 **)

Fixpoint _trf_aux (f1 f2 c:nat) :=
  match c with
  | 0 => f1
  | S d => _trf_aux f2 (f1 + f2) d
  end.

Definition tail_rec_fib (n:nat) :=
  _trf_aux 1 1 n.

Compute tail_rec_fib 10.

Lemma trf_linear:
  forall n a b c d:nat,
  _trf_aux (a+b) (c+d) n =
  _trf_aux a c n + _trf_aux b d n.
Proof.
  induction n.
  simpl; auto.
  intros a b c d.
  simpl.
  rewrite <-IHn.
  repeat rewrite plus_assoc.
  rewrite plus_comm with (n := a + b) (m := c).
  rewrite plus_assoc.
  rewrite plus_comm with (n := c) (m := a).
  auto.
Qed.

Lemma trf_step:
  forall n a b:nat,
  _trf_aux a b (S n) = _trf_aux b (a + b) n.
Proof.
  auto.
Qed.

Lemma trf_equiv:
  forall n:nat, tail_rec_fib n = fib n.
Proof.
  intros n.
  elim n using fib_ind.
  auto.
  auto.
  clear n.
  intros n Hrec1 Hrec2.
  unfold tail_rec_fib in *.
  do 2 rewrite trf_step.
  rewrite <-fib_prop.
  rewrite trf_step in Hrec2.
  rewrite <-Hrec1, <-Hrec2.
  rewrite trf_linear.
  auto.
Qed.

(** Exercise 9.16 **)

Require Import ZArith.

Open Scope Z_scope.

Definition sqrt_ind_step p s' :=
  match Zpos p ?=
        (2 * s' + 1) * (2 * s' + 1) with
  | Gt => 2 * s' + 1
  | Eq => 2 * s' + 1
  | Lt => 2 * s'
  end.

Fixpoint sqrt (p:positive) :=
  match p with
  | xH => 1
  | xO xH => 1
  | xI xH => 1
  | xO (xO p') => sqrt_ind_step p (sqrt p')
  | xI (xO p') => sqrt_ind_step p (sqrt p')
  | xO (xI p') => sqrt_ind_step p (sqrt p')
  | xI (xI p') => sqrt_ind_step p (sqrt p')
  end.

Lemma z_lt_le:
  forall a b:Z,
  a < b + 1 <-> a <= b.
Proof.
  intros a b.
  split.
  intros H.
  apply Zlt_succ_r, H.
  intros H.
  apply Zle_lt_succ, H.
Qed.

Lemma z_lt_le_minus_one:
  forall a b:Z,
  a < b <-> a <= b + (-1).
Proof.
  intros a b.
  split.
  intros H.
  rewrite Zplus_0_r_reverse,
          <-Zplus_opp_l with (n := 1),
          Zplus_assoc, z_lt_le in H.
  exact H.
  intros H.
  rewrite Zplus_0_r_reverse,
          <-Zplus_opp_l with (n := 1),
          Zplus_assoc, z_lt_le.
  exact H.
Qed.

Lemma sqrt_lt:
  forall a a' s':Z,
  1 <= a' ->
  4 * a' <= a < 4 * (a' + 1) ->
  s' * s' <= a' < (s' + 1) * (s' + 1) ->
  4 * s' * s' <= a < 4 * (s' + 1) * (s' + 1).
Proof.
  intros a a' s' H1 [H2 H3] [H4 H5].
  split.
  apply Zle_trans with (m := 4 * a').
  rewrite <-Zmult_assoc.
  apply Zmult_le_compat_l; auto.
  discriminate.
  auto.
  rewrite z_lt_le_minus_one in H5, H3.
  rewrite z_lt_le_minus_one.
  apply Zle_trans 
    with (m := 4 * (a' + 1) + -1).
  auto.
  apply Zplus_le_compat_r.
  rewrite <-Zmult_assoc.
  apply Zmult_le_compat_l.
  apply Zplus_le_reg_r with (p := -1).
  rewrite <-Zplus_assoc, Zplus_opp_r, Zplus_0_r.
  auto.
  discriminate.
Qed.

Lemma one_le_pos:
  forall p:positive, 1 <= Zpos p.
Proof.
  intros p.
  apply Zge_le.
  apply Pcompare_1.
Qed.  

Lemma sis_step:
  forall (p p':positive) (s':Z),
  4 * (Zpos p') <= Zpos p < 4 * (Zpos p' + 1) ->
  s' * s' <= Zpos p' < (s' + 1) * (s' + 1) ->
  let s := sqrt_ind_step p s' in
  s * s <= Zpos p < (s + 1) * (s + 1).
Proof.
  intros p p' s' H1 H2 s.
  cut ((2 * s' + 1) * (2 * s' + 1) <= Zpos p  \/
       Zpos p < (2 * s' + 1) * (2 * s' + 1)).
  intros [H3|H3].
  cut (s = 2 * s' + 1).
  intros H4.
  rewrite H4.
  split; auto.
  cut ((2 * s' + 1 + 1) * (2 * s' + 1 + 1) =
       4 * (s' + 1) * (s' + 1)).
  intros H5.
  rewrite H5.
  cut (4 * s' * s' <= 
       Zpos p <
       4 * (s' + 1) * (s' + 1)).
  tauto.
  apply sqrt_lt with (a' := Zpos p').
  apply one_le_pos.
  auto.
  auto.
  cut (1 + 1 = 2).
  intros H5.
  rewrite <-Zplus_assoc, H5.
  rewrite <-Zmult_1_r with (n := 2).
  rewrite <-Zmult_assoc.
  rewrite <-Zmult_plus_distr_r.
  rewrite Zmult_1_l.
  rewrite Zmult_assoc.
  rewrite Zmult_comm with (n := 2 * (s' + 1)).
  cut (2 * 2 = 4).
  intros H6.
  rewrite Zmult_assoc, H6.
  auto.
  simpl; auto.
  simpl; auto.
  unfold s, sqrt_ind_step.
  assert (Zpos p >=
          (2 * s' + 1) * (2 * s' + 1)) as H4.
  apply Zle_ge; auto.
  unfold Zge in H4.
  destruct (Zpos p ?=
            (2 * s' + 1) * (2 * s' + 1)).
  auto.
  apply False_ind, H4; auto.
  auto.
  cut (s = 2 * s').
  intros H4.
  rewrite H4.
  cut (4 * s' * s' <= 
       Zpos p <
       4 * (s' + 1) * (s' + 1)).
  intros [H5 H6].
  split.
  rewrite Zmult_assoc.
  rewrite Zmult_comm with (n := 2 * s').
  rewrite Zmult_assoc.
  cut (2 * 2 = 4).
  intros H7.
  rewrite H7; auto.
  simpl; auto.
  auto.
  apply sqrt_lt with (a' := Zpos p').
  apply one_le_pos.
  auto.
  auto.
  unfold s, sqrt_ind_step.
  unfold Zlt in H3.
  destruct (Zpos p ?=
            (2 * s' + 1) * (2 * s' + 1)).
  discriminate.
  auto.
  discriminate.
  apply Zle_or_lt.
Qed.

Open Scope positive_scope.

Lemma pos_double_induction:
  forall (P:positive->Prop),
  P 1 -> P 2 -> P 3 ->
  (forall q:positive, P q -> 
   P (q~0~0) /\ P q~0~1 /\ P q~1~0 /\ P q~1~1) ->
  forall p:positive, P p.
Proof.
  intros P P1 P2 P3 Hrec p.
  cut (P p /\ P p~0 /\ P p~1).
  tauto.
  induction p.
  split.
  apply IHp.
  apply Hrec.
  apply IHp.
  split.
  apply IHp.
  cut (P p -> P p~0~0 /\ P p~0~1).
  tauto.
  intros Pp.
  split; apply Hrec; auto.
  auto.
Qed.

Lemma two_bits_bounds:
  forall p:positive,
  p~0~0 = 4 * p /\
  p~0~1 = 4 * p + 1 /\
  p~1~0 = 4 * p + 2 /\
  p~1~1 = 4 * p + 3.
Proof.
  intros p.
  elim p using pos_double_induction; simpl; auto.
  intros q.
  split; simpl; auto.
  split; simpl; auto.
Qed.

Close Scope positive_scope.

Lemma multiply_out_pos:
  forall p q:positive,
  Zpos (p * q) = Zpos p * Zpos q.
Proof.
  intros p q.
  simpl; auto.
Qed.

Lemma ms_out_pos:
  forall p q r:positive,
  Zpos (p * q + r) = Zpos p * Zpos q + Zpos r.
Proof.
  intros p q r.
  simpl; auto.
Qed.

Lemma sqrt_works:
  forall p:positive,
  sqrt p * sqrt p <= Zpos p <
  (sqrt p + 1) * (sqrt p + 1).
Proof.
  intros p.
  elim p using pos_double_induction.
  simpl; omega.
  simpl; omega.
  simpl; omega.
  intros q Hrec.
  cut (q~0~0 = 4 * q /\
       q~0~1 = 4 * q + 1 /\
       q~1~0 = 4 * q + 2 /\
       q~1~1 = 4 * q + 3)%positive.
  intros [Q00 [Q01 [Q10 Q11]]].
  split; simpl.
  apply sis_step with (p' := q).
  rewrite Q00, multiply_out_pos.
  omega.
  auto.
  split; simpl.
  apply sis_step with (p' := q).
  rewrite Q01, ms_out_pos.
  omega.
  auto.
  split; simpl.
  apply sis_step with (p' := q).
  rewrite Q10, ms_out_pos.
  omega.
  auto.
  simpl.
  apply sis_step with (p' := q).
  rewrite Q11, ms_out_pos.
  omega.
  auto.
  apply two_bits_bounds.
Qed.
