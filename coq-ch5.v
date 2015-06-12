(** Exercise 5.1 **)

Lemma id_P : forall P:Prop, P->P.
Proof.
  intros P H; assumption.
Qed.

Lemma id_PP : forall P:Prop, (P->P)->(P->P).
Proof.
  intros P H; assumption.
Qed.

Lemma imp_trans :
  forall P Q R:Prop, (P->Q)->(Q->R)->P->R.
Proof.
  intros P Q R PQH QRH PH.
  apply QRH, PQH.
  assumption.
Qed.

Lemma imp_perm :
  forall P Q R:Prop, (P->Q->R)->(Q->P->R).
Proof.
  intros P Q R PQRH QH PH.
  apply PQRH; assumption.
Qed.

Lemma ignore_Q :
  forall P Q R:Prop, (P->R)->P->Q->R.
Proof.
  intros P Q R PRH PH QH.
  apply PRH.
  assumption.
Qed.

Lemma delta_imp :
  forall P Q:Prop, (P->P->Q)->P->Q.
Proof.
  intros P Q PPQH PH.
  apply PPQH; assumption.
Qed.

Lemma delta_impR : 
  forall P Q:Prop, (P->Q)->(P->P->Q).
Proof.
  intros P Q PQH PH PH2.
  apply PQH.
  assumption.
Qed.

Lemma diamond :
  forall P Q R T:Prop,
  (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof.
  intros P Q R T PQH PRH QRTH PH.
  apply QRTH.
  apply PQH.
  assumption.
  apply PRH.
  assumption.
Qed.

Lemma weak_peirce :
forall P Q:Prop, ((((P->Q)->P)->P)->Q)->Q.
Proof.
  intros P Q H1.
  apply H1.
  intros H2.
  apply H2.
  intros PH.
  apply H1.
  intros H3.
  assumption.
Qed.

(** Exercise 5.2 **)

(** ALREADY DONE THAT WAY... **)

(** Exercise 5.3 **)

Lemma Ex_5_3_1: ~False.
Proof.
  intro H.
  exact H.
Qed.
(* Essentially P->P *)

Lemma Ex_5_3_2: forall P:Prop, ~~~P->~P.
Proof.
  unfold not.
  intros P H1 p.
  apply H1.
  intro H2.
  apply H2.
  assumption.
Qed.
(* Essentially (((P->Q)->Q)->Q)->P->Q *)

Lemma Ex_5_3_3:
  forall P Q:Prop, ~~~P->P->Q.
Proof.
  intros P Q H p.
  assert (~P).
  apply Ex_5_3_2; assumption.
  elim H0; assumption.
Qed.

Lemma Ex_5_3_4:
  forall P Q:Prop, (P->Q)->~Q->~P.
Proof.
  unfold not.
  intros p q H1 H2 H3.
  apply H2, H1, H3.
Qed.
(* Essentially (P->Q)->(Q->R)->P->R *)

Lemma Ex_5_3_5:
  forall P Q R:Prop, (P->Q)->(P->~Q)->P->R.
Proof.
  intros P Q R H1 H2 H3.
  elim H2.
  assumption.
  apply H1; assumption.
Qed.

(** Exercise 5.4 **)

Definition dyslexic_imp :=
  forall P Q:Prop, (P->Q)->(Q->P).

Definition dyslexic_contrap :=
  forall P Q:Prop, (P->Q)->(~P->~Q).

Theorem dyslexic_imp_implies_false:
  dyslexic_imp -> False.
Proof.
  unfold dyslexic_imp.
  intro H.
  assert ((False->~False)->~False->False) as H1.
  apply H.
  apply H1.
  intro H2.
  elim H2.
  intro H2.
  assumption.
Qed.

Theorem dyslexic_contrap_implies_flase:
  dyslexic_contrap -> False.
Proof.
  unfold dyslexic_contrap.
  intro H.
  assert
    ((False->~False)->~False->~~False) as H1.
  apply H.
  apply H1.
  intro H2; elim H2.
  intro H2; assumption.
  intro H2; assumption.
Qed.

(** Exercise 5.5 **)

Theorem Ex_5_5:
  forall (A:Set)(a b c d:A),
  a=c \/ b=c \/ c=c \/ d=c.
Proof.
  intros A a b c d.
  right; right; left.
  reflexivity.
Qed.

(** Exercise 5.6 **)

Theorem Ex_5_6_a:
  forall A B C:Prop, A/\(B/\C)->(A/\B)/\C.
Proof.
  intros A B C H.
  repeat split; apply H.
Qed.

Theorem Ex_5_6_b:
  forall A B C D:Prop,
  (A->B)/\(C->D)/\A/\C -> B/\D.
Proof.
  intros A B C D H.
  elim H.
  split.
  (* It's not very nice to use auto names *)
  apply H0.
  apply H.
  repeat apply H1.
Qed.

Theorem Ex_5_6_c: forall A:Prop, ~(A/\~A).
Proof.
  intros A H.
  repeat apply H.
Qed.

Theorem Ex_5_6_d: 
  forall A B C:Prop, A\/(B\/C)->(A\/B)\/C.
Proof.
  intros A B C H.
  elim H.
  intro H1; repeat left; assumption.
  intro H1; elim H1.
  intro H2; left; right; assumption.
  intro H2; repeat right; assumption.
Qed.

Theorem Ex_5_6_e:
  forall A:Prop, ~~(A\/~A).
Proof.
  unfold not.
  intros A H.
  elim H.
  right.
  intro H1.
  apply H.
  left.
  assumption.
Qed.

Theorem Ex_5_6_f:
  forall A B:Prop, (A\/B)/\~A -> B.
Proof.
  intros A B H.
  elim H.
  intros H1 H2.
  elim H1.
  intro H3.
  contradiction.
  intro H3.
  assumption.
Qed.

(** Exercise 5.7 **)

Definition peirce := 
  forall P Q:Prop, ((P->Q)->P)->P.

Definition classic :=
  forall P:Prop, ~~P->P.

Definition excluded_middle :=
  forall P:Prop, P\/~P.

Definition de_morgan_not_and_not :=
  forall P Q:Prop, ~(~P/\~Q)->P\/Q.

Definition implies_to_or :=
  forall P Q:Prop, (P->Q)->(~P\/Q).

Lemma peirce_implies_classic:
  peirce -> classic.
Proof.
  unfold peirce, classic.
  intro H.
  assert (forall P:Prop,
          ((P->False)->P)->P) as H1.
  intro P.
  apply H.
  intros P H2.
  apply H1.
  intro H3.
  contradiction.
Qed.

Lemma nn_excluded_middle:
  forall P:Prop, ~~(P\/~P).
Proof.
  intros P H.
  assert (~P) as H1.
  intro H2.
  apply H.
  left; assumption.
  assert (~~P).
  intro H2.
  apply H.
  right; assumption.
  contradiction.
Qed.

Lemma classic_implies_excluded_middle:
  classic -> excluded_middle.
Proof.
  unfold classic, excluded_middle.
  intros H P.
  assert (~~(P\/~P)) as H1.
  apply nn_excluded_middle.
  apply H; assumption.
Qed.

Lemma excluded_middle_implies_dmnan:
  excluded_middle -> de_morgan_not_and_not.
Proof.
  unfold excluded_middle, de_morgan_not_and_not.
  intros H P Q.
  assert (P\/~P) as H1.
  apply H.
  assert (Q\/~Q) as H2.
  apply H.
  elim H1.
  elim H2.
  intros; left; assumption.
  intros; left; assumption.
  elim H2.
  intros; right; assumption.
  intros H3 H4 H5.
  assert (~P/\~Q).
  split; assumption.
  contradiction.
Qed.

Lemma modus_tollens:
  forall P Q:Prop, (P->Q)->(~Q->~P).
Proof.
  intros P Q H1 H2 H3.
  assert Q as H4.
  apply H1, H3.
  contradiction.
Qed.

Lemma dmnan_implies_implies_to_or:
  de_morgan_not_and_not -> implies_to_or.
Proof.
  unfold de_morgan_not_and_not, implies_to_or.
  intros H P Q.
  intro H1.
  apply H.
  intro H2.
  assert (~Q->~P) as H3.
  apply modus_tollens; assumption.
  assert (~P); apply H3.
  apply H2.
  apply H2.
  assert (~~P) as H4.
  apply H2.
  contradiction.
Qed.

Lemma implies_to_or_implies_peirce:
  implies_to_or -> peirce.
Proof.
  unfold implies_to_or, peirce.
  intros H1 P Q.
  assert (~P\/P) as H2.
  apply H1; intro H3; assumption.
  elim H2.
  intros H4 H5.
  apply H5; intro H6; contradiction.
  intros H7 H8; assumption.
Qed.

Lemma five_circ_impl_implies_equiv:
  forall P Q R S T:Prop,
  (P->Q)/\(Q->R)/\(R->S)/\(S->T)/\(T->P) ->
  (P<->Q)/\(Q<->R)/\(R<->S)/\(S<->T).
Proof.
  intros P Q R S T H.
  repeat split.
  apply H. intro H'; do 4 apply H; assumption.
  apply H. intro H'; do 4 apply H; assumption.
  apply H. intro H'; do 4 apply H; assumption.
  apply H. intro H'; do 4 apply H; assumption.
Qed.

Theorem classical_axioms_equiv:
  (peirce <-> classic) /\
  (classic <-> excluded_middle) /\
  (excluded_middle <-> de_morgan_not_and_not) /\
  (de_morgan_not_and_not <-> implies_to_or).
Proof.
  apply five_circ_impl_implies_equiv.
  repeat split.
  apply peirce_implies_classic.
  apply classic_implies_excluded_middle.
  apply excluded_middle_implies_dmnan.
  apply dmnan_implies_implies_to_or.
  apply implies_to_or_implies_peirce.
Qed.

(** Exercise 5.8 **)

(* repeat idtac succeeds doing nothing and
   repeat fail fails when first tried *)

(** Exercise 5.9 **)

Section ex_5_9.

  Hypothesis A:Set.
  Hypothesis P Q:A->Prop.

  Lemma ex_5_9_a:
    (exists x:A, P x \/ Q x) ->
    (ex P) \/ (ex Q).
  Proof.
    intro H1.
    elim H1.
    intros H2 H3.
    elim H3.
    intro H4; left; exists H2; apply H4.
    intro H5; right; exists H2; apply H5.
  Qed.

  Lemma ex_5_9_b:
    (ex P)\/(ex Q) -> exists x:A, P x \/ Q x.
  Proof.
    intro H1.
    elim H1.
    intro H2; elim H2; intros H3 H4; exists H3.
    left; assumption.
    intro H2; elim H2; intros H3 H4; exists H3.
    right; assumption.
  Qed.

  Lemma ex_5_9_c:
    (exists  x:A, (forall R:A -> Prop, R x)) ->
    2 = 3.
  Proof.
    intro H1.
    elim H1.
    intros H2 H3.
    assert False as H4.
    apply H3 with (R := fun (x:A) => False).
    elim H4.
  Qed.

  Lemma ex_5_9_d:
    (forall x:A, P x) -> ~(exists y:A, ~P y).
  Proof.
    intros H1 H2.
    elim H2.
    intros H3 H4.
    apply H4, H1.
  Qed.

End ex_5_9.