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