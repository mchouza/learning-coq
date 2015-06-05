Section Minimal_propositional_logic.
Variables P Q R T : Prop.

(** Exercise 3.1 **)

(* Var => P : Prop *)
(* Var => Q : Prop *)
(* Var => R : Prop *)
(* Prod => P->Q : Prop *)
(* Prod => P->R : Prop *)
(* Prod => Q->R : Prop *)
(* Prod => (Q->R)->P->R : Prop *)
(* Prod => (P->Q)->(Q->R)->P->R : Prop *)

Check ((P->Q)->(Q->R)->P->R).

(** Exercise 3.2 **)

Lemma id_P : P->P.
Proof.
  intros H.
  assumption.
Qed.

Lemma id_PP : (P->P)->(P->P).
Proof.
  intros H.
  assumption.
Qed.

Lemma imp_trans : (P->Q)->(Q->R)->P->R.
Proof.
  intros PQH QRH PH.
  apply QRH, PQH.
  assumption.
Qed.

Lemma imp_perm : (P->Q->R)->(Q->P->R).
Proof.
  intros PQRH QH PH.
  apply PQRH; assumption.
Qed.

Lemma ignore_Q : (P->R)->P->Q->R.
Proof.
  intros PRH PH QH.
  apply PRH.
  assumption.
Qed.

Lemma delta_imp : (P->P->Q)->P->Q.
Proof.
  intros PPQH PH.
  apply PPQH; assumption.
Qed.

Lemma delta_impR : (P->Q)->(P->P->Q).
Proof.
  intros PQH PH PH2.
  apply PQH.
  assumption.
Qed.

Lemma diamond : (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof.
  intros PQH PRH QRTH PH.
  apply QRTH.
  apply PQH.
  assumption.
  apply PRH.
  assumption.
Qed.

Lemma weak_peirce : ((((P->Q)->P)->P)->Q)->Q.
Proof.
  intros H1.
  apply H1.
  intros H2.
  apply H2.
  intros PH.
  apply H1.
  intros H3.
  assumption.
Qed.

(** Exercise 3.3 **)

Lemma id_P_tac : P->P.
Proof.
  intros H; assumption.
Qed.

Lemma id_PP_tac : (P->P)->(P->P).
Proof.
  intros H; assumption.
Qed.

Lemma imp_trans_tac : (P->Q)->(Q->R)->P->R.
Proof.
  intros PQH QRH PH; apply QRH, PQH; assumption.
Qed.

Lemma imp_perm_tac : (P->Q->R)->(Q->P->R).
Proof.
  intros PQRH QH PH; apply PQRH; assumption.
Qed.

Lemma ignore_Q_tac : (P->R)->P->Q->R.
Proof.
  intros PRH PH QH; apply PRH; assumption.
Qed.

Lemma delta_imp_tac : (P->P->Q)->P->Q.
Proof.
  intros PPQH PH; apply PPQH; assumption.
Qed.

Lemma delta_impR_tac : (P->Q)->(P->P->Q).
Proof.
  intros PQH PH PH2; apply PQH; assumption.
Qed.

Lemma diamond_tac :
  (P->Q)->(P->R)->(Q->R->T)->P->T.
Proof.
  intros PQH PRH QRTH PH; apply QRTH;
    [apply PQH | apply PRH]; assumption.
Qed.

Lemma weak_peirce_tac :
  ((((P->Q)->P)->P)->Q)->Q.
Proof.
  intros H1; apply H1; intros H2; apply H2;
    intros PH; apply H1; intros H3; assumption.
Qed.
