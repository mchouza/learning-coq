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

Lemma implies_and:
  forall P Q R:Prop, 
  (P->Q)->(P->R)->(P->(Q/\R)).
Proof.
  intros P Q R H1 H2 H3.
  split; [apply H1 | apply H2]; assumption.
Qed.

Lemma implies_to_or_implies_peirce:
  implies_to_or -> peirce.
(* TO BE PROVED *)