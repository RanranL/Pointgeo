Require Export PF.
Require Export Pbasics.
Require Import Reals.



Definition O: Point := 0.

(*************************************************************************************************)
(** * PROPERTY *)
(** The following definition is to definite the property of three points collinear, and "col1" is the example for it. *)

(*
Definition PCollin (B C: Point) : Prop :=
  exists l:R, B = l * C.*)

Definition collin (A B C: Point) : Prop :=
  exists m, (B - A) = m * (C - A).

(*Lemma proper1 : forall A B, 
                 PCollin B A -> collin O A B /\ vec O B = l * (vec O A).*)

Definition collinP (A B C : Point) : Prop :=
  A = O /\ exists l, B = Pmults l C.

Definition collin' (A B P : Point) :=
  exists (u v t : R), (u + v)%R = t ->
                      (u * A) + (v * B) = t * P.

Lemma Pplus_minus: forall A B, A + (B - A) = B.
Proof.
 PusingR_f.
Qed.

Lemma Pplus_opp_r: forall P, (P + -P) = O.
Proof.
  PusingR_f.
Qed.

Lemma Pplus_assoc: forall A B C, A + B + C = A + (B + C).
Proof.
  PusingR_f. 
Qed.

(** Simple tactics using the projections *)

Ltac PusingR_simpl :=
  rewrite <- Peq ; simpl ; split.

Ltac PusingR_rec := match goal with
     | id:Point |- _ => destruct id ; try PusingR_rec
end.

Ltac PusingR := intros; try PusingR_rec ; apply (proj1 (Peq _ _)) ; split ; simpl ; auto with real.

Ltac PusingR_f := PusingR ; field.

(* begin hide *)
(* Annex tactic that should not be used *)

(*

Lemma Peq : forall p1 p2 : Point, Px p1 = Px p2 /\ Py p1 = Py p2 <-> p1 = p2.

(** Simple tactics using the projections *)

Ltac PusingR_simpl :=
  rewrite <- Peq ; simpl ; split.

Ltac PusingR_rec := match goal with
     | id:Point |- _ => destruct id ; try PusingR_rec
end.

Ltac PusingR := intros; try PusingR_rec ; apply (proj1 (Peq _ _)) ; split ; simpl ; auto with real.

Ltac PusingR_f := PusingR ; field.

Ltac PusingRR :=  try rewrite <- Peq in * . *)

Ltac PRAl := PusingR; try lra.

Locate PusingR1.

Ltac Pbastac := unfold not in *; intros;
match goal with
(* destruct complex *)
     | id:Point |- _ => destruct id ; PusingRR ; simpl; try lra ; try Pbastac
(* logical destruct in goal *)
     | id: _|- _ -> _ => intros ; PusingRR ; simpl ; try lra ; try Pbastac
     | id: _|- _ /\ _ => split ; PusingRR ; simpl ; try lra ; try Pbastac
     | id: _ /\ _ |- _ => destruct id ; PusingRR ; simpl ; try lra; try Pbastac
     | id: _ \/ _ |- _ => destruct id ; PusingRR ; simpl ; try lra; try Pbastac
(* false*)
     | id: _ |- False => (apply id ; PusingR1)  ; simpl ; try lra
(* si le apply id echoue on continue le matching sur les clauses*) 

(* le ou a la fin sinon c'est galere*)
     | id: _|- _ \/ _ => try ((left ; PusingR1 ; fail) || (right ; PusingR1 ; fail)) ;
                      PusingRR ; simpl in *; try lra
     | _ => simpl in *; simpl ; try lra
end
with
PusingR1 := intros ; PusingRR ; PusingR_rec1 ; subst ; intuition ;
            try ((lra || (field ; PusingR1))).

Ltac Psolver := unfold not in *;
match goal with
(* destruct complex *)
     | id:Point |- _ => destruct id ; PusingRR ; try PusingR_rec1
(* logical destruct in goal *)
     | id: _|- _ -> _ => intros ; PusingRR ; try PusingR_rec1
     | id: _|- _ /\ _ => split ; PusingRR ; try PusingR_rec1
     | id: _ /\ _ |- _ => destruct id ; PusingRR ; try PusingR_rec1
     | id: _ \/ _ |- _ => destruct id ; PusingRR ; try PusingR_rec1
(* false*)
     | id: _ |- False => (apply id ; PusingR1) 
(* si le apply id echoue on continue le matching sur les clauses*) 

(* le ou a la fin sinon c'est galere*)
     | id: _|- _ \/ _ => try ((left ; PusingR1 ; fail) || (right ; PusingR1 ; fail)) ;
PusingRR ; simpl in *
     | _ => simpl in *
end
with
Psolver1 := intros ; PusingRR ; PusingR_rec1 ; subst ; intuition ;
            try ((lra || (field ; PusingR1))).



Lemma Pplus_eq_reg_l: forall P A B, P + A = P + B -> A = B.
Proof. Pbastac. Qed.

Lemma Pplus_eq_compat_l: forall P A B, A = B -> P + A = P + B.
Proof.
  Pbastac. 
Qed.

Lemma Pplus_eq_compat_r: forall P A B, A = B -> A + P = B + P.
Proof.
  Pbastac.
Qed.

Lemma Pplus_opp_l: forall P, - P + P = O.
Proof.
  Pbastac.
Qed. 

Lemma Popp_plus_distr: forall A B, - (A + B) = - A + - B.
Proof.
  Pbastac.
Qed.

Lemma Pplus_0_r_uniq: forall P A, P + A = P -> A = O.
Proof.
  Pbastac.
Qed.

Lemma Pplus_0_l: forall (A : Point), O + A = A.
Proof.
  Pbastac.
Qed.

Lemma Pmult_nO: forall n : R, n * O = O.
Proof. intros. PusingR1. Qed.

Lemma Pmult_eq: forall (n m : R) (P : Point), n = m -> n * P = m * P.
Proof.  PusingR1. Qed.


(****** ?????? *******)

Lemma omega3: forall x y: R, ((x + 0)%R, (y + 0)%R) = (x, y).
Proof. intros. PusingRR. Pbastac. Qed. 

(****** ???????? ****)

Lemma Pplus_0_r: forall A, A + O = A.
Proof. PusingR_f. Qed.

(************************************* Pmult ******************************************)
Lemma Pmult_O: forall n, n * O = O.
Proof. PusingR_f. Qed.

(************************************* Pminus *****************************************)

Lemma Pminus_O_r: forall P, P - O = P.
Proof. PusingR_f. Qed.

Lemma Pminus_O_l: forall P, O - P = -P.
Proof. PusingR_f. Qed.

Lemma Popp_minus_distr: forall A B, - (A - B) = B - A.
Proof. PusingR_f. Qed.

Lemma Popp_minus_distr': forall A B, - (B - A) = A - B.
Proof. PusingR_f. Qed.

Lemma Pminus_diag_uniq_sym: forall A B, B - A = O -> A = B.
Proof. intros. apply Peq in H. induction H. apply Peq. split; simpl in *; lra. Qed.

Lemma PnegO: - O = O.
Proof. PusingR_f. Qed.

Lemma Pminus_diag_uniq: forall A B, A - B = O -> A = B.
Proof. intros. apply Peq in H. induction H. apply Peq. split; simpl in *; lra. Qed.

Lemma Pminus_diag_eq: forall A B, A = B -> A - B = O.
Proof.
  intros. apply Peq in H. induction H. apply Peq. split; simpl in *; lra.
Qed.

Lemma Pminus_P: forall P, P - P = O.
Proof. PusingR_f. Qed.

(********                   Rminus END                       ***********)

Lemma Unit_right: forall A, 1 * A = A. (* Rmult_1_l *)
Proof. PusingR_f. Qed.

Lemma Unit_right': forall A, A = 1 * A.
Proof. PusingR_f. Qed.

Lemma Pmult_plus_distr_l: forall n B C,
    n * (B + C) = n * B + n * C.
Proof. PusingR_f. Qed.
 
Lemma Pmult_plus_distr_r: forall a b P,
    (a + b) * P = a * P + b * P.
Proof. PusingR_f. Qed. 

Lemma Pmult_minus_distr_r: forall a b P,
    (a - b) * P = a * P - b * P.
Proof. PusingR_f. Qed.

Lemma Pmult_minus_distr_l: forall n B C,
    n * (B - C) = n * B - n * C.
Proof. PusingR_f. Qed.

Hint Resolve Pmult_minus_distr_l : point.

Lemma property6: forall A B, A · B = B · A.
Proof. (* intros. unfold Pquantityprod. induction A, B. lra. Qed.*) Abort.

Lemma Pplus_1: forall A B, A + B = O <-> A = (-1) * B.
Proof.
  intros. split; intros. apply Peq in H; induction H ; apply Peq; simpl in *; lra.
  apply Peq in H; induction H; apply Peq; simpl in *; lra.
Qed.
  
Lemma Pmults_1: forall n m A, Pmults (n) (Pmults m A) = Pmults (n * m) A.
Proof. PusingR_f. Qed.

Lemma Alge: forall x: R, ((-1) * (-1 * x) = x)%R.
Proof. intros. lra. Qed.

Lemma collinO1: forall A B,
  (exists (l : R), A = Pmults l B) -> collin' A B O. 
Proof.
  intros. unfold collin'. destruct H.  
  exists 1%R. exists (-1 * x)%R. exists (1-x)%R.
  intros. rewrite Pmult_O with (n := (1-x)%R). rewrite Unit_right.
  apply Pplus_1. rewrite Pmults_1. rewrite Alge.
  auto.
Qed.

Definition Xcollin (A B C D F : Point) :=
  forall u v r s, (u + v = r + s)%R ->
         (u * A) + (v * B) = (r * C) + (s * D) ->
         (r + s) * F = (r * C) + (s * D).  
(*
Lemma COLLIN: forall A B C,
    A = O -> collin A B C -> PCollin B C.
Proof.
  intros. unfold PCollin. unfold collin in *.
  rewrite H in *.
  do 2 rewrite Pminus_O_r in *. auto.
Qed.  
*)
