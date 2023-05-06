From Coq Require Import Arith.Arith.
Require Export Coq.Reals.RIneq.
Require Export Coq.Reals.R_sqrt.
Require Export Coq.micromega.Lra.
Require Import Lemma.
Require Import PF.
Require Export Pbasics.
Require Export Pconstruct.
Require Export PTactic.

Lemma Elim_2: forall p1 p2: Point, p1 - p2 + p2 = p1.
Proof. PusingR_f. Qed.

Lemma Pplus_eq_reg_r: forall P A B, A + P = B + P -> A = B.
Proof. intros. apply Peq in H. simpl in H. induction H. apply Peq; split; lra. Qed.

Lemma Pplus_eq_reg_r': forall P A B, A = B -> A + P = B + P.
Proof. intros; rewrite H; auto. Qed.

Lemma eqPoint: forall (A B C D : Point), A = B -> C = D -> (A + C)%Point = (B + D)%Point.
Proof. HilXcol. Qed.
(*  intros. apply Peq in H. induction H.  apply Peq in H0. induction H0. apply Peq.
split;simpl in *. rewrite H; rewrite H0; auto.  rewrite H1; rewrite H2; auto.
Qed.*)

Tactic Notation " PerPendTac " := apply Peq; split; simpl in *; lra. 

Lemma property11 : forall A B, 
   (exists l, B = l * A ) -> collin O B A /\ exists m, vec O B = m * (vec O A).
Proof. intros. unfold collin, vec in *;split; Oelim. Qed.

Property property2_1: forall A B C, A + B = C -> Parall A O B C.
Proof. Oelim. (* HilXcol.*) Qed.

Property property2_2: forall A B M, A + B = 2 * M -> Midpoint M A B.
Proof. HilXcol. Qed.

Lemma property2_3: forall A B P, A + B = 3 * P -> Ptraingle_median P A B O.
Proof. HilXcol. Qed.

Lemma property3 : forall A B, B - A = vec A B.
Proof. HilXcol. Qed. 
       
Lemma property3': forall t A B P, B - A = t * P -> t = 1%R -> Parall O A B P.
Proof. HilXcol. Qed. 
 (* Oelim. subst. apply Peq in H; induction H;
  apply Peq; split; simpl in *; lra.
Qed.
  *)

Lemma property4_1 : forall (u v: R) (A B F: Point),
    u * A + v * B = (u + v) * F -> u * (A - F) = v * (F - B).
Proof. HilXcol. Qed.
(*  intros. do 2 rewrite Lemma.Pmult_minus_distr_l.
  apply Pplus_eq_reg_r with (P := v * B).
  rewrite Elim_2. assert (Hs :  u * A - u * F + v * B = u * A + v * B - u * F). PusingR_f.
  rewrite Hs, H. PusingR_f.
Qed.
*)
Lemma Pquan_distr_r: forall A B C : Point,
   (((A - B) · C)%Point = (A · C)- (B · C))%R.
Proof. HilXcol. Qed.
 (* Oelim. unfold Pminus. unfold Pquantityprod. simpl in *. 
  induction A. induction B. induction C. lra.
Qed.
 *)

(* property6 *)       
Lemma Pquan_comm: forall A B,
    A · B = B · A.
Proof. HilXcol. Qed.
(* unfold Pquantityprod. induction A. induction B. lra. Qed. *)

Hint Resolve Pquan_comm : point.

Lemma Pquan_distr_l: forall A B C : Point,
     ((A · C)- (B · C)=((A - B) · C)%Point)%R.
Proof. (* HilXcol.*) intros. rewrite Pquan_distr_r; auto. Qed.

(** Definition Collin (l : Z) (O A B : Point) :=
  B = Pmults l A. *)    

(*
Lemma Pmult_div : forall (p1 p2: Point) (l: R),
    l * p1 = p2 ->
    l <> 0%R ->
    p1 = /l * p2.
Proof. intros. rewrite <- H, <- Pscal_assoc. apply Rinv_l in H0. rewrite H0; PusingR_f. Qed.
 *)

Example first_exam: forall A B N C P G M,
    A = O ->  
    Midpoint P A B ->
    Midpoint N A C ->
    Midpoint M B C ->
    Xcollin N B P C G ->
    collin A G M.
Proof.   
  Oelim.
  assert (HX : 2 * N + 1 * B = 2 * P + 1 * C). Psolver.
  apply H3 in HX; auto.
  exists (2/3)%R; Psolver. 
Qed.

Example first_exam': forall A B N C P G M,
    A = O ->  
    Midpoint P A B ->
    Midpoint N A C ->
    Midpoint M B C ->
    Xcollin N B P C G ->
    collin A G M.
Proof.
  intros. unfold Midpoint, Xcollin, collin in *.
  rewrite H in *. rewrite Pplus_0_l in *. do 2 rewrite Pminus_O_r.
  assert (HX : 2 * N + 1 * B = 2 * P + 1 * C ).
  { rewrite <- H1, H0. PusingR_f. }
  apply H3 in HX; auto.
  exists (2/3)%R; Psolver.
Qed.  
 
Example Example2: forall A B C D M P,
    A = O ->
    Parall A B C D ->
    Midpoint M A B -> 
    Xcollin A C M D P ->
    vec A C = 3 * vec A P.
Proof. HilXcol 2%R 1%R 2%R 1%R. Qed.
(*
Lemma Pmult_nO: forall n : R, n * O = O.
Proof. intros. PusingR1. Qed.

Lemma Pmult_eq: forall (n m : R) (P : Point), n = m -> n * P = m * P.
Proof. intros. PusingR1. Qed.*)
 
Example Example2_contra: forall A B C D M P,
    A = O ->
    Parall A B C D ->
    Midpoint M A B -> 
    Xcollin A C M D P ->
    vec A C = 3 * vec A P.
Proof.
  intros.
  unfold Parall, Midpoint, Xcollin, vec in *.
  rewrite H in *.  
  rewrite Pplus_0_l in H1. 
  do 2 rewrite Pminus_O_r.
  rewrite H1, <- Pmult_nO with (n:= 2) in H0.
  rewrite <- Unit_right with (A:=C), <- Unit_right with (A:=D) in H0.
  assert (Hx : (2 + 1)%R = (2 + 1)%R). { lra. }
  apply H2 in Hx.
  2: assumption.
  rewrite <- Hx in H0.
  rewrite Pmult_nO, Pplus_0_l, Unit_right in H0.
  rewrite H0.
  apply Pmult_eq; lra.
Qed.

  (*
  Oelim.
  assert (HX : 2 * O + 1 * C = 2 * M + 1 * D).
  {  rewrite H0, <- H1. PusingR_f. }
  induction H2 with (u:=2) (v:=1%R) (r:=2) (s:=1%R); auto.
  assert (HCP :  2 * O + 1 * C = C).
  { PusingR_f. }
  rewrite HCP in HX. rewrite HX. PusingR_f.
Qed.
 *)

Lemma Rmove: forall a b : R,
    (a - b = 0 <-> a = b)%R.
Proof. intros. split; lra. Qed.
 
Theorem tri_3_heights': forall A B C H,
    H = O ->
    Perpendicular B C A H ->
    Perpendicular B H A C ->
    Perpendicular C H A B.
Proof. HilXcol. Qed.
(*  Oelim. rewrite Pquan_distr_r in *. rewrite Pquan_comm in H2.
  rewrite Pquan_distr_r in H2. rewrite Pquan_comm in H1. rewrite Rmove in *.
  rewrite Pquan_comm. rewrite Pquan_distr_r.
  rewrite Rmove. rewrite H1 in H2. rewrite Pquan_comm. rewrite H2.
  auto with point. 
Qed.
*)

Lemma l1: forall A B C, A + (B - C) = A + B - C.
Proof. PusingR_f. Qed.

Lemma l2: forall A B C, A - (B + C) = A - B - C.
Proof. PusingR_f. Qed.

Lemma l3: forall A B C, A = C -> A - B = C - B.
Proof. intros; subst; reflexivity. Qed.  
 
Theorem p23_exam4: forall A B C D M N P Q,
    Parall A B C D ->
    Midpoint A M P -> 
    Midpoint D M N ->
    Midpoint C Q N ->
    Midpoint B P Q.
Proof. HilXcol. Qed.
(*Oelim; Movsub B; Movsub P; Movsub Q; Movsub M; PusingR_f. Qed. *)

Definition mol A B : R := sqrt (Px B - Px A)^2 + (Py B - Py A)^2.

(*Definition Pnorm_sqr (p : Point) : R := Pquantityprod p p.

Definition Pnorm (p : Point) : R := (sqrt (Pnorm_sqr p)).*)

(* Definition Psquare (A:Point): R := A · A. *)

Definition distance (A B: Point) : R := sqrt (Pnorm_sqr (B - A))%R.

Lemma Pmult_eq_compat_r : forall (A B: Point) (r : R),
    A = B -> r * A = r * B.
Proof. intros; rewrite H; auto. Qed.

Lemma Pmult_distr_r: forall (l r: R) (P: Point), l * (r * P) = (l * r) * P.
Proof. auto with point. Qed.

Lemma rsqrt : forall l : R, (l * l)%R = l².
Proof. intro. rewrite Rsqr_pow2. lra. Qed.

Lemma Psquarel : forall (A: Point) (l: R),
  (Pnorm_sqr (l * A))%R = (l² * Pnorm_sqr A)%R.
Proof. intros. unfold Pnorm_sqr, Pquantityprod. rewrite <- rsqrt. simpl. lra. Qed.

Lemma rsqrt_l' : forall l m : R, 0 <= m  -> sqrt (l² * m)%R = (sqrt l² * sqrt m)%R. 
Proof. intros. apply sqrt_mult. apply Rle_0_sqr. auto. Qed. 

Lemma rsqrt_l : forall l m : R, 0 <= m  -> sqrt (l² * m)%R = (Rabs l * sqrt m)%R. 
Proof.
  intros. apply rsqrt_l' with (l := l) in H.
  rewrite H. rewrite sqrt_Rsqr_abs. auto.
Qed.

Lemma rgt: forall r: R, r > 0%R  -> r <> 0%R.
Proof. intros. apply Rlt_dichotomy_converse. auto. Qed.
                                 
  
Lemma property4_2 : forall (u v: R) (A B F: Point),
    u <> 0%R ->
    0 < Pnorm_sqr (F - B) ->
    u * (A - F) = v * (F - B) ->
    (distance F A * /distance B F)%R = Rabs (v * /u)%R. 
Proof. 
  intros. generalize H0; intro Hs. generalize H0; intro Hr.
  unfold distance. apply Pmult_eq_compat_r with (r:=(/u)%R) in H1.
  do 2 rewrite Pmult_distr_r in H1. rewrite Rmult_comm in H1.  apply Rinv_r in H.
  rewrite H in H1. rewrite Unit_right in H1. rewrite H1. rewrite Psquarel.
  apply Rlt_le in H0. apply rsqrt_l with (l := ((/ u * v))%R) in H0. rewrite H0.
  apply rgt in Hs. apply Rinv_r in Hs. rewrite Rmult_assoc.
  generalize Hr; intro Hn. apply Rlt_le in Hr.
  apply sqrt_div with (y := (Pnorm_sqr (F - B))%R) in Hr.
  unfold Rdiv in Hr. rewrite <- Hr.
  rewrite Hs. rewrite sqrt_1. rewrite Rmult_1_r.
  rewrite Rmult_comm. auto. apply Hn.
Qed.
(*sqrt_div: forall x y : R, 0 <= x -> 0 < y -> sqrt (x / y) = (sqrt x / sqrt y)%R.*)

Lemma property4 : forall (u v: R) (A B F: Point),
    u <> 0%R ->
    0 < Pnorm_sqr (F - B) ->
   u * A + v * B = (u + v) * F ->
   (distance F A * /distance B F)%R = Rabs (v * /u)%R.
Proof. intros. apply property4_1 in H1. apply property4_2. auto. auto. auto. Qed.
 
Lemma property6: forall A B, A · B = B · A.
Proof. HilXcol. Qed.
(* Proof. intros. unfold Pquantityprod. induction A. induction B. lra. Qed. *)

(*Lemma property_7 : forall.*)

Lemma negP_n: forall x y: R, -(x, y) = ((-x)%R, (-y)%R).
Proof. HilXcol. Qed.

Definition OutP A B := B - A.

Notation "  A @ B  " := (OutP A B)
                          (at level 50, left associativity) : Point_scope.

Lemma property8: forall A B, (A @ B) = - (B @ A). 
Proof. intros. unfold OutP.  PusingR_f. Qed.

Lemma removeb: forall A B C, A + (B - C) = A + B - C.
Proof. PusingR_f. Qed.

Lemma property9_1: forall (u v: R) (A B C P: Point),
    u*A + v*B = (u+v)*C ->
    u*(A @ P) + v*(B @ P) = (u+v)*(C @ P). 
Proof. HilXcol. Qed.

Lemma property9_2: forall u v A B C P,
    u*A + v*B = (u+v)*C ->
    u*(P@A) + v*(P@B) = (u+v)*(P@C). 
Proof.
  HilXcol. (* Oelim. apply Peq in H; induction H; apply Peq; split; simpl in *; lra. *)
Qed.

Lemma property10_1 : forall u v r A B C P,
    u * A + v * B = r * C ->
    u * (A @ P) + v * (B @ P) = r * (C @ P) + (u + v - r) * P.
Proof.
  HilXcol. (*Oelim. unfold OutP. do 3 rewrite Lemma.Pmult_minus_distr_l. rewrite <- H. PerPendTac.*)
Qed.  

Lemma property10_2 : forall u v r A B C P,
    u * A + v * B = r * C ->
    u * (P @ A) + v * (P @ B) = r * (P @ C) - (u + v - r) * P.
Proof. HilXcol.
 (* intros. unfold OutP. do 3 rewrite Lemma.Pmult_minus_distr_l. rewrite <- H.
  apply Peq; split; simpl; lra.*)
Qed.

Lemma property11_1 : forall A B C, s A B C = s B C A.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_2 : forall A B C, s B C A = s C A B.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_3 : forall A B C, s C A B = (- s A C B)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_4 : forall A B C, (- s A C B)%R = (- s B A C)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_4' : forall A B C, (s A C B)%R = (s B A C)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_4'' : forall A B C, (s A C B)%R = (- s A B C)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_5 : forall A B C, (- s B A C)%R = (- s C B A)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_6 : forall A B C, s A B C = (- s C B A)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.

Lemma property11_abs : forall A B C, Rabs (s A B C) = Rabs (s C B A).
Proof. intros. rewrite property11_6. rewrite Rabs_Ropp. auto. Qed.

Lemma property11_abs' :forall A B C, Rabs (s A B C) = Rabs (s B A C).
Proof.
  intros. rewrite <- property11_4' with (A:=A). rewrite property11_1.
  rewrite property11_2. rewrite property11_3.
  rewrite Rabs_Ropp. auto.
Qed.

Lemma property11_abs'' : forall A B C, Rabs (s A B C) = Rabs (s A C B).
Proof. intros. rewrite property11_4''. rewrite Rabs_Ropp. auto. Qed.

Lemma Psdistr: forall (u : R) (A B C : Point),
    (u * s A B C)%R = 
      (u * Px A * Py B + u * Px B * Py C + u * Px C * Py A
       - u * Px A * Py C - u * Px B * Py A - u * Px C * Py B)%R.
Proof. HilXcol. (*intros; unfold s; lra.*) Qed.


Lemma Psdistr': forall (u : R) (A B C : Point),
    (u * s A B C)%R = s (u*A) B C.
Abort.

Lemma property12 : forall u v A B C P Q,
    u * A + v * B = (u+v) * C ->
    (u * s A P Q + v * s B P Q)%R = ((u + v) * s C P Q)%R.
Proof. 
  intros. rewrite Psdistr with (u := (u+v)%R).
  unfold s. apply Peq in H. induction H. simpl in *.
  rewrite <- H.
  assert (Hs: ((u + v) * Px Q * Py C)%R = ((u + v) * Py C * Px Q)%R). lra.
  assert (Hr: ((u + v) * Px P * Py C)%R = ((u + v) * Py C  * Px P)%R). lra.
  rewrite Hs, Hr. rewrite <- H0. lra.
Qed.

Lemma property13 : forall u v r A B C P Q,
    u * A + v * B = r * C ->
    (u * s A P Q + v * s B P Q = r * s C P Q + (u + v - r) * s O P Q)%R.
Proof.
  intros. rewrite Psdistr with (u:=r). unfold s. unfold O.
  apply Peq in H; induction H; simpl in *. rewrite <- H.
  assert (Hs: (r * Px Q * Py C)%R = (r * Py C * Px Q)%R). lra. rewrite Hs; rewrite <- H0.   
  assert (Hr: (r * Px P * Py C )%R = (r * Py C * Px P)%R). lra. rewrite Hr; rewrite <- H0. lra.
Qed.
               
Lemma Example7: forall A B C D E P,
    B = O ->
    Parall A B C D ->
    ParallE E A B C D ->
    (P @ A) + (P @ C) = 2 * (P @ E).
Proof. HilXcol. Qed.
(*  Oelim. 
  generalize H0. intros. apply H1 in H0.
  induction H0. rewrite <- Unit_right with (A := (P@A)).
  rewrite <- Unit_right with (A := (P@C)).
  apply property9_2. do 2 rewrite Unit_right. rewrite H0. PusingR_f.
Qed.
*)

(*Lemma eqPoint: forall (A B C D : Point), A = B -> C = D -> (A + C)%Point = (B + D)%Point.
Proof. HilXcol. Qed.
 intros. apply Peq in H. induction H.  apply Peq in H0. induction H0. apply Peq.
split;simpl in *. rewrite H; rewrite H0; auto.  rewrite H1; rewrite H2; auto.
Qed.*)

Open Scope Point.

Lemma Elim_0: forall (l: R) (p1 p2: Point), p1 = p2 -> l * p1 = l * p2.
Proof. intros. rewrite H. auto. Qed.

Lemma Elim_1 : forall (l: R) (p1 p2 p3 p4: Point), p1 + p2 = p3 + p4 -> l * p1 + l * p2 = l * p3 + l * p4.
Proof. intros. do 2 rewrite <- Pmult_add_distr_l. rewrite H; auto. Qed.

Lemma Elim_div: forall (l: R) (p1 p2: Point),(l <> 0)%R -> l * p1 = l * p2 -> p1 = p2. 
Proof.
  intros. rewrite Unit_right' with (A := p1). rewrite Unit_right' with (A := p2).
  apply Rinv_r with (r:=l) in H. rewrite <- H.
  rewrite Rmult_comm. do 2 rewrite Pscal_assoc. rewrite H0. auto.
Qed.

Lemma Elim_div_1: forall (l: R) (p1 p2 p3 p4: Point),
    (l <> 0)%R -> l * p1 + l * p2 = l * p3 + l * p4  -> p1 + p2 = p3 + p4.
Proof.
  intros. do 2 rewrite <- Pmult_add_distr_l in H0. apply Elim_div with (l := l); auto.
Qed.

 (* 
Lemma Elim_2: forall p1 p2: Point, p1 - p2 + p2 = p1.
Proof. PusingR_f. Qed.
*)
Lemma Elim_2': forall p1 p2: Point, p1 + p2 - p2 = p1.
Proof. PusingR_f. Qed.
                 
Lemma Elim_3: forall p1 p2: Point, p1 - p2 + p1 = p1 + p1 - p2.
Proof. PusingR_f. Qed.

Lemma Elim_4: forall p1 p2: Point, p1 + (- p2) = p1 - p2.
Proof. PusingR_f. Qed.

Lemma Elim_5 : forall p1 p2: Point, p1 - p2 = - p2 + p1.
Proof. PusingR_f. Qed.

Lemma Elim_6 : forall p1 p2 p3: Point, p1 - p3 = p2 - p3 -> p1 = p2.
Proof. intros. Movsub p1. PusingR_f. Qed.  

Lemma Elim_7 : forall p1 p2 p3: Point, p1 = p2 -> p1 - p3 = p2 - p3.
Proof. intros. rewrite H; auto. Qed.

Lemma Elim_8: forall (l: R) (p: Point), (-l)%R * p = -(l * p).
Proof. PusingR_f. Qed.

Lemma Pminus_O: forall A, A - A = O.
Proof. PusingR_f. Qed.  


(* HilCol 1 5 3 3 *)
Lemma Example3_1 : forall A B C D P Q,
    A = O ->
    Xcollin C Q P B D ->
    C - A = 3 * (P-A) ->
    3 * (B - A) = 5 * (Q - A) ->
    D - P = B - D (*/\
    5 * (D - Q) = C - D /\
    3 * (R - B) = R - C /\
    3 * (Q - P) = 2 * (R - Q)*).
Proof.
 Oelim. symmetry in H2. eapply eqPoint in H2.
  2: apply H1.
  assert (Hm : (1 + 5)%R = (3 + 3)%R). lra. apply H0 in Hm.
  (*rewrite Unit_right' with (A := C) in H2. *)  rewrite Pscal_distr_R_r in Hm.
  2: rewrite <- Unit_right' with (A := C); apply H2. apply Elim_div_1 in Hm. 2: lra.
  apply Pplus_eq_reg_r with (P := D). rewrite Elim_2. rewrite Elim_3.
  apply Pplus_eq_reg_r with (P := P). rewrite Elim_2. auto.
  rewrite Padd_comm with (z1:=B); auto.
Qed.
 
Lemma Example3_2 : forall A B C D P Q,
    A = O ->
    Xcollin C Q P B D ->
    C - A = 3 * (P-A) ->
    3 * (B - A) = 5 * (Q - A) ->
    5 * (D - Q) = C - D.
Proof.
  Oelim. symmetry in H2. eapply eqPoint in H2.
  2: apply H1.
  assert (Hm : (1 + 5)%R = (3 + 3)%R).
  lra. apply H0 in Hm. rewrite <- Hm in H2. 
  rewrite Lemma.Pmult_minus_distr_l with (n:=5).
  apply Pplus_eq_reg_r with (P := D). rewrite Elim_2. symmetry.
  apply Pplus_eq_reg_r with (P:=5*Q). rewrite H2. PusingR_f.
  rewrite <- Unit_right' with (A:=C); auto.
Qed.

Lemma eqPoint_minus : forall A B C D : Point, A = B -> C = D -> A - C = B - D.
Proof. intros. rewrite H, H0; auto. Qed.                    

Lemma Example3_3 : forall A B C P Q R,
    A = O ->
    Xcollin B C Q P R ->
    C - A = 3 * (P - A) ->
    3 * (B - A) = 5 * (Q - A) ->
    3 * (R - B) = R - C (* 3 * (Q - P) = 2 * (R - Q)*).
Proof.
  Oelim.
  eapply eqPoint_minus in H1.  
  2: apply H2.
  assert (Hm : (3 + (-1))%R = (5 + (-3))%R). lra. apply H0 in Hm.
  symmetry. 
  (*rewrite Unit_right' with (A := C) in H2. *)  rewrite Pscal_distr_R_r in Hm.
  rewrite Elim_5. rewrite Elim_5 in H1. apply Elim_6 with (p3 := R2). rewrite Elim_2'.
  assert (Hn :  5 * Q + -3 * P = 5 * Q - 3 * P). PusingR_f. rewrite Hn in Hm.
  rewrite <- Hm in H1. 
  apply Elim_7 with (p3 := 3*B) in H1. rewrite Elim_2' in H1.
  rewrite H1. PusingR_f.
  assert (Hx : 3 * B - C = 3 * B + -1 * C). PusingR_f.
  assert (Hs : 5 * Q + -3 * P = 5 * Q - 3 * P). PusingR_f.
  rewrite <- Hx. rewrite Hs. auto.
Qed.

(* Hilxcol 3%R (-1)%R 5%R (-3)%R *)
Lemma Example3_4 : forall A B C P Q R,
    A = O ->
    Xcollin B C Q P R ->
    C - A = 3 * (P - A) ->
    3 * (B - A) = 5 * (Q - A) ->
    3 * (Q - P) = 2 * (R - Q).
Proof. 
  Oelim. 
  eapply eqPoint_minus in H1.  
  2: apply H2.
  assert (Hm : (3 + (-1))%R = (5 + (-3))%R).  lra. apply H0 in Hm.
  symmetry. 
  (*rewrite Unit_right' with (A := C) in H2. *)
  rewrite Pscal_distr_R_r in Hm.
  apply Elim_6 with (p3:= 3*(Q-P)).
  rewrite Pminus_O.
  apply Elim_7 with (p3:=(5*Q + -3*P)) in Hm.
  rewrite Pminus_O in Hm. rewrite <- Hm. PusingR_f.
  apply Elim_6 with (p3:= 5 * Q + -3 * P).
  rewrite Pminus_O.
  apply Elim_7 with (p3:=(5*Q-3*P)) in H1.
  rewrite Pminus_O in H1. 
  rewrite <- H1. PusingR_f.
Qed.
 

Definition triangle (A B C: Point) : Prop := ~ collin A B C.

Lemma Elim_9: forall B C D, B + C = 2 * D -> 1/2 * (B + C) = D.
Proof. intros. Movsub B; PusingR_f. Qed.
(*
Definition Psquare (A:Point): R := A · A.

Definition distance (A B: Point) : R := sqrt (Psquare(B - A)).
*)
Lemma Elim_10: forall A B: Point, Pnorm_sqr (A + B) = (Pnorm_sqr A + Pnorm_sqr B + 2 * (A · B))%R.
Proof. unfold Pnorm_sqr. HilXcol. Qed.

Lemma Elim11: forall A B C: Point, A + B = C -> Pnorm_sqr (A + B)  = Pnorm_sqr C.
Proof. intros. rewrite H; auto. Qed.

Axiom Elim12: forall A B C: Point, A + B = C -> (Pnorm_sqr A + Pnorm_sqr B + 2 * (A · B))%R = Pnorm_sqr C.
Axiom Elim13: forall B C: Point, (2 * (B · C))%R = (((1/2) * Pnorm_sqr (B + C))%R - (1/2 * Pnorm_sqr (B - C)))%R.
Axiom Elim14: forall B C D: Point,((1 / 2 * Pnorm_sqr (2 * D) - 1 / 2 * Pnorm_sqr (B - C)))%R
                                  = (2 * Pnorm_sqr D - 1 / 2 * Pnorm_sqr (B - C))%R.
Lemma Elim15: forall A B C D: R, (A + B + (C - D))%R = (A + B + C - D)%R.
Proof. intros. lra. Qed.
  
Axiom Elim16: forall B C D:Point, (Pnorm_sqr B + Pnorm_sqr C + (2 * Pnorm_sqr D - 1 / 2 * Pnorm_sqr (B - C)))%R = Pnorm_sqr (2 * D) -> (2 * Pnorm_sqr D)%R = (Pnorm_sqr B + Pnorm_sqr C - 1 / 2 * Pnorm_sqr (B - C))%R.

Lemma Example5_1 : forall A B C D: Point,
    A = O ->
    triangle A B C ->
    Midpoint D B C ->
    (2 * Pnorm_sqr (D-A))%R = (Pnorm_sqr B + Pnorm_sqr C - (1/2 * Pnorm_sqr (B - C))%R)%R.
Proof. 
  Oelim. generalize H1; intro Hn. apply Elim12 in H1. rewrite Elim13 in H1.
  rewrite Hn in H1. rewrite Elim14 with (B:=B) (C:=C) (D:=D) in H1. apply Elim16. apply H1.
Qed.

Lemma Perpend_prop2: forall (A B: Point) (l : R), A · (l * B) = (l * (A · B))%R.
Proof. intros. unfold Pquantityprod. simpl. lra. Qed.

Lemma Perpend_prop2': forall (A B: Point) (l : R), (l * A) · B = (l * (A · B))%R.
Proof. intros.  unfold Pquantityprod. simpl. lra. Qed.

Lemma Perpend_prop: forall (A B : Point) (l : R), A · B = 0%R -> A · (l * B) = 0%R.
Proof. intros. rewrite Perpend_prop2. rewrite H. lra. Qed.
          
Lemma Perpend_prop3: forall (A B : Point) (l : R), l <> 0%R -> (l * A) · B = 0%R -> A · B = 0%R.
Proof. 
  intros. rewrite Perpend_prop2' in H0.
  apply Rmult_integral in H0. induction H0. induction H; auto. auto.
Qed.

Lemma Perpend_prop3': forall (A B : Point) (l : R), l <> 0%R -> A · B = 0%R -> (l * A) · B = 0%R.
Proof. intros. rewrite Perpend_prop2'. rewrite H0. lra. Qed.

Lemma Perpend_prop4 : forall A B C: Point, (A - B) · C = (A · C - B · C)%R.
Proof. intros. unfold Pquantityprod. simpl; lra. Qed.

Lemma Perpend_prop5 : forall A B C : Point, A · (B + C) = (A · B + A · C)%R.
Proof. intros. unfold Pquantityprod. simpl; lra. Qed.

Lemma Perpend_prop6 : forall A B C: Point, A · (B - C) = (A · B - A · C)%R.
Proof. intros. unfold Pquantityprod. simpl; lra. Qed.

(*Tactic Notation " PerPendTac " := apply Peq; split; simpl; lra.*)

Lemma Example6: forall (A B C E D F G M N H L : Point) (u v : R),
    H = O ->
    triangle A B C ->
    Ptraingle_median G A B C ->
    Ptraingle_H H A B C ->
    Midpoint D B C ->
    Midpoint E A C ->
    Midpoint F A B ->
    PonLine L B C u ->
    PonLine M A C v ->
    Perpendicular A L D H ->
    Perpendicular B M E H ->
    Perpendicular C N F H ->
    Perpendicular M L G H.
Proof.
  intros. 
  unfold Ptraingle_H in H3. induction H3. induction H12. Oelim. unfold PonLine in *.
  rewrite H7 in H9. apply Perpend_prop with (l:= 2%R) in H9. rewrite <- H4 in H9.
  rewrite H8 in H10. apply Perpend_prop with (l:=2%R) in H10. rewrite <- H5 in H10.
  apply Perpend_prop3 with (l := 3). lra. rewrite H7, H8.
  assert (Hs: (3*(v*A+(1-v)*C-(u*B+(1-u)*C))=3*v*(A-C)-3*u*(B-C))).
  PerPendTac. rewrite Hs.
  (* H9 *)
  assert (Hg: 3*G-A=B+C). rewrite H2. PerPendTac.  
  rewrite Perpend_prop4.
  assert (Hj: (A - (u * B + (1 - u) * C)) = A - C - u * (B - C)). PerPendTac.
  rewrite Hj in H9. rewrite Perpend_prop4 in H9. rewrite Perpend_prop5 in H9. 
  rewrite <- Hg in H9. rewrite Perpend_prop6 in H9. rewrite property6 in H12.
  rewrite H12 in H9. rewrite property6 in H3. do 2 rewrite Perpend_prop2' in H9.
  rewrite H3 in H9.
  assert (Hk: (0 + (A - C) · C - (u * (B - C) · (3 * G) - u * 0))%R = ((A - C) · C - (3 * u * (B - C)) · G)%R). { unfold Pquantityprod. simpl. lra. } rewrite Hk in H9.
  apply -> Rmove in H9. rewrite <- H9.
  (* H10 *)
  assert (Hq: 3*G-B=A+C). rewrite H2. PerPendTac.
  assert  (Hw: (B - (v * A + (1 - v) * C)) = B - C - v * (A - C)). PerPendTac.
  rewrite Hw in H10.  rewrite Perpend_prop4 in H10. rewrite Perpend_prop5 in H10.
  rewrite <- Hq in H10. rewrite Perpend_prop6 in H10. rewrite H3 in H10.
  do 2 rewrite Perpend_prop2' in H10. rewrite H12 in H10.
  assert (Hr: (0+(B-C)·C-(v*(A-C)·(3*G)-v*0))%R=((B-C)·C-(3*v*(A-C))·G)%R).
  { unfold Pquantityprod. simpl. lra. } rewrite Hr in H10.
  apply -> Rmove in H10.  rewrite <- H10. rewrite <- Perpend_prop4.
  assert (Ht: (B - C - (A - C)) = -1 * (A - B)). PerPendTac. rewrite Ht.
  apply Perpend_prop3'. lra. rewrite property6. auto.
Qed.

Lemma Example8 : forall A B C P Q R' L M N: Point,
    A = O ->
    triangle A B C ->
    Midpoint P B C ->
    C - Q = 2 * (Q - A) ->
    R' - A = 3 * (B - R') ->
    Xcollin P A R' C M ->
    Xcollin R' C B Q L ->
    Xcollin A P B Q N ->
    (252* s L M N)%R = (25 * s A B C)%R.
Proof.
  Oelim.
  (* Hs: C = 3Q *) 
  apply Pplus_eq_reg_r' with (P:= Q) in H2. rewrite Elim_2 in H2. 
  assert (Hs : C = 3 * Q). rewrite H2. PusingR_f.
  generalize H1; intro H1'. generalize H1; intro H1''. generalize Hs; intro Hs'.
  (* Hg: B + 3Q = 4N *)
  rewrite Hs in H1.
  assert (Hf : 2 * P = 2 * P + 2 * O). PusingR_f.  rewrite Hf in H1.
  rewrite <- Unit_right with (A := B) in H1. 
  assert (Hg: (2 + 2)%R = (1 + 3)%R). lra. apply H6 in Hg.  2: rewrite H1; rewrite Padd_comm; auto.
  (* H3: 3B = 4R *) 
  rewrite Lemma.Pmult_minus_distr_l in H3.  apply Pplus_eq_reg_r' with (P:= 3 * R') in H3.
  rewrite Elim_2 in H3. assert (Hi : R' + 3 * R' = 4 * R'). PusingR_f. rewrite Hi in H3.
  generalize H3; intro H3'.
  (* H1':  3B + 3C = 6P *)
  apply Elim_0 with (l:=3) in H1'. rewrite Pscal_distr_C_l in H1'.
  assert (Hj: 3 * (2 * P) = 6 * P). PusingR_f.
  rewrite Hj in H1'.
  (* Hg': 4R + 3C = 7M *)
  rewrite <- H3 in H1'. symmetry in H1'.
  assert (Hf': 6 * P = 6 * P + 1 * O). PusingR_f. rewrite Hf' in H1'.
  assert (Hg' : (6 + 1)%R = (4 + 3)%R). lra.
  apply H4 in Hg'. 2: rewrite H1'; rewrite Padd_comm; auto.
  (* Hg'': C + 8R = 3Q + 6B = 9L *)
  (* * H3: 8R = 6B*)
  apply Elim_0 with (l:=2) in H3.
  assert (Hj' : 2 * (4 * R') = 8 * R'). PusingR_f. rewrite Hj' in H3.
  assert (Hj'' : 2 * (3 * B) = 6 * B). PusingR_f. rewrite Hj'' in H3.
  apply eqPoint with (A:= 8 * R') (B := 6 * B) in Hs. 2: auto.
  rewrite Unit_right' with (A:= C) in Hs. 
  assert (Hg'' : (8 + 1)%R = (6 + 3)%R). lra.
  apply H5 in Hg''. 2: auto.
  (* Hg '': 9L = 6B + C *)
  rewrite <- Hs' in Hg''.
  assert (Hn' : (6 + 3) * L = 9 * L). PusingR_f. rewrite Hn' in Hg''.  symmetry in Hg''.
  rewrite <- Unit_right with (A:= C) in Hg''. 
  (* Hg': 7M = 3B + 3C *)
  rewrite H3' in Hg'.
  assert (HM : (4 + 3) * M = 7 * M). PusingR_f. rewrite HM in Hg'.  symmetry in Hg'.
  (* Hg: 4N = B + C *)
  rewrite <- Hs' in Hg.
  assert (HN : (1 + 3) * N = 4 * N). PusingR_f. rewrite HN in Hg. symmetry in Hg.
 (* apply property13 with (P:= 7*M) (Q:= 4*N) in Hg'' .*)
  assert (HT : M = /7 * (3 * B + 3 * C)). rewrite Hg'. PusingR_f.
  assert (HT': N = /4 * (1 * B + C)). rewrite Hg. PusingR_f.
  assert (HT'': L = /9 * (6 * B + 1 * C)). rewrite Hg''. PusingR_f.
  rewrite HT,HT',HT''. unfold s. simpl. lra.
Qed.

Lemma Pappus_1': forall r1 r2 r3: R,
    r2 <> 0%R -> r3 <> 0%R -> r1 = (r1 * /r2 * r2* /r3 * r3)%R.
Proof.
  intros. apply Rinv_r in H, H0. rewrite Rmult_comm in H, H0.
  rewrite Rmult_assoc; rewrite H0; rewrite Rmult_1_r.
  rewrite Rmult_assoc; rewrite H; rewrite Rmult_1_r; auto.
Qed.

Lemma Pappus_1: forall r1 r2 r3: R,
    r2 <> 0%R -> r3 <> 0%R -> r1 = (r1 / r2 * r2 / r3 * r3)%R.
Proof.
  intros. unfold Rdiv. apply Pappus_1'; auto. Qed.

Lemma Pappus_div: forall r1 r2 r3: R,
    r2 <> 0%R -> r3 <> 0%R -> r1 = ((r1 / r2) * (r2 / r3) * r3)%R.
Proof.
  intros. assert (Hs: (r1 / r2 * r2 / r3 * r3)%R = ((r1 / r2) * (r2 / r3) * r3)%R). lra.
  rewrite <- Hs. unfold Rdiv. apply Pappus_1'; auto.
Qed.

Lemma Papus_2: forall C D E R' Q: Point,
    (s E C Q)%R  <> 0%R -> (s E C D)%R <> 0%R ->
    (s E R' Q)%R = (s E R' Q * /s E C Q * s E C Q * /s E C D * s E C D)%R.
Proof. intros. apply Pappus_1; auto. Qed.

 Axiom papus_3 : forall (A B C D: Point) (u v r s': R),
    u * A + v * B = r * C + s' * D -> (u * s A C D + v * s B C D)%R = 0%R.

 (*Definition Xcollin0 (A B C D F: Point) (u v r s: R) :=
   u + v = r + s /\
   (u + v) * F = u * A + v * B /\
   u<> 0%R /\
   F <> B /\
   u * A + v * B = r * C + s * D.
*)
Lemma commonEdg': forall (u v r s' : R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    (u * s A C D + v * s B C D)%R = 0%R.
Proof.
  unfold Xcollin0.  intros. induction H. induction H0. induction H1. induction H2.
  apply papus_3 in H3; auto.
Qed.

Lemma commonEdg'': forall (u v r s' : R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    (s A C D * /s B C D)%R = (-v */ u)%R.
Proof. intros.  apply commonEdg' in H. Abort.

Lemma Rinv_mult_r : forall u v r: R,
    (u * r)%R = v%R -> u <> 0%R -> r%R = (v * /u)%R.
Proof.
  intros. rewrite <- H. rewrite Rmult_comm.
  rewrite <- Rmult_assoc. apply Rinv_l in H0. rewrite H0. lra.
Qed.

Lemma Rinv_mult_l : forall u v r: R,
    (r * u)%R = v%R -> u <> 0%R -> r%R = (v * /u)%R.
Proof. intros. apply Rinv_mult_r;auto. rewrite Rmult_comm; auto. Qed.                                                                    
Lemma Rinv_mult_m' : forall u v r s: R,
    u <> 0%R -> s <> 0%R -> (u * r)%R = (v * s)%R -> (r * /s)%R = (v * /u)%R.
Proof.
  intros. apply Rinv_mult_r with (u := u) (r := r) (v := (v*s)%R)in H.
  symmetry in H1. rewrite H. assert (Hs : (v * s * / u * / s)%R = (v * / u * (s * / s))%R). lra.
  rewrite Hs. apply Rinv_r in H0. rewrite H0. lra. auto.
Qed.
(**************************** 08.14 *************************************)
(*Definition XCOLLIN A B C D F:=  forall u v r s':R , Xcollin0 A B C D F u v r s'.*)
(*******************************************************)

Lemma Rinv_mult_m : forall u v r s: R,
    (u * r)%R = (v * s)%R -> u <> 0%R -> s <> 0%R -> (r * /s)%R = (v * /u)%R.
Proof. intros. apply Rinv_mult_m'; auto. Qed.
  
Lemma Rinv_mult_0 : forall u r v s: R,
    (u * r + v * s)%R = 0%R ->
    u <> 0%R ->
    s <> 0%R -> 
    (r * /s)%R = (-(v * /u))%R .
Proof.
  intros. apply Rplus_eq_compat_r with (r := (- v * s)%R) in H.
  assert (Hs :(u * r + v * s + - v * s)%R = (u * r)%R). lra. rewrite Hs in H.
  rewrite Rplus_0_l in H. apply Rinv_mult_m in H. rewrite H. lra. auto. auto. 
Qed.

Lemma Rinv_abs_0 : forall u r v s: R,
    (u * r + v * s)%R = 0%R ->
    u <> 0%R ->
    s <> 0%R -> 
    Rabs (r * /s)%R = Rabs ((v * /u))%R .
Proof. intros. apply Rinv_mult_0 in H. rewrite H. rewrite Rabs_Ropp; auto. apply H0. apply H1. Qed.

Lemma sRabs : forall (u v: R) (A B C D: Point),
    (u * s A C D + v * s B C D)%R = 0%R ->
    u <> 0%R ->
    s B C D <> 0%R -> 
    (Rabs (s A C D) * / Rabs (s B C D))%R = Rabs (v * / u)%R.
Proof.
  intros. apply Rinv_abs_0 in H; auto.
  rewrite Rabs_mult with (x:= (s A C D)) (y := (/ (s B C D))%R) in H.
  apply Rabs_Rinv in H1. rewrite H1 in H. apply H.
Qed.

(*Axiom s_lt_0: forall A B C: Point,
    A <> B ->
    B <> C ->
    C <> D ->*)
    

       (*Rabs_Rinv: forall r : R, r <> 0%R -> Rabs (/ r) = (/ Rabs r)%R*)
       (*Rabs_mult: forall x y : R, Rabs (x * y) = (Rabs x * Rabs y)%R*)
       (*Rinv_l_sym: forall r : R, r <> 0%R -> 1%R = (/ r * r)%R*)
       (*Rinv_l: forall r : R, r <> 0%R -> (/ r * r)%R = 1%R*)
       (*Rinv_mult_distr: forall r1 r2 : R, r1 <> 0%R -> r2 <> 0%R -> (/ (r1 * r2))%R = (/ r1 * / r2)%R*)
(*Rabs_Rinv: forall r : R, r <> 0%R -> Rabs (/ r) = (/ Rabs r)%R*)

Axiom distance_eq : forall A B, distance A B = distance B A.

Lemma property4' : forall (u v: R) (A B F: Point),
    u * A + v * B = (u + v) * F ->
    u <> 0%R ->
    0 < Pnorm_sqr (F - B) ->
   (distance F A * /distance B F)%R = Rabs (v * /u)%R.
Proof. intros. apply property4_1 in H. apply property4_2. auto. auto. auto. Qed. 

Axiom Psquare_le : forall A : Point, 0%R <= Pnorm_sqr A.
(*Proof. intros. unfold Rle. unfold Psquare. unfold Pquantityprod.Abort.*)
       
Axiom Psquare_le_p: forall A B : Point, A <> B -> 0%R < (Pnorm_sqr (A - B))%R.

Lemma commonEdg'': forall (u v r s': R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    (distance F A */ distance B F)%R = Rabs (v * /u)%R.
Proof.
  intros. unfold Xcollin0 in H.
  induction H; induction H0; induction H1; induction H2.
  symmetry in H0. apply property4' in H0. apply H0.  
  apply H1. apply Psquare_le_p in H2. auto.
Qed.

Lemma commonEdg_0: forall (u v r s' : R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    s B C D <> 0%R ->
    (Rabs (s A C D) * / Rabs (s B C D))%R = (distance F A */ distance B F)%R.
Proof.
  intros. generalize H; intro H'. apply commonEdg' in H. apply sRabs in H.
  apply commonEdg'' in H'. rewrite H, H'; auto. unfold Xcollin0 in H'.
  induction H'; induction H2; induction H3; auto. auto.                            
Qed.

Lemma CommonEdg_0: forall A B C D F: Point,
    XCOLLIN A B C D F ->
    s B C D <> 0%R ->
    (Rabs (s A C D) * / Rabs (s B C D))%R = (distance F A */ distance B F)%R.
Proof.
  intros. unfold XCOLLIN in H. 
  eapply commonEdg_0. 2: apply H0. eauto. Unshelve. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
Qed.


Lemma commonEdg_0': forall (u v r s' : R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    s B C D <> 0%R ->
    (Rabs (s A C D) * / Rabs (s B C D))%R = (distance F A */ distance F B)%R.
Proof.
  intros. rewrite distance_eq with (A:= F) (B := B).
  apply commonEdg_0 with (u:=u) (v:=v) (r:=r) (s':=s');auto.
Qed.

Lemma CommonEdg_0': forall A B C D F: Point,
    XCOLLIN A B C D F ->
    s B C D <> 0%R ->
    (Rabs (s A C D) * / Rabs (s B C D))%R = (distance F A */ distance F B)%R.
Proof.
  intros. unfold XCOLLIN in H. 
  eapply commonEdg_0'. 2: apply H0. eauto. Unshelve. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
Qed.

Lemma commonEdg: forall (u v r s' : R)(A B C D F: Point),
    Xcollin0 A B C D F u v r s' ->
    s B C D <> 0%R ->
    (Rabs (s A C D) / Rabs (s B C D))%R = (distance F A / distance F B)%R.
Proof. intros. unfold Rdiv in *. apply commonEdg_0' with (u:=u) (v:=v) (r:=r) (s':=s'); auto. Qed.

Lemma CommonEdg: forall A B C D F: Point,
    XCOLLIN A B C D F ->
    s B C D <> 0%R ->
    (Rabs (s A C D) / Rabs (s B C D))%R = (distance F A / distance F B)%R.
Proof.
  intros. unfold XCOLLIN in H. 
  eapply commonEdg. 2: apply H0. eauto. Unshelve. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
Qed.

Lemma Rdiv_inver_l : forall a b c: R,
    (a/b)%R=c -> b <> 0%R -> a = (c * b)%R.
Proof.
  intros. unfold Rdiv in H.
  apply Rinv_mult_l in H. rewrite Rinv_involutive in H.
  apply H. apply H0. apply Rinv_neq_0_compat; auto.
Qed.

Lemma Rdiv_inver_f : forall a b c d : R,
    (a / b)%R = (c / d)%R -> b <> 0%R -> d <> 0%R -> (a * d)%R = (c * b)%R.
Proof.
  intros. apply Rdiv_inver_l with (b := b) (c := (c / d)%R) in H.
  unfold Rdiv in H. rewrite H.
  assert (Hs : (c * / d * b * d)%R = (c * b * (/ d * d))%R). lra.
  rewrite Hs. apply Rinv_l in H1. rewrite H1; lra. auto.
Qed.

Lemma Rdiv_inver_f_l : forall a b c d : R,
    (a * d)%R = (c * b)%R -> b <> 0%R -> d <> 0%R -> (a / b)%R = (c / d)%R.
Proof.
  intros. apply Rinv_mult_l in H.
  assert (Hs : (c * b * / d)%R = (c * / d * b)%R). lra. rewrite Hs in H.
  symmetry in H. apply Rinv_mult_l in H. symmetry in H. unfold Rdiv. auto.
  apply H0. apply H1. 
Qed. 

(*Rinv_involutive: forall r : R, r <> 0%R -> (/ / r)%R = r*)
(* Rinv_neq_0_compat: forall r : R, r <> 0%R -> (/ r)%R <> 0%R *)

Lemma Rinv_add: forall a b c d: R,
    (a/b)%R = (c/d)%R ->
    0%R < a ->
    0%R < b -> 
    0%R < c ->
    0%R < d ->         
    (a /(a + b))%R = (c/(c + d))%R.
Proof.
  intros. apply Rdiv_inver_f in H. apply Rdiv_inver_f_l.
  do 2 rewrite Rmult_plus_distr_l. rewrite H. rewrite <- H. lra.
  apply rgt. apply Rplus_lt_0_compat. apply H0.  apply H1.
  apply rgt. apply Rplus_lt_0_compat. apply H2. apply H3.
  apply rgt; auto. apply rgt; auto.
Qed.
  
(*
  Rplus_lt_compat: forall r1 r2 r3 r4 : R, r1 < r2 -> r3 < r4 -> r1 + r3 < r2 + r4
  Rplus_lt_0_compat: forall r1 r2 : R, 0 < r1 -> 0 < r2 -> 0 < r1 + r2
  rle: forall r : R, 0 < r -> r <> 0%R
 *)

Lemma Papus_3 : forall (A B C D E F Q R': Point) (u v r s' u1 v1 r1 s1: R),
    Xcollin0 R' C E Q E u v r s' -> (s C E Q)%R <> 0%R ->
    Xcollin0 Q D E C C u1 v1 r1 s1 -> (s D E C)%R <> 0%R ->
    Rabs (s R' E Q)%R = ((distance E R' / distance E C)%R *
                        (distance C Q / distance C D)%R *
                        Rabs (s D E C)%R)%R.
Proof.  
  intros.  apply commonEdg in H,H1.
  rewrite Pappus_div with (r1 := Rabs (s R' E Q)%R) (r2:= Rabs (s C E Q)%R) (r3:= Rabs (s D E C)%R).
  rewrite property11_abs with (A := Q) (B := E) (C := C) in H1. rewrite H, H1; auto.
  apply Rabs_no_R0 with (r:= (s C E Q)%R); auto.
  apply Rabs_no_R0 with (r:= (s D E C)%R); auto.
  auto. auto.
Qed.

Lemma Papus_4 : forall (A B C D E F Q R': Point) (u v r s' u1 v1 r1 s1: R),
    Xcollin0 R' C E Q E u v r s' -> (s C E Q)%R <> 0%R ->
    Xcollin0 Q D E C C u1 v1 r1 s1 -> (s D E C)%R <> 0%R ->
    distance E C = (distance E R' + distance C R')%R ->
    distance C D = (distance C Q + distance Q D)%R ->
    Rabs (s R' E Q)%R = ((distance E R' / (distance E R' + distance C R')%R)%R *
                        (distance C Q / (distance C Q + distance Q D)%R)%R *
                        Rabs (s D E C)%R)%R.
Proof.
  intros. rewrite <- H3. rewrite <- H4. 
  apply Papus_3 with (u:=u) (v:=v) (r:=r) (s':=s') (u1:=u1) (v1:=v1) (r1:=r1) (s1:=s1); auto.
Qed.

Lemma Pappus_REQ : forall (A B C D E F Q R': Point)
                  (u v r s' u1 v1 r1 s1 u2 v2 r2 s2 u3 v3 r3 s3 : R),
    Xcollin0 R' C E Q E u v r s' -> s C E Q <> 0%R ->
    Xcollin0 Q D E C C u1 v1 r1 s1 -> s D E C <> 0%R ->
    Xcollin0 E C B F R' u2 v2 r2 s2 -> s C B F <> 0%R ->
    Xcollin0 C D A F Q u3 v3 r3 s3 -> s D A F <> 0%R ->
    distance E C = (distance E R' + distance C R')%R ->
    distance C D = (distance C Q + distance Q D)%R ->
    0%R < Rabs (s E B F)%R ->
    0%R < Rabs (s C B F)%R ->
    0%R < Rabs (s C A F)%R ->
    0%R < Rabs (s D A F)%R ->
    0%R < distance E R' ->
    0%R < distance C R' ->
    0%R < distance C Q ->
    0%R < distance Q D ->
    Rabs (s R' E Q)%R  = 
      (((Rabs (s E B F)%R)/(Rabs (s E B F)%R + Rabs (s C B F)%R)) *
        ((Rabs (s C A F)%R)/(Rabs (s C A F)%R + Rabs (s D A F)%R)) *
         Rabs (s D E C))%R.
Proof. intros. apply Papus_4 with (R':=R') (u:=u) (v:=v) (r:=r) (s':=s') in H1; auto.
       apply commonEdg in H3;auto. apply commonEdg in H5; auto.
       rewrite distance_eq in H3.  rewrite distance_eq with (A:=R') (B:= C)in H3.
       rewrite distance_eq in H5. apply Rinv_add in H3; auto. apply Rinv_add in H5; auto.
       rewrite H1, H3, H5. reflexivity.
Qed.

Lemma PAPPUS_REQ : forall (A B C D E F Q R': Point),
    XCOLLIN R' C E Q E -> s C E Q <> 0%R ->
    XCOLLIN Q D E C C -> s D E C <> 0%R ->
    XCOLLIN E C B F R' -> s C B F <> 0%R ->
    XCOLLIN C D A F Q -> s D A F <> 0%R ->
    distance E C = (distance E R' + distance C R')%R ->
    distance C D = (distance C Q + distance Q D)%R ->
    0%R < Rabs (s E B F)%R ->
    0%R < Rabs (s C B F)%R ->
    0%R < Rabs (s C A F)%R ->
    0%R < Rabs (s D A F)%R ->
    0%R < distance E R' ->
    0%R < distance C R' ->
    0%R < distance C Q ->
    0%R < distance Q D ->
    Rabs (s R' E Q)%R  = 
      (((Rabs (s E B F)%R)/(Rabs (s E B F)%R + Rabs (s C B F)%R)) *
        ((Rabs (s C A F)%R)/(Rabs (s C A F)%R + Rabs (s D A F)%R)) *
         Rabs (s D E C))%R.
Proof.
  intros. eapply Pappus_REQ; auto. Unshelve. 
  exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
  exact 0%R. exact 0%R. exact 0%R; exact 0%R. exact 0%R. exact 0%R. 
  exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
Qed.

Lemma Papus_4' : forall (A B C D E F Q R': Point) (u5 v5 r5 s5 u6 v6 r6 s6: R),
    Xcollin0 Q F A R' A u5 v5 r5 s5 -> s F A R' <> 0%R ->
    Xcollin0 R' B A F F u6 v6 r6 s6 -> s B A F <> 0%R ->
    distance A F = (distance A Q + distance Q F)%R ->
    distance F B = (distance F R' + distance R' B)%R ->
    Rabs (s Q A R')%R = ((distance A Q / (distance A Q + distance Q F)%R)%R *
                        (distance F R' / (distance F R' + distance R' B)%R)%R *
                        Rabs (s B A F)%R)%R.
Proof. 
  intros.
  apply commonEdg in H,H1. rewrite <- H3. rewrite <- H4.
  rewrite Pappus_div with (r1 := Rabs (s Q A R')%R) (r2:= Rabs (s F A R')%R) (r3:= Rabs (s B A F)%R).
  rewrite property11_abs with (A := R') (B := A) (C := F) in H1. rewrite H, H1; auto. 
  apply Rabs_no_R0 with (r:= (s F A R')%R); auto.
  apply Rabs_no_R0 with (r:= (s B A F)%R); auto.
  auto. auto.
Qed.

Lemma Pappus_QAR: forall (A B C D E F Q R': Point)
                  (u5 v5 r5 s5 u6 v6 r6 s6 u7 v7 r7 s7 u8 v8 r8 s8 : R),
    Xcollin0 Q F A R' A u5 v5 r5 s5 -> s F A R' <> 0%R ->
    Xcollin0 R' B A F F u6 v6 r6 s6 -> s B A F <> 0%R ->
    Xcollin0 A F C D Q u7 v7 r7 s7 -> s F C D <> 0%R ->
    Xcollin0 F B C E R' u8 v8 r8 s8 -> s B C E <> 0%R ->
    distance A F = (distance A Q + distance Q F)%R ->
    distance F B = (distance F R' + distance R' B)%R ->
    0%R < Rabs (s F C E)%R ->
    0%R < Rabs (s B C E)%R ->
    0%R < Rabs (s A C D)%R ->
    0%R < Rabs (s F C D)%R ->
    0%R < distance F R' ->
    0%R < distance R' B ->
    0%R < distance A Q ->
    0%R < distance Q F ->
    Rabs (s Q A R')%R  =
      (((Rabs (s A C D)%R)/(Rabs (s A C D)%R + Rabs (s F C D)%R)) *
      ((Rabs (s F C E)%R)/(Rabs (s F C E)%R + Rabs (s B C E)%R)) *
        Rabs (s B A F))%R.
Proof.
  intros. apply Papus_4' with (Q:=Q) (u5:= u5) (v5:=v5) (r5:=r5) (s5:=s5) in H1; auto.
  apply commonEdg in H3;auto. apply commonEdg in H5; auto.
  rewrite distance_eq in H3.  (*rewrite distance_eq with (A:=R') (B:= C)in H3.*)
  rewrite distance_eq in H5. apply Rinv_add in H3; auto. apply Rinv_add in H5; auto.
  rewrite H1, H3, H5. reflexivity.
Qed.

Lemma PAPPUS_QAR: forall (A B C D E F Q R': Point),
    XCOLLIN Q F A R' A -> s F A R' <> 0%R ->
    XCOLLIN R' B A F F -> s B A F <> 0%R ->
    XCOLLIN A F C D Q -> s F C D <> 0%R ->
    XCOLLIN F B C E R' -> s B C E <> 0%R ->
    distance A F = (distance A Q + distance Q F)%R ->
    distance F B = (distance F R' + distance R' B)%R ->
    0%R < Rabs (s F C E)%R ->
    0%R < Rabs (s B C E)%R ->
    0%R < Rabs (s A C D)%R ->
    0%R < Rabs (s F C D)%R ->
    0%R < distance F R' ->
    0%R < distance R' B ->
    0%R < distance A Q ->
    0%R < distance Q F ->
    Rabs (s Q A R')%R  =
      (((Rabs (s A C D)%R)/(Rabs (s A C D)%R + Rabs (s F C D)%R)) *
      ((Rabs (s F C E)%R)/(Rabs (s F C E)%R + Rabs (s B C E)%R)) *
         Rabs (s B A F))%R.
Proof.
  intros. eapply Pappus_QAR; auto. Unshelve. 
  exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
  exact 0%R. exact 0%R. exact 0%R; exact 0%R. exact 0%R. exact 0%R. 
  exact 0%R. exact 0%R. exact 0%R. exact 0%R. exact 0%R.
Qed.

Lemma Pappus_omega : forall a1 a2 b1 b2 c d1 d2 e f1 f2: R,
    a1 = ((b1/c)%R * (d1/e)%R * f1)%R ->
    a2 = ((b2/e)%R * (d2/c)%R * f2)%R ->
    c <> 0%R ->
    e <> 0%R ->
    a2 <> 0%R->
    d2 <> 0%R ->
    f2 <> 0%R ->
    b2 <> 0%R ->
    (a1/a2)%R = ((f1/d2)%R*(d1/f2)%R*(b1/b2)%R)%R.
Proof.
  intros. unfold Rdiv in *. rewrite H, H0. 
  rewrite Rinv_mult_distr; auto. rewrite Rinv_mult_distr; auto.
  rewrite Rinv_mult_distr; auto. rewrite Rinv_mult_distr; auto.
  rewrite Rinv_involutive; auto. rewrite Rinv_involutive; auto.
  assert (Hs : (b1 * / c * (d1 * / e) * f1 * (/ b2 * e * (/ d2 * c) * / f2))%R=
  (b1 * (c * / c) * (d1 * (e */ e)) * f1 * / b2 * (/ d2 * / f2))%R). lra.
  rewrite Hs. apply Rinv_r in H1, H2. rewrite H1, H2. lra. 
  apply Rinv_neq_0_compat in H1; auto.
  apply Rinv_neq_0_compat in H2; auto.
  apply Rmult_integral_contrapositive_currified; auto.
  apply Rinv_neq_0_compat in H2; auto.
  apply Rmult_integral_contrapositive_currified; auto.
  apply Rinv_neq_0_compat in H1; auto.
  do 2 apply Rmult_integral_contrapositive_currified; auto.
  apply Rinv_neq_0_compat in H2; auto.
  apply Rinv_neq_0_compat in H1; auto.
Qed.

Theorem Pappus: forall (A B C D E F P Q R': Point) (u v r s' u1 v1 r1 s1 u2 v2 r2 s2 u3 v3 r3 s3 u5 v5 r5 s5 u6 v6 r6 s6 u7 v7 r7 s7 u8 v8 r8 s8 u9 v9 r9 s9 u0 v0 r0 s0 u10 v10 r10 s10 u11 v11 r11 s11 u12 v12 r12 s12 t1 t2: R),
    Xcollin0 R' C E Q E u v r s' -> s C E Q <> 0%R ->
    Xcollin0 Q D E C C u1 v1 r1 s1 -> s D E C <> 0%R ->
    Xcollin0 E C B F R' u2 v2 r2 s2 -> s C B F <> 0%R ->
    Xcollin0 C D A F Q u3 v3 r3 s3 -> s D A F <> 0%R ->
    distance E C = (distance E R' + distance C R')%R ->
    distance C D = (distance C Q + distance Q D)%R ->
    Xcollin0 Q F A R' A u5 v5 r5 s5 -> s F A R' <> 0%R ->
    Xcollin0 R' B A F F u6 v6 r6 s6 -> s B A F <> 0%R ->
    Xcollin0 A F C D Q u7 v7 r7 s7 -> s F C D <> 0%R ->
    Xcollin0 F B C E R' u8 v8 r8 s8 -> s B C E <> 0%R ->
    Xcollin0 F D E B E u9 v9 r9 s9 -> s F C D <> 0%R ->
    Xcollin0 E A B D P u0 v0 r0 s0 -> s B C E <> 0%R ->
    distance A F = (distance A Q + distance Q F)%R ->
    distance F B = (distance F R' + distance R' B)%R ->
    0%R < Rabs (s E B F)%R ->
    0%R < Rabs (s C B F)%R ->
    0%R < Rabs (s C A F)%R ->
    0%R < Rabs (s D A F)%R ->
    0%R < distance E R' ->
    0%R < distance C R' ->
    0%R < distance C Q ->
    0%R < distance Q D ->
    0%R < Rabs (s F C E)%R ->
    0%R < Rabs (s B C E)%R ->
    0%R < Rabs (s A C D)%R ->
    0%R < Rabs (s F C D)%R ->
    0%R < distance F R' ->
    0%R < distance R' B ->
    0%R < distance A Q ->
    0%R < distance Q F ->
    (Rabs (s E B F) + Rabs (s C B F))%R = t1 ->
    (Rabs (s F C E) + Rabs (s B C E))%R = t1 ->
    (Rabs (s C A F) + Rabs (s D A F))%R = t2 ->
    (Rabs (s A C D) + Rabs (s F C D))%R = t2 ->
    t1 <> 0%R ->
    t2 <> 0%R ->
    Rabs (s Q A R') <> 0%R ->
    Rabs (s F C E) <> 0%R ->
    Rabs (s A C D) <> 0%R ->
    Rabs (s B A F) <> 0%R ->
    Xcollin0 C B A D A u10 v10 r10 s10 -> s B A D <> 0%R ->
    Xcollin0 D F E C E u11 v11 r11 s11 -> s F C E <> 0%R ->
    Xcollin0 C B A F A u12 v12 r12 s12 -> s B A F <> 0%R ->
    s D E B <> 0%R ->
    distance E F <> 0%R ->
    distance A C <> 0%R ->
    distance A B <> 0%R ->
    distance E D <> 0%R ->
    (/ Rabs (s D E B))%R <> 0%R ->
    (/ Rabs (s B A D))%R <> 0%R ->
    distance A B <> 0%R ->
    (/ distance A B)%R <> 0%R ->
    (distance A C * / distance A B)%R <> 0%R ->
    Rabs (s B A D) <> 0%R ->
    Rabs (s B A D) <> 0%R ->
    Rabs (s D E B) <> 0%R ->
    s A B D <> 0%R -> 
    s F E C <> 0%R ->
    ((Rabs (s R' E Q)%R)/(Rabs (s Q A R')%R))%R = ((distance P E) / (distance P A))%R.
Proof.
  intros. apply Pappus_REQ with (A:=A) (B:=B) (C:=C) (D:=D) (E:=E) (F:=F) (Q:=Q) (R':= R')
  (u:=u) (v:=v) (r:=r) (s':=s') (u1:=u1) (v1:=v1) (r1:=r1) (s1:=s1) (u2:=u2) (v2:=v2) (r2:=r2)
  (s2:=s2) (u3:=u3) (v3:=v3) (r3:=r3) (s3:=s3) in H; auto.
  apply Pappus_QAR with (A:=A) (B:=B)(C:=C) (D:=D) (E:=E) (F:=F) (Q:=Q) (R':= R')
  (u5:=u5) (v5:=v5) (r5:=r5) (s5:=s5) (u6:=u6) (v6:=v6) (r6:=r6) (s6:=s6) (u7:=u7) (v7:=v7) (r7:=r7)
  (s7:=s7) (u8:=u8) (v8:=v8) (r8:=r8) (s8:=s8) in H9; auto.
  assert (Hs: ((Rabs (s R' E Q)%R)/(Rabs (s Q A R')%R))%R =
                (((Rabs (s D E C)%R)/(Rabs (s F C E)%R))%R *
                ((Rabs (s C A F)%R)/(Rabs (s B A F)%R))%R *
                   ((Rabs (s E B F)%R)/(Rabs (s A C D)%R))%R)%R).
  rewrite H39, H41 in H. rewrite H40, H42 in H9. apply Pappus_omega with (c:=t1) (e:=t2); auto.
  apply commonEdg in H17,H49; auto. rewrite property11_1 in H17. rewrite property11_abs' in H49.
  unfold Rdiv in H17, H49. apply  Rinv_mult_l in H17, H49; auto. apply commonEdg in H51, H53; auto.
  rewrite property11_abs'' with (A:=F)in H51. rewrite H51, H53 in Hs.
  apply commonEdg in H19.
  rewrite H17, H49 in Hs. unfold Rdiv in Hs.
  rewrite Rinv_involutive in Hs.
  rewrite Rinv_involutive in Hs. rewrite Rinv_mult_distr in Hs; auto.
  rewrite Rinv_mult_distr in Hs; auto.   rewrite Rinv_involutive in Hs.
  assert (Hs' : (distance E D * / distance E F * (distance A C * / distance A B) *
        (distance E F * / distance E D * Rabs (s D E B) *
           (/ distance A C * distance A B * / Rabs (s B A D))))%R =
                  
         ( (distance E F * / distance E F) * (distance A C * / distance A C) * (distance A B * / distance A B) * (distance E D *
         / distance E D) * (Rabs (s D E B) * / Rabs (s B A D)))%R). 
lra.   rewrite Hs' in Hs. apply Rinv_r in H56, H57, H58, H59. rewrite H56, H57, H58, H59 in  Hs.
 unfold Rdiv. rewrite Hs.  unfold Rdiv in H19. rewrite <- H19. rewrite property11_1. rewrite property11_abs' with (A:=B).
lra.    auto.  auto. auto.  auto.
Qed.

Theorem PAPPUS: forall (A B C D E F P Q R': Point) (t1 t2:R),
    XCOLLIN R' C E Q E -> s C E Q <> 0%R ->
    XCOLLIN Q D E C C -> s D E C <> 0%R ->
    XCOLLIN E C B F R' -> s C B F <> 0%R ->
    XCOLLIN C D A F Q -> s D A F <> 0%R ->
    distance E C = (distance E R' + distance C R')%R ->
    distance C D = (distance C Q + distance Q D)%R ->
    XCOLLIN Q F A R' A -> s F A R' <> 0%R ->
    XCOLLIN R' B A F F -> s B A F <> 0%R ->
    XCOLLIN A F C D Q -> s F C D <> 0%R ->
    XCOLLIN F B C E R' -> s B C E <> 0%R ->
    XCOLLIN F D E B E -> s F C D <> 0%R ->
    XCOLLIN E A B D P  -> s B C E <> 0%R ->
    distance A F = (distance A Q + distance Q F)%R ->
    distance F B = (distance F R' + distance R' B)%R ->
    0%R < Rabs (s E B F)%R ->
    0%R < Rabs (s C B F)%R ->
    0%R < Rabs (s C A F)%R ->
    0%R < Rabs (s D A F)%R ->
    0%R < distance E R' ->
    0%R < distance C R' ->
    0%R < distance C Q ->
    0%R < distance Q D ->
    0%R < Rabs (s F C E)%R ->
    0%R < Rabs (s B C E)%R ->
    0%R < Rabs (s A C D)%R ->
    0%R < Rabs (s F C D)%R ->
    0%R < distance F R' ->
    0%R < distance R' B ->
    0%R < distance A Q ->
    0%R < distance Q F ->
    (Rabs (s E B F) + Rabs (s C B F))%R = t1 ->
    (Rabs (s F C E) + Rabs (s B C E))%R = t1 ->
    (Rabs (s C A F) + Rabs (s D A F))%R = t2 ->
    (Rabs (s A C D) + Rabs (s F C D))%R = t2 ->
    t1 <> 0%R ->
    t2 <> 0%R ->
    Rabs (s Q A R') <> 0%R ->
    Rabs (s F C E) <> 0%R ->
    Rabs (s A C D) <> 0%R ->
    Rabs (s B A F) <> 0%R ->
    XCOLLIN C B A D A -> s B A D <> 0%R ->
    XCOLLIN D F E C E -> s F C E <> 0%R ->
    XCOLLIN C B A F A -> s B A F <> 0%R ->
    s D E B <> 0%R ->
    distance E F <> 0%R ->
    distance A C <> 0%R ->
    distance A B <> 0%R ->
    distance E D <> 0%R ->
    (/ Rabs (s D E B))%R <> 0%R ->
    (/ Rabs (s B A D))%R <> 0%R ->
    distance A B <> 0%R ->
    (/ distance A B)%R <> 0%R ->
    (distance A C * / distance A B)%R <> 0%R ->
    Rabs (s B A D) <> 0%R ->
    Rabs (s B A D) <> 0%R ->
    Rabs (s D E B) <> 0%R ->
    s A B D <> 0%R -> 
    s F E C <> 0%R ->
    ((Rabs (s R' E Q)%R)/(Rabs (s Q A R')%R))%R = ((distance P E) / (distance P A))%R.
Proof.
  intros. apply PAPPUS_REQ with (A:=A) (B:=B) (C:=C) (D:=D) (E:=E) (F:=F) (Q:=Q) (R':= R') in H; auto.
  apply PAPPUS_QAR with (A:=A) (B:=B)(C:=C) (D:=D) (E:=E) (F:=F) (Q:=Q) (R':= R') in H9; auto.
  assert (Hs: ((Rabs (s R' E Q)%R)/(Rabs (s Q A R')%R))%R =
                (((Rabs (s D E C)%R)/(Rabs (s F C E)%R))%R *
                ((Rabs (s C A F)%R)/(Rabs (s B A F)%R))%R *
                   ((Rabs (s E B F)%R)/(Rabs (s A C D)%R))%R)%R).
  rewrite H39, H41 in H. rewrite H40, H42 in H9. apply Pappus_omega with (c:=t1) (e:=t2); auto.
  apply CommonEdg in H17,H49; auto. rewrite property11_1 in H17. rewrite property11_abs' in H49.
  unfold Rdiv in H17, H49. apply  Rinv_mult_l in H17, H49; auto. apply CommonEdg in H51, H53; auto.
  rewrite property11_abs'' with (A:=F)in H51. rewrite H51, H53 in Hs.
  apply CommonEdg in H19.
  rewrite H17, H49 in Hs. unfold Rdiv in Hs.
  rewrite Rinv_involutive in Hs.
  rewrite Rinv_involutive in Hs. rewrite Rinv_mult_distr in Hs; auto.
  rewrite Rinv_mult_distr in Hs; auto.   rewrite Rinv_involutive in Hs.
  assert (Hs' : (distance E D * / distance E F * (distance A C * / distance A B) *
        (distance E F * / distance E D * Rabs (s D E B) *
           (/ distance A C * distance A B * / Rabs (s B A D))))%R =
                  
         ( (distance E F * / distance E F) * (distance A C * / distance A C) * (distance A B * / distance A B) * (distance E D *
         / distance E D) * (Rabs (s D E B) * / Rabs (s B A D)))%R). 
lra.   rewrite Hs' in Hs. apply Rinv_r in H56, H57, H58, H59. rewrite H56, H57, H58, H59 in  Hs.
 unfold Rdiv. rewrite Hs.  unfold Rdiv in H19. rewrite <- H19. rewrite property11_1. rewrite property11_abs' with (A:=B).
lra.    auto.  auto. auto.  auto.
Qed.

(*
Theorem Pappus : forall (A B C D E F P Q R' : Point) (u : R),
    P = O ->
    E = u * A ->
    collin A B C ->
    collin D E F ->
    Xcollin A E B P P ->
    Xcollin A F C D Q ->
    Xcollin C E B F R' ->
    s E R' Q / s A R' Q = u.  
 *)

(*************         Chapter 5 Complex and Point        ********************)

Require Export Complex.

Definition CPmult (z: C) (p: Point) : Point:=
R_R_to_Point (Cre z * Px p - Cim z * Py p) (Cre z * Py p + Cim z * Px p).

Theorem def6: forall (A: Point) (x y: R),
    A = (x, y) -> CPmult Ci A = ((-y)%R, x).
Proof.
  intros. unfold CPmult, Ci. apply Peq in H.
  apply Peq. induction H. split; simpl in *; lra.
Qed.

Lemma property14: forall A: Point, CPmult Ci (CPmult Ci A) = - A.
Proof. intros.  unfold CPmult, Ci. PusingR_f. Qed.

Lemma property15: forall A: Point, (CPmult Ci A) · A = 0%R.
Proof. intros; unfold CPmult, Ci, Pquantityprod; simpl; lra. Qed.

Lemma progress16: forall A B,
    (CPmult Ci A) · B = (-A) · (CPmult Ci B). 
Proof. intros. unfold CPmult, Ci, Pquantityprod; simpl; lra. Qed.

Require Export Cexp.

Print Cexp. 

Definition PRotateO (zeta: R) (A: Point):= CPmult (Cexp (0 +i zeta)) A.
 
Lemma property17 : forall (zeta: R) (A : Point) (x y : R),
    A = (x, y) ->
    PRotateO zeta A = ( (cos zeta * x - sin zeta * y)%R, (cos zeta * y + sin zeta * x)%R)%Point.
Proof.
  intros. unfold PRotateO. rewrite H.
  rewrite Cexp_trigo_compat. unfold CPmult.
  simpl. reflexivity.
Qed.

Definition PRotateB (zeta: R) (A A' B: Point) := A' = B + CPmult (Cexp (0 +i zeta)) (A - B).         

Lemma property19': forall alpha beta A, CPmult (alpha + beta) A = CPmult alpha A + CPmult beta A.   
Proof. intros. unfold CPmult. PusingR_f. Qed.

Lemma property19'' : forall (alpha: C) (A B: Point),
    CPmult alpha (A + B) = CPmult alpha A + CPmult alpha B.
Proof. intros. unfold CPmult. PusingR_f. Qed.

Lemma property19''' : forall (alpha beta: C) (A: Point),
 CPmult alpha (CPmult beta A) = CPmult (alpha * beta) A.
Proof. intros. unfold CPmult. PusingR_f. Qed.

Lemma property19_minus: forall alpha beta A, CPmult (alpha - beta) A = CPmult alpha A - CPmult beta A.   
Proof. intros. unfold CPmult. PusingR_f. Qed.


(*
Lemma property14
Definition i (P: Point) :=
  match P with
  | (x, y) => (-y, x)
  end.

Lemma property14: forall A, i (i A) = - A.
Proof. intros. unfold i. induction A. Plra. Qed.

Lemma property15: forall A, i A · A = 0.
Proof. intros.  unfold Pquantityprod, i. induction A. lra. Qed.

Lemma property16: forall A B,
    i A · B = - A · i B.
Proof. intros. unfold Pquantityprod, i, Pneg. induction A, B. lra. Qed.
 *)

Definition triangle0 (A B C: Point) (alpha beta: R) :=
  C - A = CPmult ((sin alpha)/(sin (alpha + beta))) (CPmult (Cexp (0 +i alpha)) (B - A)).

Axiom sin_cexp: forall a b :R, (sin a)/sin (a + b) =  ((Cexp (0 +i -a)) * (((1 - Cexp (0 +i -2*b)))/(1 - Cexp (0 +i -2*(a+b))))).

Axiom cexp_sol: forall a b, (Cexp (0 +i - a)  * b * Cexp (0 +i a)) = b.

Lemma ASA : forall (A B C: Point) (a b r: R),
    triangle0 A B C a b ->
    C = (A + CPmult ((1 - Cexp (0 +i -2*b))/(1 - Cexp (0 +i -2*(a+b)))) (B-A)%Point)%Point.
Proof.
  intros. unfold triangle0 in H. apply moveterm_3 in H. 
  rewrite H. rewrite sin_cexp. rewrite property19'''.  rewrite cexp_sol. PusingR_f.
Qed.
(*
Axiom ASA : forall (A B C: Point) (a b r: R),
    triangle0 A B C a b -> C =
                            A + CPmult ((1 - Cexp (0 +i -2*b))/(1 - Cexp (0 +i -2*(a+b)))) (B-A)%Point.

*)


Lemma INC_2 : INC 2%nat = 2%R. simpl. CusingR. Qed.

Lemma INC_3 : INC 3%nat = 3%R. simpl. CusingR; lra. Qed.

Lemma Cexp_mult_2 : forall a b : C, Cexp (2 * a) = (Cexp a) ^ 2. 
Proof. intros. rewrite <- INC_2. rewrite Cexp_mult. auto. Qed.

Lemma Cexp_mult_3 : forall a b : C, Cexp (3 * a) = (Cexp a) ^ 3. 
Proof. intros. rewrite <- INC_3. rewrite Cexp_mult. auto. Qed.

Lemma Cexp_PI : Cexp (3 * (0 +i (PI/3))%C) = (Cexp (0 +i (PI/3)%R)%C) ^ 3.
Proof. rewrite <- INC_3. rewrite Cexp_mult. auto. Qed.

Lemma Cexp_PI3 : Cexp (2 * (0 +i (PI/3))%C) = (Cexp (0 +i (PI/3)%R)%C) ^ 2.
Proof. rewrite <- INC_2. rewrite Cexp_mult. auto. Qed.  
  
  (*
Lemma Cexp_mult' : forall a n, Cexp (INC n * a) = (Cexp a) ^ n.
Proof. 
intros a n ; induction n.
simpl. Print Cmult_0_l.  rewrite Cmult_0_l. apply Cexp_0.
rewrite S_INC.  rewrite Cpow_S.  rewrite Cmult_add_distr_r. 
 Cmult_1_l, Cexp_add, IHn ; ring. 
Qed.
 *) 

Lemma Exp_PI' :  Cexp (0 +i -4 * PI / 3) = Cexp (0 +i (2 * PI/3)%R). (*Cexp (0 +i (PI - PI / 3)).*)
Proof.
  intros.
  assert (Hr : 0 +i (2 * PI/3)%R = (0 +i (PI - PI / 3))). CusingR_f. rewrite Hr.
  do 2 rewrite Cexp_trigo_compat. 
  assert (Hs : (-4 * PI / 3)%R = (-(PI + (PI/3)%R))%R). unfold Rdiv. lra.
  rewrite Hs. rewrite <- cos_sym. rewrite sin_antisym with (x:= ( (PI + PI/ 3))%R).
  rewrite Rtrigo_facts.cos_pi_plus.
  rewrite Rtrigo_facts.cos_pi_minus.
  rewrite Rtrigo_facts.sin_pi_plus.
  rewrite Rtrigo_facts.sin_pi_minus.
  CusingR_f.  
Qed.

Lemma Exp_PI :  Cexp (0 +i -4 * PI / 3) = Cexp (2 * (0 +i (PI/3)%R)).
Proof.
  intros. assert (Hs : 2 * (0 +i (PI/3)%R) = 0 +i (2 * PI/3)%R ). CusingR_f.
  rewrite Hs. rewrite Exp_PI'; auto.
Qed.

Lemma CPmultdiv : forall (c : C) (P : Point),
    c <> 0 -> CPmult (1/c) (CPmult c P) = P.
Proof.
  intros. rewrite property19'''. unfold Cdiv. apply Cinv_l in H.
  rewrite Cmult_1_l. rewrite H. unfold CPmult. PusingR_f.
Qed.

Lemma CPmultdiv_d': forall (p q: C) (A B: Point),
    A = CPmult (p/q) B -> p/q <> 0 -> B = CPmult (1/(p/q)) A.
Proof. intros. rewrite H. rewrite CPmultdiv; auto. Qed.

Lemma Cdiver: forall p q : C, p <> 0 -> q <> 0 -> 1/(p/q) = q/p.
Proof. 
  intros. unfold Cdiv. rewrite Cinv_mult_distr; auto.
  rewrite Cinv_involutive; auto. rewrite Cmult_1_l. rewrite Cmult_comm; auto.
  apply Cinv_neq_0_compat; auto.
Qed.

Lemma CPmultdiv_d: forall (p q: C) (A B: Point),
     A = CPmult (p/q) B -> p<> 0 -> q <> 0 -> B = CPmult (q/p) A.
Proof.
  intros. rewrite <- Cdiver; auto. apply CPmultdiv_d'.
  unfold Cdiv. apply H. apply Cmult_integral_contrapositive_currified; auto.
  apply Cinv_neq_0_compat; auto.
Qed.

Lemma CPmult_sub1: forall (P1 P2: Point) (c1: C),
    P1 = CPmult c1 P2 -> (P1 - P2)%Point = CPmult (c1 - 1) P2.
Proof.
  intros. rewrite H. unfold CPmult. PusingR_f.
Qed.

Lemma CPmult_mult : forall (a b: C) (Q B C: Point),
    Q = CPmult a C ->
    C = CPmult b B ->
    Q = CPmult (a*b) B.
Proof.
  intros. rewrite H, H0. unfold CPmult. PusingR_f.
Qed.

Lemma Cmult_frac : forall a b c d : C,
    b <> 0 -> d <> 0 -> (a/b) * (c/d) = (a*c) / (b*d).
Proof.
  intros. unfold Cdiv. rewrite Cinv_mult_distr; auto. do 2 rewrite <- Cmult_assoc. 
  apply Cmult_eq_compat_r. do 2 rewrite Cmult_assoc. apply Cmult_eq_compat_l.
  apply Cmult_comm.
Qed.

Lemma CPmult_mult_frac : forall (a b c d: C) (A B C: Point),
    A = CPmult (a/b) C ->
    C = CPmult (c/d) B ->
    b <> 0 ->
    d <> 0 ->
    A = CPmult ((a*c)/(b*d)) B.
Proof.
  intros.
  rewrite <- Cmult_frac; auto.
  apply CPmult_mult with (Q:=A) (B:=B) (C:=C); auto.
Qed.

Lemma Cexp_w3 : (Cexp (0 +i (PI/3)))^3 = (-1)%C.
Proof.
  rewrite <- Cexp_PI. 
  assert (Hs : (3 * (0 +i PI / 3))= 0 +i PI ). CusingR_f. rewrite Hs. 
  rewrite Cexp_trigo_compat. rewrite sin_PI, cos_PI; CusingR_f.
Qed.

Lemma Cexp_w2 : (Cexp (0 +i (PI/3)))^2 = (Cexp (0 +i (PI/3))) -1.
Proof.
  rewrite <- Cexp_PI3. Search cos. Print cos_2PI3.
  assert (Hs : 2 * (0 +i PI / 3) = (0 +i (2 * (PI / 3)))). CusingR_f. rewrite Hs.
  do 2 rewrite Cexp_trigo_compat. rewrite cos_2PI3, sin_2PI3, cos_PI3, sin_PI3. CusingR_f.
Qed.  

Lemma Cfrac_ab : forall a b: C,
    a<>0 -> b/a -1 = (b-a)/a.
Proof.
  intros. apply Cinv_r in H. rewrite <- H. unfold Cdiv.
  rewrite Cmult_minus_distr_r. reflexivity.
Qed.

Lemma Cmult_frac1 : forall a b c: C,
    a * (c/b) = (a * c)/b.
Proof. intros. unfold Cdiv. rewrite Cmult_assoc. reflexivity. Qed.

Lemma Cmult_fraca : forall a b c: C,
    a<>0 -> c <> 0 -> b/c = (a*b)/(a*c).
Proof.
  intros. unfold Cdiv. Search Cinv. rewrite Cinv_mult_distr; auto. rewrite <- Cmult_assoc.
  apply Cmult_eq_compat_r. rewrite Cmult_comm. rewrite <- Cmult_assoc. apply Cinv_l in H. rewrite H.
  CusingR_f.
Qed.

Lemma Cmult_fraca' : forall a b: C,
    a <> 0 -> b = (b*a)/a.
Proof. intros. unfold Cdiv. rewrite Cmult_assoc. apply Cinv_r in H. rewrite H. CusingR_f. Qed.

Axiom Cmult_frac_eq : forall a b c: C,
    b <> 0 -> a + c/b = (a*b +c)/b.


Lemma Cmult_fraca_r : forall a b c: C,
    a<>0 -> c <> 0 -> b/c = (b*a)/(c*a).
Proof.
  intros. rewrite Cmult_comm. rewrite Cmult_comm with (z1:=c). apply Cmult_fraca; auto.
Qed.

Lemma Cfrac_minus : forall a b c: C,
    a/c - b/c = (a-b)/c.
Proof. intros. unfold Cdiv. rewrite Cmult_minus_distr_r; reflexivity. Qed.

Lemma Cfrac_add : forall a b c: C,
    a/c + b/c = (a+b)/c.
Proof. intros. unfold Cdiv. rewrite Cmult_add_distr_r; reflexivity. Qed.
  
Lemma CPmult_P : forall P: Point, P = CPmult 1 P.
Proof. intros. unfold CPmult. PusingR_f. Qed.

Lemma Mor_H3 : forall (c : C) (B: Point),
    B + CPmult c B = CPmult (1+c) B.
Proof. intros. unfold CPmult. PusingR_f. Qed.

Lemma Ccons_eq : forall (c1 c2 : C) (P : Point),
    c1 = c2 -> CPmult c1 P = CPmult c2 P.
Proof. intros. rewrite H; reflexivity. Qed.

Lemma Cfrac_eq: forall a b c: C,
    a = b -> a/c = b/c.
Proof. intros. rewrite H; auto. Qed.  
(*
Theorem Morley : forall (A B C' P Q R': Point) (a b r: R) (w u v: C),
    A = O ->
    triangle0 A B C' (3*a)%R (3*b)%R ->
    triangle0 A B R' a b ->
    triangle0 A Q C' a (PI-a-r)%R ->
    triangle0 B C' P b r ->
    w = Cexp (0 +i (PI/3)%R) ->
    u = Cexp (0 +i (-2*a)%R) ->
    v = Cexp (0 +i (-2*b)%R)->
    r = (PI/3 - a - b)%R ->
    1 - w ^ 2 * v <> 0 ->
    1 - w ^ 2 * u * v <> 0 ->
    1 - w ^ 2 * v <> 0 ->
    1 - (u * v) ^ 3 <> 0 ->
    (w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v)) <> 0 ->
    1 - w ^ 2 * v <> 0 ->
    (w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v)) <> 0 ->
    w ^ 2 * u - 1 <> 0->
    (1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) <> 0 ->
     (1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v) <> 0 ->
     (1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) <> 0 ->
     1 - u * v <> 0 ->
     v <> 0 ->
    (w ^ 2 * u - 1) * (1 - (u * v) ^ 3) <> 0 ->
    w ^ 2 * u * v - v <> 0 ->
    1 - (u * v) ^ 3 <> 0 ->
    Cexp (2 * (0 +i PI / 3) + (0 +i -2 * a) + (0 +i -2 * b)) <> 0 ->
 1 - Cexp (0 +i -2 * (b + (PI / 3 - a - b))) <> 0 ->
1 - (u * v) ^ 3 <> 0 ->

 C' = CPmult ((1 - v ^ 3) / (1 - (u * v) ^ 3)) B ->

 1 - w ^ 2 * v <> 0 ->
 1 - (u * v) ^ 3 <> 0 ->

    ((CPmult w Q) - R')%Point = CPmult (w^2) P.
Proof.  
  intros. 
  (* H1: R = (1-v)/(1-uv) B *) 
  apply ASA in H0, H1, H2, H3; auto.  Oelim. 
  assert (Hab : (0 +i -2 * (a + b))= (0 +i -2*a) + (0 +i -2*b)). CusingR_f. 
  rewrite Hab in H1. rewrite Cexp_add in H1. rewrite <- H5, <- H6 in H1.
  (* H0 : C = (1-u3)/(1-u3v3) B *)
  assert (H3b : (0 +i -2 * (3 * b)) = 3 * (0 +i (-2*b)%R)). CusingR_f.  
  rewrite H3b in H0.   rewrite Cexp_mult_3 in H0.  rewrite <- H6 in H0. 2: auto.
  assert (H3ab : 0 +i -2*(3 * a + 3 * b) = 3*((0 +i (-2*a)%R) + (0 +i (-2*b)%R))). CusingR_f.
  rewrite H3ab in H0. rewrite Cexp_mult_3 in H0. 2: auto.
  rewrite Cexp_add in H0. rewrite <- H5, <- H6 in H0.
  (* H2 : C = (1-w2v)/(1-w2uv)Q *)
  (*up*)
  rewrite H7 in H2. 
  assert (Hpib : (-2 * (PI - a - (PI/3 - a - b)))%R = (-4 * PI/3 + (-2*b))%R). lra.
  rewrite Hpib in H2.
  assert (Hipib : (0 +i -4 * PI / 3 + -2 * b) =(0 +i -4 * PI / 3) + (0 +i (-2*b)%R) ). CusingR_f.
  rewrite Hipib in H2. rewrite Cexp_add in H2. rewrite <- H6 in H2.
  rewrite Exp_PI, Cexp_mult_2, <- H4 in H2. 2: auto.
  (*down*)
  assert (Habr : (0 +i -2 * (a + (PI - a - (PI / 3 - a - b)))) =
                   (0 +i -4 * PI / 3) + (0 +i (-2*a)%R) + (0 +i (-2*b)%R)). CusingR_f.
  rewrite Habr in H2. do 2 rewrite Cexp_add in H2.
  rewrite Exp_PI, Cexp_mult_2, <- H4, <- H5, <- H6 in H2. 2: auto.
  (***alge***)
   generalize H0; intro Hs. apply CPmult_sub1 in Hs.
   (* wQ-R=()B *)
   (* · Q = ()B *)
   apply CPmultdiv_d in H2; auto.
   apply CPmult_mult_frac with
     (A:=Q) (C:= C') (B:=B)
     (a:=(1 - w ^ 2 * u * v)%C) (b:=(1 - w ^ 2 * v)%C)
     (c:=(1 - v ^ 3)%C) (d:=(1 - (u * v) ^ 3)%C) in H2.
   (* · C-B = ()B *)
   rewrite Cfrac_ab in Hs.
   assert (Huv : (1 - v ^ 3 - (1 - (u * v) ^ 3)) = ((v ^ 3) * ((u^3) -1))).
   CusingR_f. rewrite Huv in Hs.
   (* wQ-R *)
   rewrite H2. rewrite property19'''.
   assert (Hwq : w * ((1 - w ^ 2 * u * v) * (1 - v ^ 3)) = (w - w^3 * u * v ) * (1 - v ^ 3)).
   CusingR_f.
   assert (Hw3 : (w - w ^ 3 * u * v) = w + u * v).
   rewrite H4. rewrite Cexp_w3. rewrite <- H4. CusingR_f.
   rewrite Hw3 in Hwq.
   rewrite Cmult_frac1, Hwq. rewrite H1.
   rewrite <- property19_minus.
   (* w^2P = ()B*) 
   rewrite H7 in H3.
   (*assert (Hrp : (0 +i -2 * (PI / 3 - a - b)) =
                   (-2*(0 +i (PI/3))) + (-(0 +i -2 * a)) + (-(0 +i -2 * b))).
   CusingR_f. rewrite Hrp in H3. do 2 rewrite Cexp_add in H3.*)
   rewrite Cmult_fraca with (a:= Cexp (2* (0 +i PI / 3) + ((0 +i -2 * a)) + ((0 +i -2 * b)))) in H3.
   do 2 rewrite Cmult_minus_distr_l with (z1:= Cexp (2 * (0 +i PI / 3) + (0 +i -2 * a) + (0 +i -2 * b))) in H3. rewrite Cmult_1_r in H3.
   do 2 rewrite <- Cexp_add in H3.
   assert (Hpab : (2 * (0 +i PI / 3) + (0 +i -2 * a) + (0 +i -2 * b) + (0 +i -2 * (PI / 3 - a - b))) = 0). CusingR_f. rewrite Hpab in H3.
   assert (Hpab2 : (2 * (0 +i PI / 3) + (0 +i -2 * a) + (0 +i -2 * b) + (0 +i -2 * (b + (PI / 3 - a - b)))) = (0 +i -2 * b)). CusingR_f.
   rewrite Hpab2 in H3. do 2 rewrite Cexp_add in H3.
   rewrite  Cexp_PI3 in H3. rewrite <- H4, <- H5, <- H6 in H3.
   Search Cexp. rewrite Cexp_0 in H3.
   (* · sub C-B *)
   rewrite Hs in H3. rewrite property19''' in H3.
   rewrite Cmult_frac in H3.
   rewrite Mor_H3 in H3.
   assert (Hv3 : (w ^ 2 * u * v - 1) * (v ^ 3 * (u ^ 3 - 1))
                 = v * ((v ^ 2) * (w ^ 2 * u * v - 1) *  (u ^ 3 - 1))).
   CusingR_f. rewrite Hv3 in H3. 
   assert (Hv : ((w ^ 2 * u * v - v) * (1 - (u * v) ^ 3)) = v * ((w ^ 2 * u - 1) * (1 - (u * v) ^ 3))).
   CusingR_f. rewrite Hv in H3.
   rewrite <- Cmult_fraca in H3; auto.
   rewrite H3.
   rewrite property19'''. rewrite Cmult_add_distr_l. rewrite Cmult_1_r.
   assert (HW3 : w^3=-1). rewrite H4.
   apply Cexp_w3. rewrite Cmult_frac1 with (a := w ^ 2).
   assert (Hw2 : w ^ 2 * (v ^ 2 * (w ^ 2 * u * v - 1) * (u ^ 3 - 1))
                 = w * v ^ 2 * (w ^ 3 * u * v - w) * (u ^ 3 - 1)).
   CusingR_f. rewrite Hw2, HW3.
   assert (Hsym : w * v ^ 2 * (-1 * u * v - w) * (u ^ 3 - 1) = w * v ^ 2 * (u * v + w) * (1 - u ^ 3)).
   CusingR_f. rewrite Hsym.
   (* turn to Equal_C *)
   apply Ccons_eq.
   assert (Huv3 : (1 - (u * v) ^ 3) = (1+u*v+u^2*v^2)*(1-u*v)).
   CusingR_f. rewrite Huv3.
   rewrite Cmult_fraca with (a:=((1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2)))
                            (b:=(1 - v)) (c:=(1 - u * v)).
   assert (Hg : ((1 - w ^ 2 * v) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v))) =
                  ((1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v))).
   CusingR_f. rewrite Hg.
   rewrite Cfrac_minus with (a:=(w+u*v)*(1-v^3))
                            (b:=(1-w^2*v)*(1+u*v+u^2*v^2)*(1-v))
                            (c:=((1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v))).
   rewrite Cmult_fraca_r with (a:= (w ^ 2 * u - 1)).
   assert (Heq2 : w^2+w*v^2*(u*v+w)*(1-u^3)/((w^2*u-1)*((1+u*v+u^2*v^2)*(1-u*v)))=
                    (w^2*(w^2*u-1)*((1+u*v+u^2*v^2)*(1-u*v))+w*v^2*(u*v+w)*(1-u^3))/((w^2*u-1)*((1+u*v+u^2*v^2)*(1-u*v)))).
   rewrite Cmult_frac_eq.
   assert (Hequal : (w ^ 2 * ((w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v))) +
   w * v ^ 2 * (u * v + w) * (1 - u ^ 3)) = (w ^ 2 * (w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v)) +
                                                   w * v ^ 2 * (u * v + w) * (1 - u ^ 3))). CusingR_f.
   rewrite Hequal; auto. auto. rewrite Heq2.
   rewrite Cmult_fraca_r with (a:= (1 - w ^ 2 * v))
   (b:= (w ^ 2 * (w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v)) +
              w * v ^ 2 * (u * v + w) * (1 - u ^ 3))).
   assert (Hfe : ((1 - w ^ 2 * v) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v) * (w ^ 2 * u - 1)) =
                   ((w ^ 2 * u - 1) * ((1 + u * v + u ^ 2 * v ^ 2) * (1 - u * v)) * (1 - w ^ 2 * v))).
   CusingR_f. rewrite Hfe.
   apply  Cfrac_eq.
   assert (Hw32 : w ^ 2 * (w ^ 2 * u - 1) = w * (w^3 * u - w)). CusingR_f.
   rewrite HW3 in Hw32. assert (Hw33 : w * (-1 * u - w) = -w * (u + w)). CusingR_f.
   rewrite Hw33 in Hw32. rewrite Hw32. rewrite <- Huv3.
   (*compute*)
   (*1*)
   rewrite Cmult_minus_distr_r.
   assert (Hq1 : (w + u * v) * (1 - v ^ 3) * (w ^ 2 * u - 1)=
           w ^ 3 * u - w ^ 3 * v ^ 3 * u - (w - w * v ^ 3) +
  (u * v * 1 * (w ^ 2 * u) - u * v * v ^ 3 * (w ^ 2 * u) - (u * v * 1 - u * v * v ^ 3)) ).
   do 2 rewrite Cmult_add_distr_r. do 3 rewrite Cmult_minus_distr_l. do 3 rewrite Cmult_1_r.
   rewrite Cmult_minus_distr_r.
   rewrite Cmult_minus_distr_l.
   rewrite Cmult_minus_distr_r.
   assert (Hq2 : w * (w ^ 2 * u) = w^3 * u). CusingR_f. rewrite Hq2. 
   assert (Hq3 : w * v^3 * (w ^ 2 * u) = w^3 * v^3 * u). CusingR_f. rewrite Hq3.
   reflexivity.   rewrite Hq1.
   assert (HW2 : w^2 = w -1). rewrite H4. apply Cexp_w2.
   rewrite HW3, HW2.
   assert (Hq4 : (1 - (w - 1) * v) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - v) * ((w - 1) * u - 1) = ((1 - (w - 1) * v) * ((w - 1) * u - 1)) * (1 + u * v + u ^ 2 * v ^ 2) * (1 - v)). CusingR_f.
   assert (Hq5 : ((1 - (w - 1) * v) * ((w - 1) * u - 1)) = w * u - u - 1 - (w ^ 2 * v * u - w * v * u - w * v - w * u * v + v * u + v)). CusingR_f.
   rewrite Hq4, Hq5. rewrite HW2.
   (*2*)
   rewrite Cmult_add_distr_r.
   assert (Hq6 : - w * (u + w) * (1 - (u * v) ^ 3) * (1 - (w - 1) * v) =
             (-w * (u + w) * (1 - (w - 1) * v)) * (1 - (u * v) ^ 3)). CusingR_f.
   assert (Hq7 : -w * (u + w) * (1 - (w - 1) * v) =
                   -w * u - (w * u * v- w^2 * u * v) + (- (w^2*v- w^3*v)- w^2)).
   CusingR_f. rewrite Hq6, Hq7. rewrite HW2,HW3.
   assert (HQ8 : w * v ^ 2 * (u * v + w) * (1 - u ^ 3) * (1 - (w - 1) * v) =
                   (w * v ^ 2 * (u * v + w) * (1 - (w - 1) * v)) * (1 - u ^ 3)).

   CusingR_f.
   assert (HQ9 : w * v ^ 2 * (u * v + w) * (1 - (w - 1) * v) =
          w * v ^ 2 * u * v - (w^2 * v^4 * u - w * v ^ 2 * (u * v) * v) +
                    (w^2 * v ^ 2  - (w^3 * v^2 * v - w^2 * v^2 * v))). CusingR_f.
   rewrite HQ8, HQ9. rewrite HW3,HW2.
   CusingR_f. auto. auto. auto. auto. auto. auto. auto.  auto. auto.
   auto.   auto.
   auto.  auto. auto.
Qed.  

   
   
  
  
   
   
*)   
   
     
   
   
   
  
  
  
  
  
  
  
  
  
  
  

 

  
  
  
  
  
   
   
  
  


  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  
  

  
  
  
                                                                

  
  
  
  
   
  
  
    
    
    
    
  
    

      
  

