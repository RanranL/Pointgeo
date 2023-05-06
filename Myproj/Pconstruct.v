Require Export Coq.micromega.Lra.
Require Import Lemma.
Require Import PF.
Require Export Pbasics.



(** the definition of Midpoint *)

Definition Midpoint (C A B : Point) :=
  Pplus A B = Pmults 2 C.


Definition MidpointE (C A B: Point) :=
  2 * C - A - B = 0.

Definition MidpointC (C A B: Point) :=
  C = (1/2) * (A + B).


(** Parallel *)
Definition Parall (A B C D : Point) : Prop := A + C = B + D.

Definition ParallM (A B C D:Point) : Prop := B - A = C - D.

(** line segment equality *)
Definition Lseg_eq (A B C D : Point) : Prop :=
  (A - B) · (A - B) = (C - D)·(C - D).

(** Perpendicular *)
Definition Perpendicular (A B C D : Point) : Prop := (A - B) · (C - D) = 0%R.

(** Point on line *)
Definition PonLine (C A B : Point) (t: R):= C = t*A + (1-t)%R * B.

(** median point of traingle *)
Definition Ptraingle_median (G A B C : Point) := 3 * G = A + B + C. 

(** pendant center of traingle *)
Definition Ptraingle_H (H A B C: Point) :=
  Perpendicular A H B C /\
  Perpendicular B H A C /\
    Perpendicular C H A B.

(** E of Parall *)
Definition ParallE E A B C D :=
  Parall A B C D -> Midpoint E A C /\ Midpoint E B D.

Definition Xcollin0 (A B C D F: Point) (u v r s: R) :=
   u + v = r + s /\
   (u + v) * F = u * A + v * B /\
   u<> 0%R /\
   F <> B /\
   u * A + v * B = r * C + s * D.

Definition XCOLLIN A B C D F:=  forall u v r s':R , Xcollin0 A B C D F u v r s'.


(* area *)
Definition Sarea A B C := s A B C.

Definition area A B C := Rabs(s A B C).

Definition SParea A B C D := s A B C + s B C D.

Definition Parea A B C D := Rabs(s A B C) + Rabs(s B C D).

(* more construct *)
Definition ParallD (t: R) (A B C D : Point) :=
  C - D = t * (A - B).

Definition Ptraingle_O O A B C :=
  (A-O)·(A-O) = (B-O)·(B-O) /\ (B-O)·(B-O) = (C-O)·(C-O).

Definition Ptraingle_OP P A B C :=
  (A-P)·(A-P) = (B-P)·(B-P) /\ (B-P)·(B-P) = (C-P)·(C-P).

Definition NinepointCircleO K A B C :=
  K = (1/2) * (A + B + C).



