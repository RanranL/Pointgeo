From Coq Require Import Arith.Arith.
From Coq Require Import Reals.

Open Scope R_scope.

(** * The definition of point *)
Inductive Point : Type :=
| pair (n1 n2 : R) : Point.

Declare Scope Point_scope.
Delimit Scope Point_scope with Point.
Bind Scope Point_scope with Point.

Notation " ( x , y ) " := (pair x y):Point_scope.
Local Open Scope Point_scope.
Check (1, 2)%Point.
(* useless???????????????????? *)
Inductive Line :Type :=
  | line (n1 n2 : Point) : Line.
(* useless???????????????????? *)
Check pair 1 2.
Check line (1,2) (2,3).
Check (1, 2).

(**********************************************************)
(** * DEFINITION *)
(**********************************************************)

(** ** point_add *)
Definition Pplus (A B : Point) : Point :=
  match A, B with
  | (a, b), (c, d)
    => (a + c, b + d)
  end.

Compute Pplus (1, 2) (4, 6).

(** ** Pminus *)
Definition Vetor : Type := Point.

Definition Pminus (A B : Point) : Point :=
  match A, B with
  | (a, b), (c, d)
    => (a - c, b - d)
  end.

Compute Pminus (4, 6) (1, 2).
Definition Vec (A B: Point) := Pminus B A.  

(** ** Pmults *)
Definition Pmults (n : R) (A : Point) :=
  match A with
  | (x, y) => (n * x, n * y)
  end.

Compute Pmults 2 (1, 2).


Definition Pneg (P: Point): Point :=
  match P with
  | (a, b) => (-a, -b)
  end.

(** ** Pquantityprod *)
Definition Pquantityprod (A B : Point) : R :=
  match A, B with
  | (a, b), (c, d)
    => (a * c + b * d)%R
  end.
Check Pquantityprod (1,2) (3,4).
(** Pquantityprod (1, 2) (3, 4) : R *)

(** ** Pouterprod *)
Definition Pouterprod (A B : Point) : Vetor := Pminus B A.

(** ** Pequal **)
Definition Pequal (A B: Point) : Prop :=
  match A, B with
  |(a, b), (c, d) => a=c /\ b=d
  end.

(*******************************************************)
(*******************************************************)

Notation " x + y " := (Pplus x y)
                         (at level 50, left associativity) : Point_scope.

Notation " x * y " := (Pmults x y)
                        (at level 40, left associativity) : Point_scope.

Notation " x - y " := (Pminus x y)
                        (at level 50, left associativity) : Point_scope.

Notation " x · y " := (Pquantityprod x y)
                        (at level 50, left associativity) : Point_scope.

Notation " - x " := (Pneg x) : Point_scope.

Notation " x == y " := (Pequal x y)
                         (at level 51, left associativity) :Point_scope.
                       

Check Pplus.
Check 2 * (1,2).
Check (1, 2) + (4, 6).
Compute (1, 2) - (3, 7).
Check 2 * (5, 2).
Check (1, 2) · (3, 4).
Check -(1,2).
Check (1,2)==2*(3,4).

Open Scope Point_scope.
Check (1,2).


