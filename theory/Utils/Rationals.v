Require Import POram.Utils.Classes.
Require Import Coq.QArith.QArith.

(*** RATIONALS ***)
#[export] Instance Monoid_rat : Monoid Q:= { null := 0 / 1 ; append := Qplus}.
