From mathcomp Require Import all_ssreflect all_algebra.
Import GRing.Theory.
Local Open Scope ring_scope.
From HB Require Import structures.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Notation "d '\is_surjective'" :=
  (forall x, exists phi, d phi x)
  (at level 10).

Notation "d '\is_singlevalued'" :=
  (forall phi x y, d phi x -> d phi y -> x = y)
  (at level 10).

HB.mixin Record isRepSpace carrier := RepSpace {
  queries   : countType;
  answers  : countType;
  is_name   : (queries -> answers) (*names *) -> carrier -> Prop;
  rep_total :is_name \is_surjective;
  rep_singlevalued : is_name \is_singlevalued;
}.
#[short(type="repType")]
HB.structure Definition RepSpace := { T of isRepSpace T }.

Definition names (X : repType) := @queries X -> @answers X.
Notation "phi '|=' x" := (is_name phi x) (at level 70).

(* HB.mixin Record isRepZmod T of GRing.Zmodule T & isRepSpace T := { *)
(*   zero_rlzr : names T; *)
(*   add_rlzr : names T -> names T -> names T; *)
(*   opp_rlzr : names T -> names T; *)

(*   zero_nameP : is_name zero_rlzr 0; *)
(*   add_nameP : forall px py x y, *)
(*     px |= x ->  py |= y -> *)
(*     (add_rlzr px py) |= (x + y); *)
(*   opp_nameP : forall px x, *)
(*     px |= x -> *)
(*     (opp_rlzr px) |= (- x); *)
(* }. *)

(* #[short(type="repZmodType")] *)
(* HB.structure Definition RepZmod := *)
(*   { T of GRing.Zmodule T & isRepSpace T & isRepZmod T }. *)

(* HB.mixin Record isRepComRing T of GRing.ComRing T & RepZmod T := { *)
(*   one_rlzr : names T; *)
(*   mul_rlzr : names T -> names T -> names T; *)
(*   one_nameP : one_rlzr |= 1; *)
(*   mul_nameP : forall px py x y, *)
(*     px |= x -> py |= y -> *)
(*     (mul_rlzr px py) |= (x * y) *)
(* }. *)

(* #[short(type="repComRingType")] *)
(* HB.structure Definition RepComRing := *)
(*   { T of GRing.ComRing T & isRepComRing T }. *)

(* HB.mixin Record isRepField T of GRing.Field T & RepComRing T := { *)
(*   inv_rlzr : names T -> names T; *)
(*   inv_nameP : forall px x, *)
(*     x != 0 -> px |= x ->  *)
(*     (inv_rlzr px) |= GRing.inv x *)
(* }. *)

(* #[short(type="repFieldType")] *)
(* HB.structure Definition RepiIeld := *)
(*   { T of GRing.ComRing T &isRepField T }. *)
(* Declare Scope rep_scope. *)
(* Delimit Scope rep_scope with rep. *)
(* Notation "0" := (zero_rlzr) : rep_scope. *)
(* Notation "1" := (one_rlzr) : rep_scope. *)
(* Notation "- x" := (opp_rlzr x) : rep_scope. *)
(* Notation "x + y" := (add_rlzr x y) : rep_scope. *)
(* Notation "x - y" := (add_rlzr x (opp_rlzr y)) : rep_scope. *)
(* Notation "x * y" := (mul_rlzr x y) : rep_scope. *)
(* Notation "/ x" := (inv_rlzr x) : rep_scope. *)
(* Notation "x / y " := (mul_rlzr x (inv_rlzr y)) : rep_scope. *)

