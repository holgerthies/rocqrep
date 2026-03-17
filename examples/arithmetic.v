From Stdlib Require Import Reals.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
From RocqRep Require Import core.representation spaces.ireals.
Unset Printing Implicit Defensive.
Require Import QArith.
Require Import List.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.

Open Scope rep_scope.

Eval vm_compute in (approx_real (0.5) 10).

Fixpoint phin (n : nat)  : names R :=
  match n with
  | 0%nat => 1
  | n.+1  => 1 + / (phin n)
  end.

Notation "x `| n"  := (approx_real x n)
  (at level 2, left associativity).
Definition phi := phin 1000.
Eval vm_compute in (phi`|100).

 
