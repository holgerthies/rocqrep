From Stdlib Require Import Reals.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
From RocqRep Require Import core.representation core.matrix spaces.ireals.
Unset Printing Implicit Defensive.
Require Import QArith.
Require Import List.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.

Set Implicit Arguments.
Unset Strict Implicit.


Open Scope rep_scope.

Fixpoint phin (n : nat)  : names R :=
  match n with
  | 0%nat => 1
  | n.+1  => 1 + / (phin n)
  end.
Definition phi := phin 1000.

Eval vm_compute in (phi`|10).

Definition M1  :=
  [::
  [:: 1; (0.2 : names R); (3 : names R)];
  [:: 1; (0.12 : names R); (3 : names R)];
  [:: 1; (0.5 : names R); (3 : names R)]].

Eval vm_compute in ((M1+0+M1-M1 *m M1) `|| 3).


Definition I2 : (names 'M[R]_2)  :=[::[:: 1; 0];
                                     [:: 0; 1]].

Definition M2 : (names 'M[R]_2)  :=[::[:: 1; 1];
                                     [:: 1; 0]].

Fixpoint powM2  (M : names 'M[R]_2) (n : nat) := match n with
                    | 0%nat => I2
                    | n'.+1 => (powM2 M n') *m M
                    end.

Eval vm_compute in ((M2 *m M2 *m M2) `|| 3).
