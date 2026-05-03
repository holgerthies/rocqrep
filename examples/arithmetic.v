From Stdlib Require Import Reals.
From mathcomp Require Import reals rat ssrnum all_algebra Rstruct ssrZ.
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

From Interval Require Import Tactic.
Fixpoint test (x : R) (n : nat) :=
  match n with | 0%nat => x | n'.+1 => let y := (x*(1-x))%rocqR in ( test y n')%rocqR end.

Goal forall (x : R), (0.5<=x<=0.5)%rocqR -> True.
Proof.
intros x Hx.  
interval_intro (test x 15)%rocqR as H.
Abort.
Open Scope rep_scope.

Eval vm_compute in ((3.0 / 2 - 1) `| 10).

Fixpoint test' (x : names R) (n : nat) :=
  match n with | 0%nat => x | n'.+1 => let y := (x*(1-x))%rep in ( test' y n') end.
Eval vm_compute in ((test' 0.5 16) `| 10).
Fixpoint phin (n : nat)  : names R :=
  match n with
  | 0%nat => 1
  | n.+1  => 1 + / (phin n)
  end.
Definition phi := phin 1000.

Eval vm_compute in (phi`|10).
Local Notation Rc := (names R).

From RocqRep Require Import  extra.interval_extensions.
Definition inner x prec := (FI.mul (nat2p prec) x (FI.sub (nat2p prec) (1 prec)%rep x)).

Definition test1'' (x : names R) (n :nat) := test'' (x 10%nat) n.

Eval vm_compute in (interval_string.interval_to_cr_string (test1'' (0.5 : Q) 100 10) 10).
Definition M1  :=
  [::
  [:: 1; (0.2 : Rc); (3 : Rc)];
  [:: 1; (0.12 : Rc); (3 : Rc)];
  [:: 1; (0.5 : Rc); (1 : Rc)]].

Eval vm_compute in ((M1+0+M1-M1 *m M1) `|| 3).

Definition I2 : (names 'M[R]_2)  :=[::[:: 1; 0];
                                     [:: 0; 1]].
Eval vm_compute in (M1^T `|| 10).

Definition M2 : (names 'M[R]_2)  :=[::[:: 1; 1];
                                     [:: 1; 0]].

Fixpoint powM2  (M : names 'M[R]_2) (n : nat) := match n with
                    | 0%nat => I2
                    | n'.+1 => M *m (powM2 M n') 
                    end.


Eval vm_compute in ((powM2 M2 (n:=13%nat)) `|| 20).


Fixpoint power_method (A : (names 'M[R]_2)) (x : names 'M[R]_(2,1)) k :=
  match k with
    | 0%nat => x
    | k'.+1 => let y := (A *m x)%rep in
             power_method A y k' 
     end.

Definition rayleigh (A : (names 'M[R]_2)) (x : names 'M[R]_(2,1)) := (/ mx_entry (x^T *m x) 0%nat 0%nat) *: (x^T *m A *m x).

Definition v2 : (names 'M[R]_(2,1))  :=[::[:: 1] ; [:: 1]].

Definition eigenvec := (power_method M2 v2 8%nat).
Definition eigenval := rayleigh M2 eigenvec.
Eval vm_compute in (eigenvec `|| 20).

Eval vm_compute in (eigenval `|| 20).

Definition inv_diag {n m} (M : names 'M[R]_(n.+1,m.+1)) : names 'M[R]_(n.+1, m.+1) :=fun q =>  ( if q.2.1 =? q.2.2 then / mx_entry M q.2.1 q.2.2 else 0) q.1.

Definition approx_solution_step {m} (D_inv B : names 'M[R]_(m.+1, m.+1))  (b x0 : names 'M[R]_(m.+1, 1))  := D_inv *m (b - B *m x0).

Fixpoint approx_solution_rec {m} (D_inv B : names 'M[R]_(m.+1, m.+1))  (b x0 : names 'M[R]_(m.+1, 1)) steps :=
  match steps with
  | 0%nat => x0
  | k.+1 =>
      let x1 := approx_solution_step D_inv B b x0 in
      approx_solution_rec D_inv B b x1 k
  end.
                                                                                                                  
Definition approx_solution {m} (A : names 'M[R]_m.+1) b x0 n :=
  let D_inv := inv_diag A in
  let D := mx_diag A in
  let B := A - D in
  approx_solution_rec D_inv B b x0 n.


Definition A  :=
  [::
  [:: (4 : Rc); (0.2 : Rc); (0.1 : Rc)];
  [:: (0.1 : Rc); (5 : Rc); (0.2 : Rc)];
  [:: (0.2 : Rc); (0.1 : Rc); (6 : Rc)]].

Definition b : (names 'M[R]_(2,1))  :=[::[:: 4.3 : Rc] ; [:: 5.3 : Rc]; [:: 6.3 : Rc]].


Definition ex1 := (approx_solution A b 0 4). 
Eval vm_compute in (ex1 `|| 10).

