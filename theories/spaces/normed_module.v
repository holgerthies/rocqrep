From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
From HB Require Import structures.
From mathcomp Require Import reals all_ssreflect all_boot all_order ssrnum ssralg ssrnum mathcomp_extra matrix.
From mathcomp Require Import Rstruct.
From mathcomp Require Import interval.
From mathcomp Require Import reals topology.
From mathcomp Require Import topology normed_module.
From mathcomp Require Import boolp classical_sets functions filter reals.
From mathcomp Require Import pseudometric_normed_Zmodule normed_module.
Import numFieldNormedType.Exports.

From RocqRep Require Import core.representation extra.tpmn.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.
Local Open Scope ring_scope.


Section normRep.
Local Open Scope classical_set_scope.
Open Scope R_scope.
Context  {X : normedModType R}.
Context {ball_type : countType} {ball_set : ball_type -> set X}.
Hypothesis ball_basis :
  forall x n, exists b, ball_set b x /\ ball_set b `<=` ball x (/2 ^ n).

Definition repX := fun (name : nat -> ball_type) (x : X) => (forall n, (ball_set (name n) x)) /\ (forall n, exists N, forall k, (N <= k)%nat -> ball_set (name k) `<=` ball x (/2 ^ n)).

Lemma tpmn_ball (x : X) n m: (m<=n)%nat -> (ball x (/2 ^ n) `<=` (ball x (/ 2^ m))).
Proof.
move => h.
apply le_ball.
by  apply /RleP/tpmnP;lia.
Qed.

Lemma repX_surjective : repX \is_surjective.
Proof.
move => x.
have /choice [f p]:= (ball_basis x).
exists f.
split=>n;first by apply p.
exists n => k nk.
apply: (subset_trans _ (tpmn_ball x _ _ nk)).
by apply p.
Qed.

Lemma repX_singlevalued : repX \is_singlevalued.
Proof.
move=>phi1 x y [c1 s1] [c2 s2].
apply /eqP.
rewrite -subr_eq0 -normr_eq0.
apply /eqP.
apply cond_eq => e eg0.
have [n ineq]:= tpmn_bound eg0.
rewrite Rminus_0_r RabsE normr_id.
suff h : ball x (/2 ^ n) y.
  apply /Rlt_trans/ineq/RltP.
  move  : h.
  by rewrite -ball_normE/ball_/=.
have [N1 P1] := s1 n.
have [N2 P2] := s2 n.
by apply : (subset_trans (P1 N1 _)).
Qed.


HB.instance Definition normedSpace_isRepSpace :=
  isRepSpace.Build X repX_surjective repX_singlevalued.

End normRep.

From mathcomp Require Import matrix_normedtype.
From RocqRep Require Import core.representation spaces.ireals.
Section Matrix_rep.
Context {m n : nat} {X : repType}.
Local Notation MX := 'M[X]_(m,n).
Local Notation Q := ((@queries X) * ('I_m * 'I_n))%type.
Local Notation A := (@answers X).
Definition repM := fun (name : Q -> A) (x : MX) => forall i j, (fun q => (name (q,(i,j)))) |= (x i j).

Lemma repM_surjective : repM \is_surjective.
Proof.
move => M.
rewrite /repM.
suff /choice [phi_ij P] : forall ij, exists phi, phi |= M ij.1 ij.2 by exists (fun q => phi_ij q.2 q.1) => i j /=;apply P.
move => [i j].
exact: rep_total.
Qed.

Lemma repM_singlevalued : repM \is_singlevalued.
Proof.
move => phi x y phix phiy.
apply /matrixP => i j.
by apply: (rep_singlevalued _ _ _ (phix i j)).
Qed.
