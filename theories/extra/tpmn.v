From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
Local Open Scope R_scope.

Lemma tpmn_bound eps : 0 < eps -> exists n, /2 ^ n < eps. 
Proof.
move => eps_gt0.
have [n [h1 h2]] := archimed_cor1 _ eps_gt0. 
exists n.
apply/Rle_lt_trans/h1.
apply Rinv_le_contravar; first by apply lt_0_INR.
rewrite pow_IZR.
rewrite INR_IZR_INZ.
apply IZR_le.
clear h1 h2.
have -> : Zpos (xO xH) = Z.of_nat 2 by [].
rewrite -Znat.Nat2Z.inj_pow.
apply Znat.inj_le.
suff <- : (expn 2 n = Nat.pow 2 n)%coq_nat by apply /ssrnat.leP/ltnW/ltn_expl.
elim n => // n0 Ih.
rewrite expnS Ih /= Nat.add_0_r.
by rewrite mul2n -addnn.
Qed.

Lemma tpmnP n m: reflect (/2^n <= /2^m) (m <= n)%nat.
Proof.
 case E: (m <= n)%nat.
 - apply/ReflectT/Rinv_le_contravar/Rle_pow/ssrnat.leP/E; try lra.
      by apply/pow_lt; lra.
    apply/ReflectF/Rlt_not_le/Rinv_lt_contravar/Rlt_pow/ssrnat.leP; try lra.
    - apply/Rmult_lt_0_compat; apply/pow_lt; try lra.
    by rewrite ltnNge E.
Qed.

Lemma powerRZ2_neg_pos n: powerRZ 2 (-Z.of_nat n) = /2^n.
Proof.
by rewrite powerRZ_neg; try lra; rewrite pow_powerRZ powerRZ_inv.
Qed.

