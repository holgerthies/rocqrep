From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
From HB Require Import structures.
From mathcomp Require Import reals all_ssreflect all_boot all_order ssrnum ssralg ssrnum mathcomp_extra matrix tvs.
From mathcomp Require Import Rstruct.
From mathcomp Require Import interval.
From mathcomp Require Import reals topology.
From mathcomp Require Import topology normed_module.
From mathcomp Require Import all_boot all_order all_algebra ssralg ssrnum boolp classical_sets functions filter reals Rstruct interval.
From mathcomp Require Import archimedean mathcomp_extra unstable pseudometric_normed_Zmodule normed_module.
Import numFieldNormedType.Exports.
From mathcomp Require Import interval_inference.
From RocqRep Require Import core.representation extra.tpmn.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Import numFieldNormedType.Exports.
Local Open Scope ring_scope.


Lemma tpmn_bound (eps : R) : 0 < eps -> exists n, 2 ^- n < eps. 
Proof.
move => eps_gt0.
have [n +] := Rarchimedean_axiom eps.
rewrite ger0_norm ?ltW// => -h.
exists n.
apply /lt_trans.
(* apply/Rle_lt_trans/h1. *)
(* apply Rinv_le_contravar; first by apply lt_0_INR. *)
(* rewrite pow_IZR. *)
(* rewrite INR_IZR_INZ. *)
(* apply IZR_le. *)
(* clear h1 h2. *)
(* have -> : Zpos (xO xH) = Z.of_nat 2 by []. *)
(* rewrite -Znat.Nat2Z.inj_pow. *)
(* apply Znat.inj_le. *)
(* suff <- : (expn 2 n = Nat.pow 2 n)%coq_nat by apply /ssrnat.leP/ltnW/ltn_expl. *)
(* elim n => // n0 Ih. *)
(* rewrite expnS Ih /= Nat.add_0_r. *)
(* by rewrite mul2n -addnn. *)
Admitted.

Lemma tpmnP n m: reflect (2 ^- n <= (2 : R) ^- m) (m <= n)%nat.
Proof.
 case E: (m <= n)%nat.
 - apply/ReflectT.
      rewrite ler_pV2 ?inE ?unitfE ?exprn_gt0 ?expf_neq0 ?lt0r_neq0 ?ltr0n ?RealsE//.
admit.
    apply/ReflectF.
Admitted.

Local Open Scope classical_set_scope.

(* HB.mixin Record RNormedModChosenBasis X of NormedModule R X := { *)
(*   basis_type : countType; *)
(*   basis_set : basis_type -> set X; *)
(*   basis_spec : *)
(*     forall x n, *)
(*       exists b, basis_set b x /\ basis_set b `<=` ball x (2 ^- n); *)
(* }. *)

(* #[short(type="repNormedModType")] *)
(* HB.structure Definition RepNormedMod := *)
(*   { T of NormedModule R T &  isRepNormedMod T }. *)
Section RepNorm.
Context {X : normedModType R}.
Context (basis_type : countType) (basis_set : basis_type -> set X).
Hypothesis basis_spec :
    forall x n,
      exists b, basis_set b x /\ basis_set b `<=` ball x (2 ^- n).

(* HB.builders Context X of RNormedModChosenBasis X. *)
Definition repX := fun (name : nat -> basis_type) (x : X) => (forall n, (basis_set (name n) x)) /\ (forall n, exists N, forall k, (N <= k)%nat -> basis_set (name k) `<=` ball x (2^-n)).

Lemma tpmn_ball (x : X) n m: (m<=n)%nat -> (ball x (2 ^- n) `<=` (ball x (2^-m))).
Proof.
move => h.
apply le_ball.
by apply /tpmnP.
Qed.

Lemma repX_surjective : repX \is_surjective.
Proof.
move => x.
have /choice [f p]:= (basis_spec x).
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
apply cond_eq => e /RltP eg0.
rewrite Rminus_0_r RabsE normr_id.
apply /RltP.
have [n ineq]:= tpmn_bound e eg0.
suff h : ball x (2 ^- n) y.
  apply /lt_trans/ineq.
  move  : h.
  by rewrite -ball_normE/ball_/=.
have [N1 P1] := s1 n.
have [N2 P2] := s2 n.
by apply : (subset_trans (P1 N1 _)).
Qed.

(* HB.instance Definition normedSpace_isRepSpace (X : normedModType R) B Bs H := *)
(*   isRepSpace.Build X (repX_surjective _ _ H) (repX_singlevalued B Bs). *)
End RepNorm.

HB.mixin Record hasRepBasis X of NormedModule R X := {
  basis_type : countType;
  basis_set : basis_type -> set X;
  basis_spec :
    forall x n,
      exists b, basis_set b x /\ basis_set b `<=` ball x (2 ^- n)
}.

HB.builders Context X of hasRepBasis X.
HB.instance Definition normedSpace_isRepSpace  :=
  isRepSpace.Build X (repX_surjective _ _ basis_spec) (repX_singlevalued _ _).
HB.end.

#[short(type="repBasisNormedModType")]
HB.structure Definition repBasisNormedMod :=
  { X of NormedModule R X & hasRepBasis X }.

HB.mixin Record isRepNormedMod X
  of NormedModule R X & hasRepBasis X & isRepSpace X := {
    add_rlzr : (@queries X) -> @answers X -> @answers X -> @answers X;
    add_nameP : forall (px py : names X) x y, px |= x -> py |= y -> (fun n => add_rlzr n (px n) (py n)) |= x+y

}.

#[short(type="repNormedModType")]
HB.structure Definition repNormedMod :=
  { X of NormedModule R X & hasRepBasis X & isRepNormedMod X }.

Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import Bignums.BigQ.BigQ Bignums.BigZ.BigZ.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
From HB Require Import structures.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Module SFBI2 := SpecificFloat BigIntRadix2.    
From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
Import Interval.Real.Xreal.
Import GRing.Theory Num.Theory.
Import BigN BigZ.
Import GRing.Theory.
Locate archi_boundP.
Check Num.Theory.archi_boundP.
Open Scope R_scope.
From mathcomp Require Import classical_sets.

From RocqRep Require Import extra.interval_counttype extra.interval_string extra.tpmn interval_extensions.
Definition R : realType := R.

Definition I_set (i : I) : set R := [set x | Interval.contains i (Xreal x)].

Lemma IR_basis_spec : forall x n, exists (i : I),  I_set i x /\ I_set i `<=` ball x (2 ^-n).
Proof.
have p2lt n : 0 < 2 ^ n by apply (pow_lt 2 n);lra.
suff : forall x n, exists (i : I),  I_set i x /\ I_set i `<=` closed_ball x (2 ^-n).
  move=>h x n.
  have [i [p1 p2]] := h x n.+1.
  exists i;split=>//.
  apply: (subset_trans p2).
  apply: closed_ball_subset => //.
  by rewrite ltr_pV2 ?ltr_eXn2l ?inE ?unitfE ?expf_neq0 ?lt0r_neg0  ?ltr1n ?RealsE//=.
move => x n.
have {}p2lt := p2lt n.
exists (FI.bnd 
	(Float (BigZ.BigZ.of_Z (Int_part (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))
	(Float (BigZ.BigZ.of_Z (up (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))).
rewrite /I_set /= !D2R_SFBI2toX !D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos /= .
have [bi1 bi2]:= base_Int_part (x * 2^n).
have arc:= archimed (x * 2 ^ n).
split; first by split;apply (Rmult_le_reg_r (2 ^ n)); rewrite ?Rmult_assoc ?Rinv_l;lra.
move=>/=x0 [h1 h2].
have -> : (2 ^- n)%R = / (2 ^ n) by rewrite !RealsE.
Search (0 < / _).
rewrite closed_ballE/closed_ball_/= ?ler_distlC; last by apply/RltP;apply Rinv_0_lt_compat.
apply /andP;split.
  apply /RleP/Rle_trans/h1.
  apply (Rmult_le_reg_r (2 ^ n)) => //.
  by rewrite Rmult_assoc  Rmult_minus_distr_r Rinv_l; lra .
apply /RleP/(Rle_trans _ _ _ h2).
apply (Rmult_le_reg_r (2 ^ n)) => //.
by rewrite Rmult_assoc  Rmult_plus_distr_r Rinv_l; lra .
Qed.


HB.instance Definition real_hasRepBasis :=
  hasRepBasis.Build R _ _ IR_basis_spec.


Definition addIR_rlzr (n : nat) := FI.add (nat2p n).

Lemma addIR_rlzr_spec : forall (px py : names R) x y, px |= x -> py |= y -> (fun n => addIR_rlzr n (px n) (py n)) |= x+y.
Admitted.

HB.instance Definition real_isRepNormedMod :=
  isRepNormedMod.Build R _ addIR_rlzr_spec.
Lemma zeroIR_nameP :  (fun n=> (FI.zero : @answers R))|= (0 : R).
Proof.
split => n /=; rewrite /I_set/=; first by lra.
exists 0%nat => k _.
move => /= x x0.
suff ->: x = 0 by apply ballxx.
by lra.
Qed.

Lemma floatIR_nameP m e :  ((fun n=> FI.singleton (Float m e)) : names R) |= IZR (to_Z m) * powerRZ 2 (to_Z e).
Proof.
split => n; rewrite /= /I_set/=.  
  by rewrite D2R_SFBI2toX D2R_Float; lra.
exists 0%nat => k _.
rewrite D2R_SFBI2toX D2R_Float.
move => /= x xp.
suff -> : x =  IZR (to_Z m) * powerRZ 2 (to_Z e) by apply ballxx.
by lra.
Qed.

Definition float_to_real (m e : Z) (n : nat) := FI.singleton (Float (of_Z m) (of_Z e)).

Lemma float_to_real_spec m  e : float_to_real m e |= IZR m * powerRZ 2 e.
Proof.
rewrite /float_to_real -{2}(spec_of_Z m) -{2}(spec_of_Z e).
by apply floatIR_nameP.
Qed.
