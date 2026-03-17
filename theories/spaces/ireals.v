Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import Bignums.BigQ.BigQ Bignums.BigZ.BigZ.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
From RocqRep Require Import core.representation extra.interval_counttype extra.interval_string extra.tpmn interval_extensions.
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
Locate archi_boundP.
Check Num.Theory.archi_boundP.
Open Scope R_scope.

Definition rep_IR := fun (name : nat -> I) (r : R) => (forall n, Interval.contains (name n) (Xreal r)) /\ (forall n, exists N, forall k, (N <= k)%nat -> FI.bounded (name k) /\ diam (name k) <= /2 ^ n).


Lemma rep_IR_surjective : rep_IR \is_surjective.
Proof.
move => x.
exists (fun n => FI.bnd 
	(Float (BigZ.BigZ.of_Z (Int_part (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))
	(Float (BigZ.BigZ.of_Z (up (x * (2 ^ n)))) (BigZ.BigZ.of_Z (-Z.of_nat n)))).
split => n/=.
	have bi:= base_Int_part (x * 2^n); have lt:= pow_lt 2 n; have arc:= archimed (x * 2 ^ n).
	rewrite !D2R_SFBI2toX;	split; rewrite D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos.
		by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
	by apply (Rmult_le_reg_r (2 ^ n)); try lra; rewrite Rmult_assoc Rinv_l; lra.
exists n.+1 => k ineq;  split => //.
have bi:= base_Int_part (x * 2^k); have ltn1:= pow_lt 2 n.+1; have arc:= archimed (x * 2 ^ k).
have ltk:= pow_lt 2 k; have ltn2:= pow_lt 2 n; have eq: 2 ^ k * /2 ^k = 1 by rewrite Rinv_r; lra.
have /=exp: /2 ^ k <= /2 ^ n.+1.
	apply Rinv_le_contravar; try lra.
	by apply Rle_pow; try lra; apply /ssrnat.leP.
rewrite  !D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos.
rewrite -Rcomplements.Rmult_minus_distr_r.
rewrite -[/2 ^ n]Rmult_1_l -(Rinv_r 2); try lra.
rewrite Rmult_assoc -Rinv_mult_distr; try lra.
apply Rmult_le_compat; try lra.
by apply /Rlt_le/Rinv_0_lt_compat; lra.
Qed.

Lemma rep_IR_singlevalued : rep_IR \is_singlevalued.
Proof.
move => In x x' [xeIn convIn] [x'eIn _].
apply cond_eq => e eg0.
have [n ineq]:= tpmn_bound eg0.
have [N prop]:= convIn n.
have ineq': (N <= N)%nat by trivial.
have [Ibnd dI]:= (prop N ineq').
move: xeIn (xeIn N) => _ xeIn.
move: x'eIn (x'eIn N) => _ x'eIn.
apply/Rle_lt_trans/ineq.
case: (In N) Ibnd dI xeIn x'eIn => // l u/=.
case: u; first by case: l.
by case: l => // um ue lm le; rewrite !D2R_SFBI2toX; split_Rabs; lra.
Qed.

HB.instance Definition real_isRepSpace :=
  isRepSpace.Build R rep_IR_surjective rep_IR_singlevalued.

Definition addIR_rlzr (x y : names R) (n : nat) := FI.add (nat2p n) (x n) (y n).

Lemma zeroIR_nameP :  (fun n=> FI.zero)|= 0.
Proof.
split => n /=; first by lra.
exists 0%nat => k _.
split=>//.
rewrite Rminus_diag.
apply Rlt_le.
apply Rinv_0_lt_compat.
by apply pow_lt;lra.
Qed.

Lemma floatIR_nameP m e :  (fun n=> FI.singleton (Float m e))|= IZR (to_Z m) * powerRZ 2 (to_Z e).
Proof.
split => n /=.  
  by rewrite D2R_SFBI2toX D2R_Float; lra.
exists 0%nat => k _.
split=>//.
rewrite Rminus_diag.
apply Rlt_le.
apply Rinv_0_lt_compat.
by apply pow_lt;lra.
Qed.

Definition float_to_real (m e : Z) (n : nat) := FI.singleton (Float (of_Z m) (of_Z e)).

Lemma float_to_real_spec m  e : float_to_real m e |= IZR m * powerRZ 2 e.
Proof.
rewrite /float_to_real -{2}(spec_of_Z m) -{2}(spec_of_Z e).
by apply floatIR_nameP.
Qed.

Eval vm_compute in (interval_to_cr_string (float_to_real 11 (-10) 3%nat) 6).


Definition oppIR_rlzr (x : names R) (n : nat) := FI.neg (x n).


Lemma name_bnd phi x : phi |= x -> exists N, forall n, (N <= n)%nat -> ibound (phi n) ((Rabs x)+1).
Proof.
move => [n1 n2].
case (n2 0%nat) => N kn.
exists N => n nk.
have [b1 +]:= kn _ nk.
rewrite Rinv_1 => -H.
split;apply Stdlib.Rabs_def1_le.
- apply : Rle_trans.
  apply (contains_bnd b1 (n1 n)).
  suff : x <= Rabs x by lra.
  apply Rle_abs.
- suff: - FI.upper (phi n) <= Rabs x by lra.
  apply /Rle_trans/Rcomplements.Rabs_maj2.
  apply Ropp_le_contravar.
  apply contains_bnd =>//.
- suff: FI.lower (phi n)  <= Rabs x by lra.
  apply /Rle_trans/Rle_abs.
  apply contains_bnd=>//.
- suff : - FI.upper (phi n) <= Rabs x by lra.
  apply /Rle_trans/Rcomplements.Rabs_maj2.
  apply Ropp_le_contravar.
  apply contains_bnd=>//.
Qed.

Lemma name_bnd2 phi1 x phi2 y : phi1 |= x -> phi2 |= y -> exists N, forall n, (N <= n)%nat -> ibound (phi1 n) ((Rmax (Rabs x) (Rabs y))+1) /\ ibound (phi2 n) ((Rmax (Rabs x) (Rabs y))+1).
Proof.
move => n1 n2.
have [N1 N1p] := name_bnd n1.
have [N2 N2p] := name_bnd n2.
exists (Nat.max N1 N2) => n nle.
rewrite !Rcomplements.Rplus_max_distr_r.
split.
by split;apply /Rle_trans/Rmax_l;apply N1p;lia.
by split;apply /Rle_trans/Rmax_r;apply N2p;lia.
Qed.

Lemma oppIR_is_rlzr phix x : phix |= x -> (oppIR_rlzr phix) |= (-x).
Proof.
move => [rlzr1 rlzr2].
split=>n /=; first by apply (FI.neg_correct (phix n) (Xreal x)).
have [N p] := rlzr2 n.
exists N => k Nk.
rewrite /oppIR_rlzr/=.
split.
  by have [pb _] := p _ Nk;apply neg_bounded.
have [+ +] := p _ Nk.
rewrite /FI.upper/FI.lower/FI.neg.
case (phix k) => //= l u /andP[r1 r2] h.
rewrite /FI.F.toR/=.
rewrite !FI.F'.neg_correct.
by rewrite !FI.F'.real_correct //=;lra.
Qed.

Definition addRI_rlzr (x y : names R)  (n : nat) := FI.add (nat2p n) (x n) (y n). 

Lemma addIR_is_rlzr phix phiy x y : phix |= x -> phiy |= y -> (addRI_rlzr phix phiy) |= (x+y).
Proof.
move => n1 n2. 
have [xr1 xr2] := n1.
have [yr1 yr2] := n2.
rewrite /addRI_rlzr.
split => /= n.
exact: FI.add_correct (nat2p n) (phix n) (phiy n) _ _ (xr1 n) (yr1 n).
have [N Np] := name_bnd2 n1 n2.
set M := (Rmax (Rabs x) (Rabs y) + 1).
have M0 : 0 <= M.
  rewrite /M.
  rewrite Rcomplements.Rplus_max_distr_r.
  apply /Rle_trans/Rmax_l.
  suff : 0 <= Rabs x by lra.
  by apply Rabs_pos.

suff [m mb] : exists m,   / 2 ^ m + / 2 ^ m + 8 * M *  /2 ^ m <= /2 ^ n.
  have [N1 N1p] := xr2 m.
  have [N2 N2p] := yr2 m.
  exists (Nat.max m (Nat.max N (Nat.max N1 N2))) => k kge.
  have [kbx1 kbx2] : (FI.bounded (phix k)) /\ diam (phix k) <= /2 ^ m  by apply N1p;lia.
  have [kby1 kby2] : (FI.bounded (phiy k)) /\ diam (phiy k) <= /2 ^ m  by apply N2p;lia.
  have Nk : (N <= k)%nat by lia.
  have [ib1 ib2] := Np _ Nk.
  have [add_bnd add_err] := add_error k kbx1 kby1 ib1 ib2.
  split => //.
  apply (Rle_trans _ (/ 2 ^ m + / 2 ^ m + 8 * M * / 2 ^ m )); last by apply mb;lia.
  apply (Rle_trans _ _ _ add_err).
  apply Rplus_le_compat.
  apply Rplus_le_compat => //.
  apply Rmult_le_compat_l.
  by apply Rmult_le_pos => //; lra.
  by apply /tpmnP;lia.

case : (@tpmn_bound (/ 2 ^ n / (2 + 8 * M))).
  apply Rmult_lt_0_compat; first by apply tpmn_lt.
  by apply Rinv_0_lt_compat;lra.
move => m mp.
exists m.
suff : / 2 ^ m * (2 + 8*M) < / 2 ^ n by lra.
by rewrite Rcomplements.Rlt_div_r;lra.
Qed.

HB.instance Definition real_isRepZmod :=
  isRepZmod.Build R zeroIR_nameP addIR_is_rlzr oppIR_is_rlzr.


Lemma oneIR_nameP : is_name (float_to_real 1 0) 1.
Proof.
have ->  : (1 = IZR 1 * powerRZ 2 0)%R by rewrite /=;lra.
exact: float_to_real_spec.
Qed.

Definition mulIR_rlzr (x y : names R) (n : nat):= FI.mul (nat2p n) (x n) (y n).

Lemma mulIR_is_rlzr phix phiy x y :  phix |= x -> phiy |= y ->  (mulIR_rlzr phix phiy) |= (x*y).
Proof.
move => n1 n2. 
have [xr1 xr2] := n1.
have [yr1 yr2] := n2.
rewrite /mulIR_rlzr.
split => /= n.
  exact: FI.mul_correct (nat2p n) (phix n) (phiy n) _ _ (xr1 n) (yr1 n).
have [N Np] := name_bnd2 n1 n2.
set M := (Rmax (Rabs x) (Rabs y) + 1).
have M0 : 0 < M.
  rewrite /M.
  rewrite Rcomplements.Rplus_max_distr_r.
  apply /Rlt_le_trans/Rmax_l.
  suff : 0 <= Rabs x by lra.
  by apply Rabs_pos.
set b := fun m => 2* M * / 2 ^ m +  2 * M * / 2 ^ m + 4 * M * M *  /2 ^ m.
suff [m mb] : exists m,   b m <= /2 ^ n.
  have [N1 N1p] := xr2 m.
  have [N2 N2p] := yr2 m.
  exists (Nat.max m (Nat.max N (Nat.max N1 N2))) => k kge.
  have [kbx1 kbx2] : (FI.bounded (phix k)) /\ diam (phix k) <= /2 ^ m  by apply N1p;lia.
  have [kby1 kby2] : (FI.bounded (phiy k)) /\ diam (phiy k) <= /2 ^ m  by apply N2p;lia.
  have Nk : (N <= k)%nat by lia.
  have [ib1 ib2] := Np _ Nk.
  have [mul_bnd mul_err] := mul_error k kbx1 kby1 ib1 ib2.
  split => //.
  apply (Rle_trans _ (b m)); last by apply mb;lia.
  apply (Rle_trans _ _ _ mul_err).
  have h1 : Rabs (diam (phix k)) = diam (phix k).
    rewrite Rabs_right//.
    suff : FI.lower (phix k) <=  FI.upper (phix k) by lra.
    by apply (Rle_trans _ x); apply contains_bnd.
  have h2 : Rabs (diam (phiy k)) = diam (phiy k).
    rewrite Rabs_right//.
    suff : FI.lower (phiy k) <=  FI.upper (phiy k) by lra.
    by apply (Rle_trans _ y); apply contains_bnd.
  rewrite h1 h2.
  apply Rplus_le_compat.
  apply Rplus_le_compat => //.
  apply Rmult_le_compat_l => //.
  by apply Rmult_le_pos => //; lra.
  rewrite -/M.
  nra.
  apply Rmult_le_compat_l.
    apply Rmult_le_pos;[apply Rmult_le_pos |];lra.
  by apply /tpmnP;lia.
case : (@tpmn_bound (/ 2 ^ n / (2*M + 2*M + 4 * M * M ))).
  apply Rmult_lt_0_compat; first by apply tpmn_lt.
  apply Rinv_0_lt_compat.
  nra.
move => m mp.
exists m.
rewrite /b.
suff : / 2 ^ m * (2*M + 2*M  + 4*M*M) < / 2 ^ n by lra.
rewrite Rcomplements.Rlt_div_r //.
by nra.
Qed.


HB.instance Definition real_isRepComRing :=
  isRepComRing.Build R oneIR_nameP mulIR_is_rlzr.

Definition invIR_rlzr (x : names R) (n : nat):= FI.inv (nat2p n) (x n).



Lemma name_cvg (phi : names R) x : phi |= x -> forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> [/\ FI.lower (phi n) <= FI.upper (phi n),  x -FI.lower (phi n)  < eps &  (FI.upper (phi n) - x) < eps].
Proof.
move => [phin1 phin2] eps eps0.
have [m p] := tpmn_bound eps0.
have [N pn] := phin2 m.
exists N => n Nn.
have [bnd d] := pn _ Nn.
have c := phin1 n.
have ul := contains_bnd bnd c.
split; [lra| |];apply /Rle_lt_trans/p;apply /Rle_trans/d;lra.
Qed.

Lemma neq0_apart phi x : x <> 0 -> phi |= x -> exists M,  M > 0 /\ exists m,  (forall k, (m <= k)%nat -> neg_bound (phi k) M) \/ (forall k, (m <= k)%nat -> pos_bound (phi k) M).
Proof.
move  => h.
have {}h: Rabs x > 0 by apply Rabs_pos_lt.
move => phix.
exists (Rabs x /2).
have  x2pos: Rabs x / 2 > 0 by nra.
split => //.
have [m M]:=  name_cvg phix x2pos.
exists m.
have [xle | xge] := Rle_dec 0 x.
  right => k km.
  have [ul lx ux] := M _ km.
  by move : lx ux;rewrite !Rabs_right; lra.
left => k km.
have [ul lx ux] := M _ km.
by move : lx ux;rewrite !Rabs_left; lra.
Qed.

Lemma invIR_is_rlzr phi x : x != 0 -> phi |= x -> (invIR_rlzr phi) |= GRing.inv x.
Proof.
move => /eqP xne0 rlzr_phi.
split=>n.
  rewrite /invIR_rlzr.
  suff -> : Xreal x^-1 = Xinv (Xreal x) by apply FI.inv_correct;apply rlzr_phi.
  by rewrite /Xinv' /= is_zero_false //.
have [M [M0 [m Hapart]]] := neq0_apart xne0 rlzr_phi.
have Minv0  : (0 < 1/M) by apply Rdiv_lt_0_compat;lra.
have [m' mp'] : exists m, 4 * (1 / M) * /2 ^ m + (1/M)*(1/M) * /2 ^ m <= / 2 ^ n.
  case : (@tpmn_bound (/ 2 ^ n / (4*(1 /M) + (1/M)*(1/M)))).
    apply Rmult_lt_0_compat; first by apply tpmn_lt.
    apply Rinv_0_lt_compat.
    by nra.
  move => m' mp'.
  exists m'.
  suff : (/ 2 ^ m') * (4*(1 /M) + (1/M)*(1/M)) < / 2 ^ n by nra.
  by rewrite Rcomplements.Rlt_div_r;nra.
have [N pN] := rlzr_phi.2 m'. 
exists (Nat.max m (Nat.max N m')) => k kge.
have Fk_bnd : FI.bounded (phi k) by apply pN;lia.
have  [| hb herr]:= inv_error k M0 Fk_bnd.
  have [h' | h'] := Hapart.
  by right;apply h';lia.
  by left;apply h';lia.
split => //.
apply (Rle_trans _ _ _ herr).
have tpmn_kn : (/2 ^ k <= / 2^m') by apply /tpmnP;lia.
apply /Rle_trans/mp'.
apply Rplus_le_compat; [nra|].
apply Rmult_le_compat_l; [nra|].
suff ->: Rabs (diam (phi k)) = diam (phi k) by apply pN;lia.
rewrite Rabs_right//.
suff : FI.lower (phi k) <=  FI.upper (phi k) by lra.
by apply (Rle_trans _ x); apply contains_bnd => //;apply rlzr_phi.
Qed.

HB.instance Definition real_isRepField :=
  isRepField.Build R invIR_is_rlzr.

Require Import QArith.
Open Scope rep_scope.
Definition QtoReal (q : Q) := (float_to_real (Qnum q) 0) / (float_to_real ((Z.pos (Qden q))) 0) .

Lemma QtoReal_spec q : QtoReal q |= (Q2R q).
Proof.
rewrite /Q2R.
rewrite /QtoReal.
apply: mul_nameP.
  have -> : (IZR (Qnum q)) = ((IZR (Qnum q)) * powerRZ 2 0)%R by simpl;lra.
  exact: float_to_real_spec.
apply: inv_nameP; first by apply /eqP; apply Qreals.IZR_nz.
have -> : (IZR (QDen q)) = ((IZR (QDen q)) * powerRZ 2 0)%R by simpl;lra.
exact: float_to_real_spec.
Qed.
Coercion QtoReal: Q >-> names.

Definition approx_real (x : names R) (n : nat) := interval_to_cr_string (x n) (Pos.of_nat n).


