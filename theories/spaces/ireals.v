Require Import Interval.Interval.Float.
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import Bignums.BigQ.BigQ Bignums.BigZ.BigZ.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra classical_sets topology tvs.
From mathcomp Require Import archimedean mathcomp_extra unstable pseudometric_normed_Zmodule normed_module.
Import numFieldNormedType.Exports.
From mathcomp Require Import interval_inference.
From RocqRep Require Import spaces.efftop extra.interval_counttype extra.interval_string extra.tpmn interval_extensions pinterval.
From HB Require Import structures.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

From CoqEAL Require Import hrel param refinements trivial_seq.
From CoqEAL Require Import seqmx seqmx_complements binint binrat.

Import Refinements.Op.
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
Import Order.TTheory.
From mathcomp Require Import boolp.


Local Open Scope ring_scope.
Open Scope classical_set_scope.
Open Scope R_scope.
Definition R : realType := R.
Definition I_set (i : I) : set R := [set x | Interval.contains i (Xreal x)]. 

Lemma IR_basis_spec : forall (x : R) n, exists (i :I),  (I_set i)° x /\ I_set i `<=` ball x (2 ^-n).
Proof.
have p2lt n : 0 < 2 ^ n by apply (pow_lt 2 n);lra.
suff : forall (x : R) n, exists (i : I),  (I_set i)° x /\ I_set i `<=` closed_ball x (2 ^-n).
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
rewrite /I_set /= /spec_I/= !D2R_SFBI2toX !D2R_Float !BigZ.spec_of_Z powerRZ2_neg_pos /= .
have [bi1 bi2]:= base_Int_part (x * 2^n).
have arc:= archimed (x * 2 ^ n).
(* split; first by split;apply (Rmult_le_reg_r (2 ^ n)); rewrite ?Rmult_assoc ?Rinv_l;lra. *)
admit.
(* split => //. *)
(* move=>/=x0 [h1 h2]. *)
(* have -> : (2 ^- n)%R = / (2 ^ n) by rewrite !RealsE. *)
(* rewrite closed_ballE/closed_ball_/= ?ler_distlC; last by apply/RltP;apply Rinv_0_lt_compat. *)
(* apply /andP;split. *)
(*   apply /RleP/Rle_trans/h1. *)
(*   apply (Rmult_le_reg_r (2 ^ n)) => //. *)
(*   by rewrite Rmult_assoc  Rmult_minus_distr_r Rinv_l; lra . *)
(* apply /RleP/(Rle_trans _ _ _ h2). *)
(* apply (Rmult_le_reg_r (2 ^ n)) => //. *)
(* by rewrite Rmult_assoc  Rmult_plus_distr_r Rinv_l; lra . *)
Admitted.

Lemma real_kolmogorov : kolmogorov_space R.
Proof.
apply accessible_kolmogorov.
by apply hausdorff_accessible.
Qed.

Delimit Scope ring_scope with mcR.
Delimit Scope R_scope with rocqR.

Lemma Inbhd_base (x : R) U :  open U -> U x ->
                     exists b,  (I_set b)° x /\ I_set b `<=` U.
Proof.
move => openU Ux.
suff [n bn] : exists n, ball x (2 ^- n) `<=` U.
  have [i [ip1 ip2]] := IR_basis_spec x n.
  by exists i;split=>//;apply: (subset_trans ip2).
have [e /RltP e0 be] := open_subball openU Ux.
have [n np] := tpmn_bound e0 .
exists n.
apply be; last by rewrite exprnN // exprz_ge0.
rewrite /ball_/= distrC subr0 ger0_norm  ?exprnN ?exprz_ge0 //.
rewrite -exprnN.
apply /RltP.
by rewrite -!RealsE.
Qed.

HB.instance Definition real_efftop :=
  effectiveTopological.Build R real_kolmogorov I I_set Inbhd_base.


Definition zeroIR_name : name_of (0 : R).
Proof.
refine {|
    name_fun := (fun n => (FI.zero : @nbhd_type R) )
  |}.
 split => [n | U Uopen U0] /=; rewrite /to_set/=/I_set /=;first by lra.
exists 0%nat => n /= _ x /=xp.
by have -> : x = 0 by lra.
Defined.


(* todo: improve *)
Lemma to_set_bounded i (x eps : R) : to_set i `<=` ball x eps -> FI.bounded i.
Proof.
move: i => /= i.
rewrite /to_set/=/I_set/=/spec_I/=.
have /= H0: (setT `<=` ball x eps) -> false.
  apply /contraPT => _.
  rewrite subTset.
  rewrite -ball_normE/ball_/=.
  move /(congr1 (fun f => f (eps + x))).
  by rewrite RealsE /=  opprD addrC -addrA (addrC (-x))  subrr addr0 normrN ltNge //= ler_norm //= boolp.falseE => ->.
rewrite /FI.bounded/Interval.contains/=.
have setTT P : P ->  [set _ : R | P] = setT.
    by move => pP;apply/eq_set => _ ;apply propext.
case i => //=.
move => l u.
case l => //= [| lm le].
  case u => //= [| um ue].
  by rewrite setTT ?RealsE ?subrr -?RealsE //=;  split => //;apply tpmn_pos.
  rewrite D2R_SFBI2toX.
  move /(_ (minr (D2R (Float um ue)) (x - eps))).
  apply /contraPT => _ .
  rewrite not_implyE /=.
  do ! split => //; first  by apply /RleP;rewrite ge_min lexx.
  by rewrite -ball_normE/=;apply /negP; rewrite -real_leNgt //= !RealsE ler_normr lerBrDl -lerBrDr ge_min lexx orbT.
case u => //=.
rewrite !D2R_SFBI2toX.
move /(_ (maxr (D2R (Float lm le)) (x + eps))).
apply /contraPT => _ .
rewrite not_implyE /=.
do ! split => //;first by apply /RleP;rewrite le_max lexx.
rewrite -ball_normE/=;apply /negP.
rewrite -real_leNgt //= !RealsE ler_normr.
apply /orP;right.
by rewrite opprD opprK addrC lerBrDl le_max lexx orbT.
Qed.

Lemma name_bnd (phi : names R) x : phi |= x -> exists N, forall n, (N <= n)%nat -> ibound (phi n) ((Rabs x)+1).
Proof.
move => [n1 n2].
have [N P] := (n2 _ (ball_open x 1) (ballxx  _ ltr01)).
exists N => n nk.
have := P _ nk.
rewrite  -ball_normE/ball_/=.
have  h : FI.bounded (phi n) by apply: to_set_bounded;apply (P n).
have n1n := n1 n.
have := (contains_bnd h n1n).
move : h.
case: (phi n) => //= => -l u;case l => //=;  case u => //= lm le um ue _ /= ineq  Pn. 
rewrite /ibound.
rewrite !RealsE.
split;apply /RleP;rewrite  -lerBlDl;apply: (le_trans (lerB_dist _ _ ));rewrite distrC ltW //;apply Pn;rewrite /to_set/=/I_set/=/Interval.contains/= !D2R_SFBI2toX.
split => //; by move : ineq;rewrite !D2R_Float;lra.
split => //;by move : ineq;rewrite !D2R_Float;lra.
Qed.

Lemma name_bnd2 (phi1 phi2 : names R)  x y : phi1 |= x -> phi2 |= y -> exists N, forall n, (N <= n)%nat -> ibound (phi1 n) ((Rmax (Rabs x) (Rabs y))+1) /\ ibound (phi2 n) ((Rmax (Rabs x) (Rabs y))+1).
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

Lemma IR_name_metric (phi : names R) x : phi |= x <-> (forall n, (Interval.contains (phi n : I) (Xreal x))) /\ forall n, exists N, forall m, (N <= m)%nat -> FI.bounded (phi m) /\ diam (phi m) <= (/ 2 ^ n).
Proof.
split.
- move => [rlzr1 rlzr2].
  (* split=>// n;first by apply rlzr1. *)
  (* have h0 : (0 < / 2 ^ n)%mcR by apply /RltP;apply tpmn_lt. *)
  (* have [N PN] := (rlzr2 _ (ball_open x (/ 2 ^ n)) (ballxx  _ h0 )). *)
  (* exists N => m mge. *)
  (* have  h : FI.bounded (phi m) by apply: to_set_bounded;apply PN. *)
  (* suff: (/ 2 ^ pint_prec (phi m) <= /2 ^ n). *)
  (*   split=>//. *)
  (*   have [_ + ]:= rlzr1 m. *)
  (*   move /(_ h). *)
  (*   move /Rle_trans. *)
  (*   by apply. *)
  (*   by apply /tpmnP. *)

  (* apply /tpmnP. *)
  (* rewrite /to_set/=/I_set/=/spec_I/=. *)
Admitted.

Lemma oppIR_is_rlzr (x : R) phix : phix |= x -> (lift_rlzr ((fun n i => FI.neg i ):( nat -> @nbhd_type R -> @nbhd_type R)) phix) |= (-x).
Proof.
move  => /IR_name_metric [rlzr1 rlzr2].
apply /IR_name_metric.
split=>n /=.
rewrite /lift_rlzr/=; first by apply (FI.neg_correct (phix n) (Xreal x)).
have [N p] := rlzr2 n.
exists N => k Nk.
rewrite /lift_rlzr /=.
split.
  by have [pb _] := p _ Nk;apply neg_bounded. 
 have [+ +] := p _ Nk. 
rewrite /FI.upper/FI.lower/FI.neg.
case (phix k) => //= l u /andP[r1 r2] h.
rewrite /FI.F.toR/=.
rewrite !FI.F'.neg_correct.
rewrite !FI.F'.real_correct //=;try lra.
Qed.


Lemma addIR_is_rlzr x y phix phiy  : phix |= x -> phiy |= y -> (lift_rlzr2 ((fun n (x y : I )  => FI.add (nat2p n) x y) : nat -> @nbhd_type R -> @nbhd_type R -> @nbhd_type R) phix phiy) |= (x+y)%mcR.
Proof.
rewrite /lift_rlzr2.
move  =>  n1  n2. 
have   /IR_name_metric [xr1 xr2]:= n1.
have /IR_name_metric [yr1 yr2] := n2.
apply /IR_name_metric.
split => /= n.
apply (FI.add_correct _ (phix n) (phiy n) _ _ (xr1 n) (yr1 n)).
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

Definition oppIR_rlzr : rlzr_of (fun (x : R) => (Algebra.opp x)).
Proof.
by refine {|
    rlzr_correct := oppIR_is_rlzr
  |}.
Defined.

Definition addIR_rlzr : rlzr2_of (fun (x y : R) => (Algebra.add x y)).
Proof.
by refine {|
    rlzr2_correct := addIR_is_rlzr
  |}.
Defined.


HB.instance Definition real_effzmod := repTopZModule.Build R zeroIR_name addIR_rlzr oppIR_rlzr.

Lemma floatIR_nameP m e :  ((fun n=> FI.singleton (Float m e)) : names R)|= IZR (to_Z m) * powerRZ 2 (to_Z e).
Proof.
apply /IR_name_metric.
split => n /=.  
  by rewrite D2R_SFBI2toX D2R_Float; lra.
exists 0%nat => k _.
split=>//.
rewrite !RealsE subrr.
apply /RleP.
by rewrite invr_ge0 exprn_ge0.
Qed.

Definition float_to_real_fun (m e : Z) : names R := (fun n => FI.singleton (Float (of_Z m) (of_Z e))).

Lemma float_to_real_spec m  e : (float_to_real_fun m e : names R) |= IZR m * powerRZ 2 e.
Proof.
rewrite /float_to_real_fun -{2}(spec_of_Z m) -{2}(spec_of_Z e).
by apply floatIR_nameP.
Qed.


Definition float_to_real (m e : Z) : name_of (X:=R) (IZR m * powerRZ 2 e).
Proof.
refine {| name_fun := float_to_real_fun m e |}.
exact: float_to_real_spec.
Defined.


Definition one_name : name_of (X:=R) 1.
Proof.
refine {|name_fun := float_to_real_fun 1 0|}.
have -> : (1 = IZR 1 * powerRZ 2 0)%R by rewrite /=;lra.
apply (float_to_real 1 0).
Defined.

Definition mulIR_rlzr_fun (n : nat): (@nbhd_type R) -> (@nbhd_type R) -> (@nbhd_type R) := FI.mul (nat2p n).

Lemma mulIR_is_rlzr phix phiy x y :  phix |= x -> phiy |= y ->  (lift_rlzr2 mulIR_rlzr_fun phix phiy) |= (x*y).
Proof.
rewrite /lift_rlzr2/mulIR_rlzr_fun/=.
move => n1 n2. 
have /IR_name_metric [xr1 xr2] := n1.
have /IR_name_metric [yr1 yr2] := n2.
apply IR_name_metric.
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

Definition mulIR_rlzr : rlzr2_of (fun (x y : R) => ( x * y)%mcR).
Proof.
refine {|
    rlzr2_fun := mulIR_rlzr_fun
  |}.
move => x y phi1 phi2.
apply mulIR_is_rlzr.
Defined.

HB.instance Definition real_isRepNzRing :=
  isRepNzRing.Build R one_name mulIR_rlzr.

Definition invIR_rlzr_fun (n : nat) : (@nbhd_type R) -> (@nbhd_type R)  := FI.inv (nat2p n).


Lemma name_cvg (phi : names R) x : phi |= x -> forall eps, eps > 0 -> exists N, forall n, (N <= n)%nat -> [/\ FI.lower (phi n) <= FI.upper (phi n),  x -FI.lower (phi n)  < eps &  (FI.upper (phi n) - x) < eps].
Proof.
move => /IR_name_metric [phin1 phin2] eps eps0.
have [m p] := tpmn_bound eps0.
have [N pn] := phin2 m.
exists N => n Nn.
have [bnd d] := pn _ Nn.
have c := phin1 n.
have ul := contains_bnd bnd c.
split; [lra| |];apply /Rle_lt_trans/p;apply /Rle_trans/d;lra.
Qed.

Lemma neq0_apart (phi : names R) x : x <> 0 -> phi |= x -> exists M,  M > 0 /\ exists m,  (forall k, (m <= k)%nat -> neg_bound (phi k) M) \/ (forall k, (m <= k)%nat -> pos_bound (phi k) M).
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

Lemma invIR_is_rlzr x (phi : names R)  : x != 0 -> phi |= x -> (lift_rlzr invIR_rlzr_fun phi) |= GRing.inv x.
Proof.
move => /eqP xne0 rlzr_phi0.
have /IR_name_metric rlzr_phi := rlzr_phi0.
apply /IR_name_metric.
split=>n.
  rewrite /invIR_rlzr_fun.
  suff -> : Xreal x^-1 = Xinv (Xreal x) by apply FI.inv_correct;apply rlzr_phi.
  by rewrite /Xinv' /= is_zero_false //.
have [M [M0 [m Hapart]]] := neq0_apart xne0 rlzr_phi0.
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
  isRepField.Build R invIR_rlzr_fun invIR_is_rlzr.

From Stdlib Require QArith.
Definition QtoReal (q : QArith_base.Q) : (name_of (X:=R) (Q2R q)). 
Proof.
apply: (eval_rlzr2  mul_rlzr). 
  refine {|name_fun := (float_to_real_fun (QArith_base.Qnum q) 0) |}.
  have -> : (IZR (QArith_base.Qnum q)) = ((IZR (QArith_base.Qnum q)) * powerRZ 2 0)%R by simpl;lra.
  apply float_to_real_spec.
 apply: inv_name; last by apply /eqP;apply Qreals.IZR_nz. 
refine {|name_fun :=  float_to_real_fun (QArith_base.QDen q) 0|}.
 have -> : (IZR (QArith_base.QDen q)) = ((IZR (QArith_base.QDen q)) * powerRZ 2 0)%R by simpl;lra. 
apply float_to_real_spec.
Defined.

Module Params.
Definition index := 100%nat.
End Params.
Module RealObject.
  Definition T := (R : repFieldType).
End RealObject.

Module E := EffectiveTop(Params).

Module RApprox := E.ForField(RealObject).

Import RApprox.

Open Scope rep_scope.
Notation Rname := (name_of (X:=R) _ ).
Coercion QtoReal: QArith_base.Q >-> Rname.
Print one_approx.
Print one_name.
Eval vm_compute in (name_fun _ (float_to_real 1 0) 10%nat : I).
Eval vm_compute in (name_fun _ one_name 10%nat).
Eval vm_compute in ((name_fun (X:=R) _ zero_rlzr 10%nat) : I).

Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.

Notation "x `| n"  := (interval_to_cr_string (approx_val x) n) (at level 2).

Eval vm_compute in (interval_to_cr_string (name_fun _ (float_to_real 1 2) 10%nat : I)) 5.
 Eval vm_compute in (float_to_real 1 2) `| 5.

Fixpoint test_fix {x : R}  (n : nat) (p : ApproximationOf x)  : {r : R & ApproximationOf r} :=
  match n with
  | 0%nat => existT _ _ p
  | n'.+1 => test_fix n' ((float_to_real 1 2 : ApproximationOf _) * p * (1 - p))%CT
 end.

Definition test_fix' {x} n p  := projT2 (@test_fix x n p).

Definition x0 := (float_to_real 17 (-6)).
Eval vm_compute in (test_fix' 10 x0) `| 10.

Eval vm_compute in (1+(float_to_real 1 2) * (float_to_real 5 4))%CT `| 3.


From RocqRep Require Import matrix.

Module MatrixObject.
  Definition T := ('M[R]_(2,2) : effectiveTopZModType).
End MatrixObject.


Module MApprox := E.ForZmod(MatrixObject).
Import MApprox.
Definition z := (0 : ApproximationOf (Algebra.zero : 'M[R]_(2,2))).

Definition approx_real_matrix {n m} (x : @nbhd_type 'M[R]_(n,m)) p := map (fun r=>(map (fun j => interval_to_cr_string j p) r)) x. 
Definition M1  := mx_name_from_fun (m:=2) (n:=2) (fun i j => float_to_real (Z.of_nat i) (-2)).

Notation "x `|| n"  := (approx_real_matrix (approx_val x) n) (at level 2). 
Eval vm_compute in ((approx_val 0) ).
(* Definition a := (QArith_base.Qmake 2 200 : name_of _). *)
(* Definition h := (add_rlzr a a). *)
(* Definition approx_name {x : R} (phi : name_of x) (n : nat) := interval_to_cr_string (phi.(name_fun _) n) (Pos.of_nat n). *)

(* Eval vm_compute in (approx_name (inv_name a0 _ ) 10). *)
(* Eval vm_compute in (approx_name (a - 0 + a -a + a - a - a)%rep 100). *)
(* Fixpoint fix_slow {x : R} (a : name_of x) (n : nat) : { y : R & name_of y } := *)
(*   match n as n0 return { y : R & name_of y } with *)
(*   | 0%nat => existT _ x a *)
(*   | n'.+1 => *)
(*       let y := (a + a)%rep in *)
(*       fix_slow y n' *)
(*   end. *)

(* Definition fix_slow' {x} (a : name_of x) n := projT2 (fix_slow a n). *)

(* Eval vm_compute in (approx_name (fix_slow' a 14)%rep 100). *)
(* Module test_params  <: EFFTOP_PARAMS. *)
(*   Definition index := 5%nat. *)
(* End test_params. *)
(* Module TEST  := EffectiveTop test_params. *)
(* Import TEST. *)
(* Definition aa := (a0 + a0 )%rep. *)

(* Fixpoint fix_fast (a : @ ) (n : nat) : { y : R & name_of y } := *)
(*   match n as n0 return { y : R & name_of y } with *)
(*   | 0%nat => existT _ x a *)
(*   | n'.+1 => *)
(*       let y := (a + a)%rep in *)
(*       fix_slow y n' *)
(*   end. *)
(* Eval vm_compute in (interval_to_cr_string (fix_slow' a0 20 : @nbhd_type R) 3). *)

(* Notation "x `| n"  := (approx_real x n) (at level 2). *)

(* Notation mxr_type := (seq (seq (names R))). *)

(* Definition rmx_from_seq (M : mxr_type) := mx_from_seq (n:=(List.length M).-1) (m:=(List.length (nth [::] M 0)).-1) (c:=(0 0%nat)) M. *)

(* Coercion rmx_from_seq:  mxr_type >-> names. *)


(* Notation "x `|| n"  := (approx_real_matrix x n) (at level 2). *)
