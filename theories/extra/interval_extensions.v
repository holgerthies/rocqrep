Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import Bignums.BigQ.BigQ Bignums.BigZ.BigZ.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.
Import Order.TTheory GRing.Theory Num.Def Num.Theory.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Local Open Scope ring_scope.
Module SFBI2 := SpecificFloat BigIntRadix2.    
From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
Module FI   := FloatInterval SFBI2.         
Import Interval.Real.Xreal.
Import GRing.Theory Num.Theory.
Import BigN BigZ.
Locate archi_boundP.
Notation I := FI.type.
Notation D2R := FI.F.toR.
Definition F := SFBI2.type.
Coercion FI.convert: I >-> Interval.interval.
Coercion D2R: FI.F.type >-> R.
Open Scope R_scope.
Import SFBI2.
Notation diam i := (FI.upper i - FI.lower i). 


Notation pos_bound I M := (FI.lower I >= M /\ FI.upper I >=  M). 
Notation neg_bound I M := (FI.lower I <= - M /\ FI.upper I <= - M). 
Definition nat2p n := SFBI2.PtoP (Pos.of_nat n).

Lemma neg_bounded x : FI.bounded x -> FI.bounded (FI.neg x). 
Proof.
case x => //.
rewrite /FI.neg/FI.bounded/= => l u /andP[].
by rewrite !FI.F'.real_neg => -> ->.
Qed.


Lemma D2R_SFBI2toX m e: SFBI2.toX (Float m e) = Xreal (D2R (Float m e)).
Proof.
rewrite /D2R/proj_val/=/SFBI2.toX/=/Basic.FtoX/=.
by case: BigIntRadix2.mantissa_sign (Float m e) => //.
Qed.

Lemma D2R_Float (m e: bigZ):
  D2R (Float m e) = IZR (BigZ.to_Z m) * powerRZ 2 (BigZ.to_Z e).
Proof.
rewrite /D2R /SFBI2.toX /SFBI2.toF/=.
case: (BigIntRadix2.mantissa_sign m) (BigIntRadix2.mantissa_sign_correct m);
  rewrite /BigIntRadix2.MtoZ /=.
	by move => ->; lra.
move => s p' [-> [p]].
rewrite /BigIntRadix2.EtoZ /BigIntRadix2.MtoP => -> {p'}.
move: (BigZ.to_Z e) => {e} [ | e | e ] /=;
  rewrite ?Z.pow_pos_fold ?mult_IZR ?pow_IZR ?Znat.positive_nat_Z;
  case: s => //; lra.
Qed.

Lemma generic_round_bnd rnd x p :   Generic_fmt.Valid_rnd rnd -> Rabs ((Generic_fmt.round radix (FLX.FLX_exp (Z.pos (prec (nat2p p)))) rnd x) - x) <= Rabs x * (2 * /2 ^ p).
Proof.
move => rnd_valid.
apply: Rle_trans.
  apply Ulp.error_le_ulp => //.
  by apply FLX.FLX_exp_valid.
apply : Rle_trans.
apply FLX.ulp_FLX_le => //.
apply Rmult_le_compat_l; first by apply Rabs_pos.
case: p => //=; first by rewrite Rinv_1;lra.
move => n.
have -> : (prec (nat2p (n.+1))) = Pos.of_nat n.+1.
  by rewrite /prec/nat2p/= spec_of_pos;lia.
have -> : Z.pos_sub 1 (Pos.of_nat n.+1) = (- Z.of_nat n)%Z.
  by change (1%Z - Z.pos (Pos.of_nat n.+1) = (- Z.of_nat n)%Z)%Z;lia.
rewrite Raux.bpow_opp -Rdiv_def Rdiv_mult_distr Rdiv_diag; last by lra.
rewrite Rdiv_1_l.
apply Raux.Rinv_le; first by apply pow_lt;lra.
rewrite -Raux.IZR_Zpower/= ?pow_IZR //; [lra | lia].
Qed.
Lemma tpmn_pos n: 0 <= /2^n.

Proof. by apply/Rlt_le/Rinv_0_lt_compat/pow_lt; lra. Qed.
Lemma tpmn_lt n: 0 < /2^n.
Proof. apply/Rinv_0_lt_compat/pow_lt; lra. Qed.

Lemma  add_up_error p m1 e1 m2 e2 M : Rabs (toR (Float m1 e1)) <= M -> Rabs (toR (Float m2 e2)) <= M ->  add_UP (nat2p p) (Float m1 e1) (Float m2 e2) <= toR (Float m1 e1) + toR (Float m2 e2) + 4*M * /2 ^ p.
Proof.
move => xbnd ybnd.
rewrite /SFBI2.add_UP /FI.F.toR SFBI2.add_slow_correct /Basic.Xround /Xbind/proj_val !toX_Float /Basic.round /=.
apply Rcomplements.Rabs_le_between'.
apply: Rle_trans.
apply generic_round_bnd; first by apply Generic_fmt.valid_rnd_UP.
have -> : (4 * M * / 2^ p = (M + M) * (2 * / 2^ p)) by lra.
apply Rmult_le_compat_r.
apply Rmult_le_pos; by [apply tpmn_pos|lra].
apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
by apply Rplus_le_compat.
Qed.

Lemma  add_dn_error p m1 e1 m2 e2 M : Rabs (toR (Float m1 e1)) <= M -> Rabs (toR (Float m2 e2)) <= M ->  toR (Float m1 e1) + toR (Float m2 e2) - 4*M * /2 ^ p <= add_DN (nat2p p) (Float m1 e1) (Float m2 e2).
Proof.
move => xbnd ybnd.
rewrite /SFBI2.add_UP /FI.F.toR SFBI2.add_slow_correct /Basic.Xround /Xbind/proj_val !toX_Float /Basic.round /=.
apply Rcomplements.Rabs_le_between'.
apply: Rle_trans.
apply generic_round_bnd; first by apply Generic_fmt.valid_rnd_DN.
have -> : (4 * M * / 2^ p = (M + M) * (2 * / 2^ p)) by lra.
apply Rmult_le_compat_r.
apply Rmult_le_pos; by [apply tpmn_pos|lra].
apply: (Rle_trans _ _ _ (Rabs_triang _ _)).
by apply Rplus_le_compat.
Qed.

Definition ibound I M := (Rabs (toR (FI.lower I)) <= M /\ Rabs (toR (FI.upper I)) <= M).

Lemma add_error (I J : FI.type) M p:
  FI.bounded I ->  FI.bounded J -> 
  ibound I M -> ibound J M ->
  FI.bounded (FI.add (nat2p p) I J)
  /\
  diam (FI.add (nat2p p) I J) <= diam I + diam J + 8 * M *  /2 ^ p.
Proof.
case I => //; case => //lIm lIe; case => //uIm uIe _.
case J => //; case => //lJm lJe; case => //uJm uJe _.
move => [Ibl Ibu] [Jbl Jbu].
split.
  by rewrite /FI.bounded/FI.add !real_correct/FI.F.add_DN/FI.F.add_UP !add_slow_correct  /Basic.Xround /Xbind/proj_val !toX_Float/= .
rewrite /FI.upper /FI.lower /FI.add.
apply Rcomplements.Rle_minus_l.
apply : Rle_trans.
  apply (add_up_error _ Ibu Jbu).
ring_simplify.
rewrite !Rplus_assoc.
apply Rplus_le_compat_l.
apply Rplus_le_compat_l.
suff : toR (Float lIm lIe) + toR (Float lJm lJe) - 4 * M * / 2^ p <=  FI.F.add_DN (nat2p p) (Float lIm lIe) (Float lJm lJe) by lra.
by apply add_dn_error.
Qed.

Lemma contains_bnd (I : FI.type) x: FI.bounded I -> Interval.contains I (Xreal x) -> FI.lower I <= x /\ x <= FI.upper I.
Proof.
case I =>//; case => // m e; case => // m' e' /= _.
by rewrite !toX_Float.
Qed.

Lemma sign_large_float_zero m1 e1 m2 e2:  FI.sign_large_ (Float m1 e1) (Float m2 e2) = Xeq ->
                                          [/\ BigIntRadix2.mantissa_sign m1 = Specific_sig.Mzero,
                                            BigIntRadix2.mantissa_sign m2 = Specific_sig.Mzero,
                                            (toX (Float m1 e1) = Xreal 0) &
                                            toX (Float m2 e2) = Xreal 0].
Proof.
rewrite /FI.sign_large_/=.
have := BigIntRadix2.mantissa_sign_correct m1.
have := BigIntRadix2.mantissa_sign_correct m2.
case : (BigIntRadix2.mantissa_sign m1); case : (BigIntRadix2.mantissa_sign m2); try by case => ? [] //.
rewrite /BigIntRadix2.MtoZ.
rewrite !toX_Float !D2R_Float.
move => -> -> _.
split => //; by apply congr1;lra.
Qed.

Lemma mantissa_sign_zero m : BigIntRadix2.mantissa_sign m = Specific_sig.Mzero -> forall e, toX (Float m e) = Xreal 0.
Proof.
move => h e.
move : h.
have := BigIntRadix2.mantissa_sign_correct m.
case : (BigIntRadix2.mantissa_sign m); last by case => ? [] //.
by rewrite /BigIntRadix2.MtoZ !toX_Float !D2R_Float => -> _;apply congr1;lra.
Qed.

Lemma upper_mul p  lIm lIe uIm uIe lJm lJe uJm uJe :
  let I := Ibnd (Float lIm lIe) (Float uIm uIe) in
  let J := Ibnd (Float lJm lJe) (Float uJm uJe) in
  [\/ toX (FI.upper (FI.mul p I J)) = toX (FI.F.mul_UP p (FI.upper I) (FI.upper J)),
    toX (FI.upper (FI.mul p I J)) = toX (FI.F.mul_UP p (FI.lower I) (FI.lower J)),
    toX (FI.upper (FI.mul p I J)) = toX (FI.F.mul_UP p (FI.upper I) (FI.lower J))
  | toX (FI.upper (FI.mul p I J))  = toX (FI.F.mul_UP p (FI.lower I) (FI.upper J)) ].
Proof.
rewrite /FI.mul.
case s: (FI.sign_large_ _ _) => /=.
- have [-> -> -> ->]:= sign_large_float_zero s.
  by apply Or41.
-  case s': (FI.sign_large_ _ _) => /=.
    + have [-> -> h1 h2]:= sign_large_float_zero s'.
      by case e1:  (BigIntRadix2.mantissa_sign uIm); rewrite ?(mantissa_sign_zero e1);apply Or41.
    + by apply Or42.
    + by apply Or43.
    + by apply Or42.
-  case s': (FI.sign_large_ _ _) => /=.
   + have [-> -> h1 h2]:= sign_large_float_zero s'.
     by case e1:  (BigIntRadix2.mantissa_sign uIm); rewrite ?(mantissa_sign_zero e1);apply Or41.
    + by apply Or44.
    + by apply Or41.
    + by apply Or41.
- case s': (FI.sign_large_ _ _) => /=.
  + have [-> -> hs hs']:= sign_large_float_zero s'.
    case e1 : (BigIntRadix2.mantissa_sign uIm) => /=.
    case e2:  (BigIntRadix2.mantissa_sign lIm) => //=.
    by move : s;rewrite /FI.sign_large_/FI.F.cmp e1 e2.
    by apply Or44.
    by apply Or41.
  + by apply Or42.
  + by apply Or41.
  + rewrite /FI.F.max.
    case cmpe: (cmp _ _).
    by apply Or41.
    by apply Or41.
    by apply Or42.
    move : cmpe.
    case e1 : (BigIntRadix2.mantissa_sign lIm);case e2 : (BigIntRadix2.mantissa_sign uIm) => //=.
    * by rewrite e1 e2.
    * rewrite /= e1.
      case e3 : (BigIntRadix2.mantissa_sign uJm) => /=; first by rewrite e3.
      move => h.
      apply Or41.
      move : h.
      case: (round_aux _ _ _ _) => //.
      move => ? ?.
      by case: (BigIntRadix2.mantissa_sign _) => //; case.
    * case e3 : (BigIntRadix2.mantissa_sign lJm) => /=.
        by rewrite e3; case (BigIntRadix2.mantissa_sign _) => // -[].
        rewrite /cmp.
        case: (round_aux _ _ _ _); first by move => _; apply Or42.
        move => ? ?.
        case  (BigIntRadix2.mantissa_sign _); first by case (BigIntRadix2.mantissa_sign _) => // -[].
        move => s0 m.
        case (BigIntRadix2.mantissa_sign uIm ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
    * case e3 : (BigIntRadix2.mantissa_sign lJm) => //=.
      case e4 : (BigIntRadix2.mantissa_sign uJm) => //=;first by rewrite e3 e4.
        case: (round_aux _ _ _ _); first by move => _; apply Or41.
        move => ? ?.
        case  (BigIntRadix2.mantissa_sign _); first by case (BigIntRadix2.mantissa_sign _) => // -[].
        move => s0 m.
        case (BigIntRadix2.mantissa_sign _ ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        rewrite /cmp.
        case: (round_aux _ _ _ _); first by move => _; apply Or42.
        move => ? ?.
        case  (BigIntRadix2.mantissa_sign _).
        case  (BigIntRadix2.mantissa_sign _).
        case  (BigIntRadix2.mantissa_sign _) => //.
        by case.
        move => s0 m.
        case (BigIntRadix2.mantissa_sign uJm ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        move => ? ?.
        case: (round_aux _ _ _ _); first by move => _; apply Or41.
        move => s0 m.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        by case.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        by case.
        move => [] ? [] // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
Qed.

Lemma mul_up_error p m1 e1 m2 e2 M : Rabs (toR (Float m1 e1)) <= M -> Rabs (toR (Float m2 e2)) <= M ->  mul_UP (nat2p p) (Float m1 e1) (Float m2 e2) <= toR (Float m1 e1) * toR (Float m2 e2) + 2*M*M * /2 ^ p.
Proof.
move => xbnd ybnd.
rewrite /SFBI2.mul_UP /FI.F.toR mul_correct /Basic.Xround /Xbind/proj_val !toX_Float /Basic.round /=.
apply Rcomplements.Rabs_le_between'.
apply: Rle_trans.
apply generic_round_bnd; first by apply Generic_fmt.valid_rnd_UP.
have -> : (2 * M * M * / 2^ p = (M * M) * (2 * / 2^ p)) by lra.
apply Rmult_le_compat_r.
apply Rmult_le_pos; by [apply tpmn_pos|lra].
rewrite RnormM. 
apply Rmult_le_compat => //; by apply Rabs_pos.
Qed.

Lemma  mul_dn_error p m1 e1 m2 e2 M : Rabs (toR (Float m1 e1)) <= M -> Rabs (toR (Float m2 e2)) <= M ->  toR (Float m1 e1) * toR (Float m2 e2) - 2*M*M * /2 ^ p <= mul_DN (nat2p p) (Float m1 e1) (Float m2 e2).
Proof.
move => xbnd ybnd.
rewrite /SFBI2.mul_DN /FI.F.toR mul_correct /Basic.Xround /Xbind/proj_val !toX_Float /Basic.round /=.
apply Rcomplements.Rabs_le_between'.
apply: Rle_trans.
apply generic_round_bnd; first by apply Generic_fmt.valid_rnd_DN.
have -> : (2 * M * M * / 2^ p = (M * M) * (2 * / 2^ p)) by lra.
apply Rmult_le_compat_r.
apply Rmult_le_pos; by [apply tpmn_pos|lra].
rewrite RnormM. 
apply Rmult_le_compat => //; by apply Rabs_pos.
Qed.

Lemma lower_mul p  lIm lIe uIm uIe lJm lJe uJm uJe :
  let I := Ibnd (Float lIm lIe) (Float uIm uIe) in
  let J := Ibnd (Float lJm lJe) (Float uJm uJe) in
  [\/ toX (FI.lower (FI.mul p I J)) = toX (FI.F.mul_DN p (FI.upper I) (FI.upper J)),
    toX (FI.lower (FI.mul p I J)) = toX (FI.F.mul_DN p (FI.lower I) (FI.lower J)),
    toX (FI.lower (FI.mul p I J)) = toX (FI.F.mul_DN p (FI.upper I) (FI.lower J))
  | toX (FI.lower (FI.mul p I J))  = toX (FI.F.mul_DN p (FI.lower I) (FI.upper J)) ].
Proof.
rewrite /FI.mul.
case s: (FI.sign_large_ _ _) => /=.
- have [-> -> -> ->]:= sign_large_float_zero s.
  by apply Or41.
-  case s': (FI.sign_large_ _ _) => /=.
    + have [-> -> h1 h2]:= sign_large_float_zero s'.
      by case e1:  (BigIntRadix2.mantissa_sign uIm); rewrite ?(mantissa_sign_zero e1);apply Or41.
    + by apply Or41.
    + by apply Or44.
    + by apply Or44.
-  case s': (FI.sign_large_ _ _) => /=.
   + have [-> -> h1 h2]:= sign_large_float_zero s'.
     by case e1:  (BigIntRadix2.mantissa_sign uIm); rewrite ?(mantissa_sign_zero e1);apply Or41.
    + by apply Or43.
    + by apply Or42.
    + by apply Or43.
- case s': (FI.sign_large_ _ _) => /=.
  + have [-> -> hs hs']:= sign_large_float_zero s'.
    case e1 : (BigIntRadix2.mantissa_sign uIm) => /=.
    case e2:  (BigIntRadix2.mantissa_sign lIm) => //=.
    by move : s;rewrite /FI.sign_large_/FI.F.cmp e1 e2.
    by apply Or44.
    by apply Or41.
  + by apply Or43.
  + by apply Or44.
  + rewrite /FI.F.min.
    case cmpe: (cmp _ _).
    by apply Or44.
    by apply Or44.
    by apply Or43.
    move : cmpe.
    case e1 : (BigIntRadix2.mantissa_sign lIm);case e2 : (BigIntRadix2.mantissa_sign uIm) => //=.
    * by rewrite e1 e2.
    * rewrite /= e1.
      case e3 : (BigIntRadix2.mantissa_sign lJm) => /=; first by rewrite e3.
      move => h.
      apply Or43.
      move : h.
      case: (round_aux _ _ _ _) => //.
      move => ? ?.
      by case: (BigIntRadix2.mantissa_sign _) => //; case.
    * case e3 : (BigIntRadix2.mantissa_sign uJm) => /=.
        by rewrite e3; case (BigIntRadix2.mantissa_sign _) => // -[].
        rewrite /cmp.
        case: (round_aux _ _ _ _); first by move => _; apply Or44.
        move => ? ?.
        case  (BigIntRadix2.mantissa_sign _); first by case (BigIntRadix2.mantissa_sign _) => // -[].
        move => s0 m.
        case (BigIntRadix2.mantissa_sign uIm ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
    * case e3 : (BigIntRadix2.mantissa_sign lJm) => //=.
      case e4 : (BigIntRadix2.mantissa_sign uJm) => //=;first by rewrite e3 e4.
        case: (round_aux _ _ _ _); first by move => _; apply Or44.
        move => ? ?.
        rewrite /cmp.
        case  (BigIntRadix2.mantissa_sign _); first by case (BigIntRadix2.mantissa_sign _) => // -[].
        move => s0 m.
        case (BigIntRadix2.mantissa_sign _ ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        rewrite /cmp.
        case: (round_aux _ _ _ _); first by move => _; apply Or43.
        move => ? ?.
        case  (BigIntRadix2.mantissa_sign _).
        case  (BigIntRadix2.mantissa_sign _).
        case  (BigIntRadix2.mantissa_sign _) => //.
        by case.
        move => s0 m.
        case (BigIntRadix2.mantissa_sign _ ) => //; first by case s0.
        case s0;case => // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        move => ? ?.
        case: (round_aux _ _ _ _); first by move => _; apply Or44.
        move => s0 m.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        by case.
        case (BigIntRadix2.mantissa_sign _ ) => //.
        by case.
        move => [] ? [] // m0;rewrite /cmp_aux2;case  (BigIntRadix2.exponent_cmp _) => //.
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
        by case  (BigIntRadix2.exponent_cmp _); rewrite /cmp_aux1; case ( BigIntRadix2.mantissa_cmp _).
Qed.

Lemma toX_eq_D2R_eq x y : toX x = toX y -> D2R x = D2R y. 
Proof.
move => h.
by rewrite /D2R h.
Qed.

Lemma mul_bnd  (I J : FI.type) M: FI.bounded I ->  FI.bounded J -> 
  ibound I M -> ibound J M -> forall a b, (a = FI.upper I \/ a = FI.lower I) -> (b = FI.upper J \/ b = FI.lower J ) -> Rabs (a * b -  FI.upper I * FI.upper J) <=  M * Rabs (diam I) + M * Rabs (diam J).
Proof.
move => Ib Jb  [Ibl Ibu] [Jbl Jbu].
have M0 : 0 <= M by apply /Rle_trans/Ibl/Rabs_pos.
have abs_pos1 := Rabs_pos (diam I).
have abs_pos2 := Rabs_pos (diam J).
move => a b [-> | ->] [-> | ->] /=.
- rewrite Rminus_diag Rabs_R0.
  suff : 0 <=  M * (Rabs (diam I) + Rabs (diam J)) by lra.
  by apply Rmult_le_pos;lra.
- rewrite -Rmult_minus_distr_l.
  rewrite RnormM.
  apply: (Rle_trans _ (M * Rabs (diam J))).
  rewrite Rabs_minus_sym.
  apply Rmult_le_compat_r => //.
  suff : 0 <= M * Rabs (diam I) by lra.
  by apply Rmult_le_pos;lra.
- rewrite -Rmult_minus_distr_r.
  rewrite RnormM.
  apply: (Rle_trans _ (Rabs (diam I) * M)).
  rewrite Rabs_minus_sym.
  apply Rmult_le_compat_l => //.
  suff : 0 <= M * Rabs (diam J) by lra.
  by apply Rmult_le_pos;lra.
- have -> : FI.lower I * FI.lower J - FI.upper I * FI.upper J = FI.upper J * (FI.lower I - FI.upper I) + FI.lower I * (FI.lower J - FI.upper J)  by lra.
  apply (Rle_trans _ _ _ (Rabs_triang _ _)).
  apply Rplus_le_compat;rewrite RnormM.
  by rewrite Rabs_minus_sym;apply Rmult_le_compat_r.
  by rewrite Rabs_minus_sym;apply Rmult_le_compat_r.
Qed.

Lemma bounded_realP I : FI.F.real (FI.upper I) && FI.F.real (FI.lower I) <-> FI.bounded I.
Proof. split;by case I => // [[[]//= | m1 e1 [//=| m2 e2]]]. Qed.

Lemma mul_error_upper (I J : FI.type) M p:
  FI.bounded I ->  FI.bounded J -> 
  ibound I M -> ibound J M ->
   D2R (FI.upper (FI.mul (nat2p p) I J)) <=  D2R (FI.upper I) * D2R (FI.upper J) + (M * Rabs (diam I) + M * Rabs (diam J) + 2*M*M *  /2 ^ p).
Proof.
move => Ib Jb IM JM.
have  := mul_bnd Ib Jb IM JM.
move : Ib Jb IM JM.
case I => //; case => //lIm lIe; case => //uIm uIe _.
case J => //; case => //lJm lJe; case => //uJm uJe _.
move => [Ibl Ibu] [Jbl Jbu] H. 
case (upper_mul (nat2p p)  lIm lIe uIm uIe lJm lJe uJm uJe ) => /toX_eq_D2R_eq -> .
- apply : (Rle_trans _ _ _ (mul_up_error _ Ibu Jbu)).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite /=.
  have M0 : 0 <= M by apply /Rle_trans/Ibl/Rabs_pos.
  suff: (0 <=  M * Rabs (D2R (Float uIm uIe) - D2R (Float lIm lIe)) + M * Rabs (D2R (Float uJm uJe) - (D2R (Float lJm lJe))))%R by lra.
  by apply Rplus_le_le_0_compat; apply Rmult_le_pos => //; apply Rabs_pos.
- apply : (Rle_trans _ _ _ (mul_up_error _ Ibl Jbl)).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite Rplus_assoc.
  apply Rcomplements.Rabs_le_between'.
  by apply H; right.
- apply : (Rle_trans _ _ _ (mul_up_error _ Ibu Jbl)).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite Rplus_assoc.
  apply Rcomplements.Rabs_le_between'.
  by apply H ;[left | right].
- apply : (Rle_trans _ _ _ (mul_up_error _ Ibl Jbu)).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite Rplus_assoc.
  apply Rcomplements.Rabs_le_between'.
  by apply H; [right | left].
Qed.

Lemma mul_error_lower (I J : FI.type) M p:
  FI.bounded I ->  FI.bounded J -> 
  ibound I M -> ibound J M ->
  D2R (FI.upper I) * D2R (FI.upper J) - (M * Rabs (diam I) + M * Rabs (diam J) + 2*M*M *  /2 ^ p) <= D2R (FI.lower (FI.mul (nat2p p) I J)).
Proof.
move => Ib Jb IM JM.
have  := mul_bnd Ib Jb IM JM.
move : Ib Jb IM JM.
case I => //; case => //lIm lIe; case => //uIm uIe _.
case J => //; case => //lJm lJe; case => //uJm uJe _.
move => [Ibl Ibu] [Jbl Jbu] H. 
case (lower_mul (nat2p p)  lIm lIe uIm uIe lJm lJe uJm uJe ) => /toX_eq_D2R_eq -> .
- apply /Rle_trans/(mul_dn_error _ Ibu Jbu).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite -Rminus_plus_distr.
  apply Rcomplements.Rabs_le_between'.
  by apply H; left.
- apply /Rle_trans/(mul_dn_error _ Ibl Jbl).
  apply Rcomplements.Rle_minus_r.
  rewrite /=.
  ring_simplify.
  rewrite -Rminus_plus_distr.
  apply Rcomplements.Rabs_le_between'.
  by apply H;right.
- apply/Rle_trans/(mul_dn_error _ Ibu Jbl).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite -Rminus_plus_distr.
  apply Rcomplements.Rabs_le_between'.
  by apply H ;[left | right].
- apply/Rle_trans/(mul_dn_error _ Ibl Jbu).
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite -Rminus_plus_distr.
  apply Rcomplements.Rabs_le_between'.
  by apply H; [right | left].
Qed.

Lemma mul_error (I J : FI.type) M p:
  FI.bounded I ->  FI.bounded J -> 
  ibound I M -> ibound J M ->
  FI.bounded (FI.mul (nat2p p) I J)
  /\
  diam (FI.mul (nat2p p) I J) <= 2*M * Rabs (diam I) + 2*M * Rabs (diam J) + 4 * M * M*  /2 ^ p.
Proof.
move => IB JB MI MJ.
split.
- move : IB JB MI MJ.
  case I => //; case => //lIm lIe; case => //uIm uIe _.
  case J => //; case => //lJm lJe; case => //uJm uJe _.
  move => [Ibl Ibu] [Jbl Jbu].
  apply /bounded_realP/andP;split.
  by case (upper_mul (nat2p p)  lIm lIe uIm uIe lJm lJe uJm uJe ) => h; rewrite real_correct h /FI.F.mul_UP mul_correct !toX_Float.
  by case (lower_mul (nat2p p)  lIm lIe uIm uIe lJm lJe uJm uJe ) => h; rewrite real_correct h /FI.F.mul_UP mul_correct !toX_Float.
- apply Rcomplements.Rle_minus_l.
  apply: (Rle_trans _ _ _ (mul_error_upper _ IB JB MI _)) => //.
  apply Rcomplements.Rle_minus_r.
  ring_simplify.
  rewrite  Rplus_comm.
  apply Rcomplements.Rle_minus_l.
  apply /Rle_trans/(mul_error_lower _ IB JB MI MJ).
  lra.
Qed.


Lemma inv_error (I : FI.type) M p:
  M > 0 ->
  FI.bounded I ->  
  (pos_bound I M \/ neg_bound I M) ->
  FI.bounded (FI.inv (nat2p p) I)
  /\
  diam (FI.inv (nat2p p) I) <=  4*(1/M) * / 2 ^ p + (1/M)*(1/M)*(Rabs (diam I)).
Proof.
case I => //; case => //lIm lIe; case => //uIm uIe M0 bnd Mp.
have Isgn  : FI.sign_strict_ (Float lIm lIe) (Float uIm uIe) = Xlt \/ FI.sign_strict_ (Float lIm lIe) (Float uIm uIe) = Xgt.
  rewrite /FI.sign_strict_ !cmp_correct !toX_Float /=.
  have -> : D2R (Float BigIntRadix2.mantissa_zero BigIntRadix2.exponent_zero) = 0.
    by rewrite D2R_Float /= /IZR/=;ring.
    case Mp => //= h.
      have -> := Raux.Rcompare_Gt; last by lra.
      have -> := Raux.Rcompare_Gt; last by lra.
      by right.
    have -> := Raux.Rcompare_Lt; last by lra.
    have -> := Raux.Rcompare_Lt; last by lra.
    by left.
have [invIl_bnd invIu_bnd] : Rabs (1/D2R (Float lIm lIe)) <= 1/M /\ Rabs (1/D2R (Float uIm uIe)) <= 1/M.
  rewrite !Rabs_mult Rabs_R1 /Rdiv !Rmult_1_l !Rabs_inv. 
  by split;apply Rinv_le_contravar =>//; apply Raux.Rabs_ge;case Mp => /=;lra.
have -> : FI.inv (nat2p p) (Ibnd (Float lIm lIe) (Float uIm uIe)) =  Ibnd (FI.F.div_DN (nat2p p) FI.c1 (Float uIm uIe)) (FI.F.div_UP (nat2p p) FI.c1 (Float lIm lIe)) by rewrite  /FI.inv/FI.Fdivz_UP;case Isgn => ->.
split.
- apply /bounded_realP.
  rewrite (real_correct (FI.upper _)) (real_correct (FI.lower _)) !div_correct /Basic.Xround /Xbind/proj_val !toX_Float /Basic.round /= /Xdiv'.
  by rewrite !is_zero_false //; case Mp => //=;lra.
- rewrite /FI.F.toR/proj_val ?toX_Float !div_correct /Basic.Xround/Xbind/proj_val !toX_Float /Basic.round /= /Xdiv' /=.
   rewrite !is_zero_false /=; try by case Mp => //=;lra.
   have -> : (D2R (Float (Pos (of_pos 1)) BigIntRadix2.exponent_zero)) = 1 by rewrite D2R_Float/to_Z spec_of_pos/=;ring.
   set x := D2R (Float lIm lIe).
   set y := D2R (Float uIm uIe).
   have b1 : Generic_fmt.round radix (FLX.FLX_exp (Z.pos (prec (nat2p p)))) Raux.Zceil (1 / x) <= 1/x + Rabs (1/x) * (2* / 2 ^ p).
     by apply Rcomplements.Rabs_le_between';apply generic_round_bnd;apply Generic_fmt.valid_rnd_UP.
   have b2 : 1/y - Rabs (1/y) * (2* / 2 ^ p) <= Generic_fmt.round radix (FLX.FLX_exp (Z.pos (prec (nat2p p)))) Raux.Zfloor (1 / y).
     by apply Rcomplements.Rabs_le_between';apply generic_round_bnd;apply Generic_fmt.valid_rnd_DN.
   apply: (Rle_trans _ (1/x + Rabs (1/x) * (2* /2 ^p) - (1/y - Rabs (1/ y) * (2/ 2^ p)))); first by lra.
   ring_simplify.
   have tpmn0 := tpmn_lt p.
   suff :  (1/x - 1 / y <= (1/ M)^2 * Rabs (y-x)) by rewrite /x/y;nra.
   rewrite Rcomplements.Rdiv_minus ?Rmult_1_l; try by rewrite /x/y; case Mp => /=;lra.
   apply (Rle_trans _ _ _ (Rle_abs _)).
   rewrite Rabs_mult /Rcomplements.Rabs_div Rmult_comm Rabs_inv Rabs_mult.
   apply Rmult_le_compat_r; first by apply Rabs_pos.
   rewrite Rinv_mult -!Rabs_inv.
   rewrite /x/y -!Rdiv_1_l.
   apply Rmult_le_compat; try lra; apply Rabs_pos.
Qed.
