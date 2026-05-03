Require Import Interval.Interval.Float.        
Require Import Interval.Float.Specific_ops.    
Require Import Interval.Float.Specific_bigint. 
Require Import Bignums.BigQ.BigQ Bignums.BigZ.BigZ.
From mathcomp Require Import reals rat ssrnum all_ssreflect all_algebra Rstruct ssrZ.
From mathcomp Require Import all_boot all_order ssralg ssrnum mathcomp_extra.

Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.
From RocqRep Require Import interval_counttype.
Notation I := FI.type.
Definition F := SFBI2.type.
(* interval string operations, should be moved *)

Require Import List.
Require Import String.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.

Section interval_string.
Local Open Scope string_scope.
Definition ZtoStr (z : Z) := NilZero.string_of_int (Z.to_int z).
Definition PostoStr z := NilZero.string_of_int (Pos.to_int z).

Definition decimal_to_string (num : positive) (denum : positive) : string.
Proof.
   destruct (Z.div_eucl (Z.pos num) (Z.pos denum)) as [d r].
   remember (r + (Z.pos denum))%Z as rn.
   apply ((ZtoStr d) ++ "." ++ (substring 1 (length (ZtoStr rn)) (ZtoStr rn))).
 Defined.


Definition decimal_rat_to_string (num : Z) (denum : positive) : string.
Proof.
destruct num.
apply ("0" : string).
apply (decimal_to_string p denum).
apply ("-" ++ (decimal_to_string p denum)).
Defined.

Definition output_bound_to_string (b : Interval.output_bound) : string.
Proof.
  destruct b.
  - apply (ZtoStr z).
  - destruct q.
    destruct Qnum.
    apply ("0" : string).
    apply (decimal_to_string p Qden).
    apply ("-" ++ (decimal_to_string p Qden)).
  - apply (append (ZtoStr z) (append "/"  (ZtoStr z0))).
Defined.
Definition interval_to_string (i : I) : string.
Proof.
  destruct (FI.output true i) as [l r].
  destruct l as [l |];[|apply ("None" : string)].
  destruct r as [r | ]; [|apply ("None" : string)].
  remember ((output_bound_to_string l)) as ls.
  remember ((output_bound_to_string r)) as rs.
  apply  ("⟦" ++ ls ++ "," ++ rs ++ "⟧" ).
Defined.

Definition output_bnd_float
  (digits : positive) (upp : bool)  (s : bool) (m : positive) (e : Z)
  : Z :=
  let m0 := if s then Z.neg m else Z.pos m in
  match e with
  | 0%Z =>  m0 * Zaux.Zfast_pow_pos 10 digits 
  | Z.pos p => m0 * Zaux.Zfast_pow_pos 2 p * Zaux.Zfast_pow_pos 10 digits 
  | Z.neg p =>
  let m' := (m0 * Zaux.Zfast_pow_pos 5 digits)%Z in
   match (Z.pos p - Z.pos digits) with
   | 0%Z => m'      
   | Z.neg p0 => m' * Zaux.Zfast_pow_pos 2 p0
   | Z.pos p0 =>
      let q  := Zaux.Zfast_pow_pos 2 p0 in
      let m'' := Z.div_eucl m' q in
      let u :=
    if upp then if (m''.2 =? 0)%Z then 0%Z else 1%Z else 0%Z in
  m''.1 + u
   end
 end.
Definition interval_to_cr_string  (i : I) (digits: positive) : string.
Proof.
destruct i as [| l r];[apply ("None" : string)|].
set zl := match (FI.F.toF l) with Basic.Float b p z => (output_bnd_float digits false b p z) | _ => 0%Z end.
set zr := match (FI.F.toF r) with Basic.Float b p z => (output_bnd_float digits true b p z) | _ => 0%Z end.
set center := (5*(zl+zr))%Z.
set r1 := (center - 10*zl)%Z.
set r2 := (10*zr - center)%Z.
set radius:=Z.max r1 r2.
set d := Z.to_pos (Zaux.Zfast_pow_pos 10 (digits+1)).
set center_string := decimal_rat_to_string center d.
set radius_string := decimal_rat_to_string radius d.
apply  (center_string ++ "±" ++ radius_string).
Defined.

End interval_string.
