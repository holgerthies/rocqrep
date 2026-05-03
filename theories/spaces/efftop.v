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

Local Open Scope classical_set_scope.

Section BasisRepresentation.
Context {X : topologicalType}.
Context {nbhd_type : countType} {to_set : nbhd_type -> set X}.

Hypothesis T0X : kolmogorov_space X.
Hypothesis  nbhd_base :
    forall x U, open U -> U x -> 
      exists b, interior (to_set b) x /\ to_set b `<=` U.

Local Lemma nbhd_directed :
  forall x b1 b2,(interior (to_set b1)) x -> (interior (to_set b2)) x ->
    exists b3, interior (to_set b3) x /\ to_set b3 `<=`  (to_set b1) `&` (to_set b2).
Proof.
move => x b1 b2 t1 t2.
case (nbhd_base x ((to_set b1)° `&` (to_set b2)°)).
  by apply openI; apply open_interior.
  by split => //.
move => b [Hb1 Hb2].
 exists b.
split=>//.
apply (subset_trans Hb2).
by split; apply interior_subset;apply H.
Qed.

Definition repX := fun (name : nat -> nbhd_type) (x : X) => (forall n, (to_set (name n) x)) /\ (forall U, open U -> U x -> exists N, forall n, (N <= n)%nat -> to_set (name n) `<=` U).

Lemma repX_surjective : repX \is_surjective.
Proof.
move => x.
set  xsets  :=   [set b | interior (to_set b) x].
case : (nbhd_base x setT) => //[| b0 [ b0x _]]; first by apply openT.
set nth_set := (fun n => (match (@unpickle nbhd_type n) with
          | Some b => if (b \in xsets) then b else b0
          | _ => b0
          end)).
have H0 : forall n, interior (to_set (nth_set n)) x.
   by rewrite /nth_set => n;case (unpickle n) => // -s;case: ifP => //;rewrite inE.
have /choice [f Pf] : forall n, exists b, interior (to_set b) x /\ forall m, (m <= n)%nat -> to_set b `<=` to_set (nth_set m).
  move=>n.
  elim: n => [| n IH].
    by exists (nth_set 0);split=> // m mp; have -> : (m = 0)%nat by lia.
  have [bn [Bn1 Bn2]] := IH. 
  have [i [I1 I2]] := nbhd_directed _ _ _ Bn1 (H0 n.+1).
  exists i;split=>// m mp.
  apply (subset_trans I2).
  apply subIset.
  move : mp.
  rewrite leq_eqVlt => /orP[/eqP -> | hlt].
  by right.
  by left;apply Bn2.
exists f.
split=>U; first by apply interior_subset;apply Pf.
move => Uopen Ux.
have [b1 [ b1x b1U]] := nbhd_base _ _ Uopen Ux.
exists (pickle b1).
move => n np.
have [_ +]:= Pf n.
move /(_ _ np);move /subset_trans;apply.
rewrite /nth_set.
rewrite pickleK.
by have -> : (b1 \in xsets) by rewrite inE.
Qed.

Lemma repX_singlevalued : repX \is_singlevalued.
Proof.
move=>phi1 x y [c1 s1] [c2 s2].
have /contra_not_eq  := (T0X x y).
apply.
apply /forallNP => U0.
rewrite not_orP !not_andP  !in_setC !notin_setE !not_notE -!implyE !inE.
split => U0nbhs; suff [n P] : exists N, forall n, (N <= n)%nat ->  to_set (phi1 n) `<=` interior U0 by apply interior_subset;apply (P n).
by apply s1;first by apply open_interior.
by apply s2;first by apply open_interior.
Qed.

(* HB.instance Definition normedSpace_isRepSpace  := *)
(*   isRepSpace.Build X repX_surjective repX_singlevalued. *)

(* HB.instance Definition normedSpace_isRepSpace (X : normedModType R) B Bs H := *)
(*   isRepSpace.Build X (repX_surjective _ _ H) (repX_singlevalued B Bs). *)
End BasisRepresentation.


HB.mixin Record effectiveTopological T of Topological T := 
{
  kolmogorov: kolmogorov_space T;
  nbhd_type : countType;
  to_set : nbhd_type -> set T;
  nbhd_base : forall x U, open U -> U x ->
                     exists b, interior (to_set b) x /\ to_set b `<=` U;

}.
#[short(type="effectiveTopType")]
HB.structure Definition effectiveTop := { T of Topological T & effectiveTopological T }.

Definition is_top_name {T : effectiveTopType} (phi : nat -> @nbhd_type T) (x :T) := repX (to_set := @to_set T) phi x.   
Notation "phi '|=' x" := (is_top_name phi x) (at level 70).

Record name_of {X : effectiveTopType} (x : X) := {
    name_fun : nat -> (@nbhd_type X);
    name_correct : (is_top_name name_fun x)
  }. 


Definition names (T : effectiveTopType) := nat -> (@nbhd_type T).

Definition lift_rlzr {X Y : effectiveTopType} (F : nat -> (@nbhd_type X) -> (@nbhd_type Y)) := fun (x : names X) n => F n (x n).

Definition lift_rlzr2 {X Y Z : effectiveTopType} (F : nat -> (@nbhd_type X) -> (@nbhd_type Y) -> (@nbhd_type Z)) := fun (x : names X) (y : names Y) n => F n (x n) (y n).

Record rlzr_of {X Y: effectiveTopType} (f : X -> Y) := {
    rlzr_fun : nat -> (@nbhd_type X) -> (@nbhd_type Y);
    rlzr_correct : forall x phi, (is_top_name phi x) -> (is_top_name (lift_rlzr rlzr_fun phi) (f x))
  }.

Record rlzr2_of {X Y Z: effectiveTopType} (f : X -> Y -> Z) := {
    rlzr2_fun :  nat -> (@nbhd_type X) -> (@nbhd_type Y)  -> (@nbhd_type Z);
    rlzr2_correct : forall x y phi1 phi2, (is_top_name phi1 x) -> (is_top_name phi2 y) -> (is_top_name (lift_rlzr2 rlzr2_fun phi1 phi2) (f x y))
  }.

HB.mixin Record repTopZModule T of effectiveTopological T & TopologicalZmodule T := {
   zero_rlzr : name_of (0 : T); 
   add_rlzr : rlzr2_of (fun (x y : T) => x + y);
   opp_rlzr : rlzr_of (fun (x : T) => (- x)); 
}.
#[short(type="effectiveTopZModType")]
HB.structure Definition effectiveTopZMod := { T of Topological T & effectiveTopological T & repTopZModule T}.

HB.mixin Record isRepNzRing T of GRing.NzRing T & effectiveTopZMod T := {
  one_rlzr : name_of (1 : T);
  mul_rlzr : rlzr2_of (fun (x y : T) => x * y)
}.
#[short(type="repNzRingType")]
HB.structure Definition RepNzRing :=
{ T of Topological T & effectiveTopological T & repTopZModule T & GRing.NzRing T & isRepNzRing T}.

HB.mixin Record isRepField T of GRing.Field T & RepNzRing T := {
    inv_rlzr_fun : nat -> (@nbhd_type T) -> (@nbhd_type T);
    inv_rlzr_correct : forall x phi, x != 0 -> (is_top_name phi x) -> (is_top_name (lift_rlzr inv_rlzr_fun phi) (GRing.inv x))
}.
#[short(type="repFieldType")]
HB.structure Definition RepField :=
{ T of Topological T & effectiveTopological T & repTopZModule T & GRing.NzRing T & isRepNzRing T & GRing.Field T & isRepField T}.

Definition compose_rlzr {X Y Z : effectiveTopType} (f : Y -> Z) (g : X -> Y ) (F : rlzr_of f) (G : rlzr_of g) : rlzr_of (fun x => f (g x)).
Proof.
refine {|
   rlzr_fun := (fun n x => F.(rlzr_fun f) n (G.(rlzr_fun g) n x)) 
  |}.
move => x phi n1.
by do 2 apply rlzr_correct.
Qed.

Definition compose_rlzr21 {X X' Y Z : effectiveTopType} (f : X -> Y -> Z) (g : X' -> X) (F : rlzr2_of f) (G : rlzr_of g) : rlzr2_of (fun x y => f (g x) y).
Proof.
refine {|
   rlzr2_fun := (fun n x y => F.(rlzr2_fun f) n (G.(rlzr_fun g) n x) y) 
  |}.
move => x y phi1 phi2 n1 n2.
apply rlzr2_correct => //.
by apply rlzr_correct.
Qed.

Definition compose_rlzr22 {X Y Y' Z : effectiveTopType} (f : X -> Y' -> Z) (g : Y -> Y') (F : rlzr2_of f) (G : rlzr_of g) : rlzr2_of (fun x y => f x (g y)).
Proof.
refine {|
   rlzr2_fun := (fun n x y => F.(rlzr2_fun f) n x (G.(rlzr_fun g) n y)) 
  |}.
move => x y phi1 phi2 n1 n2.
apply F.(rlzr2_correct _) => //.
by apply G.(rlzr_correct _).
Defined.

Definition eval_rlzr {X Y : effectiveTopType}  {x : X} {f : X -> Y} (F : rlzr_of f ) (phi : name_of x)  : name_of (f x).
Proof.
refine {| name_fun := lift_rlzr F.(rlzr_fun _) phi.(name_fun _)|}.
apply F.(rlzr_correct _).
apply phi.(name_correct _).
Defined.

Definition eval_rlzr2 {X Y Z : effectiveTopType}  {x : X} {y : Y} {f : X -> Y -> Z} (F : rlzr2_of f)  (phi1 : name_of x) (phi2 : name_of y)  : name_of (f x y).
Proof.
refine {| name_fun := lift_rlzr2 F.(rlzr2_fun _) phi1.(name_fun _) phi2.(name_fun _)|}.
apply F.(rlzr2_correct _).
apply phi1.(name_correct _).
apply phi2.(name_correct _).
Defined.

Definition inv_name {X : repFieldType} {x : X} (phi : name_of x): x != 0 -> name_of (GRing.inv x).
Proof.
move=>h.
refine {|name_fun := lift_rlzr inv_rlzr_fun phi.(name_fun _) |}.
apply inv_rlzr_correct => //.
apply name_correct.
Defined.

Coercion eval_rlzr : rlzr_of >-> Funclass.
Coercion eval_rlzr2 : rlzr2_of >-> Funclass.

Module Type EFFTOP_PARAMS.
Parameter index : nat.
End EFFTOP_PARAMS.

Module Type EFFTOP_OBJECT.
  Parameter T : repNzRingType.
End EFFTOP_OBJECT.

Module Type EFFTOP_FIELD_OBJECT.
  Parameter T : repFieldType.
End EFFTOP_FIELD_OBJECT.

Module EffectiveTop (params : EFFTOP_PARAMS).
Module ForRing (O : EFFTOP_OBJECT).
Definition X := O.T.
Definition n := params.index.
Local Definition nbhds := @nbhd_type X.

Record ApproximationOf  (x : X) :=
 {
   phi : name_of x;
   approx_val : nbhds;
   approx_spec : approx_val = name_fun _ phi n
 }.

Arguments approx_val {x} _.
Coercion approx_val : ApproximationOf >-> Countable.sort.

Definition one_approx : ApproximationOf 1.
Proof.
  by refine {| phi := one_rlzr; approx_val :=  name_fun _ one_rlzr n |}.
Defined.

Definition zero_approx : ApproximationOf 0.
Proof.
  by refine {| phi := zero_rlzr; approx_val :=  name_fun _ zero_rlzr n |}.
Defined.

Definition add_approx {x y} (p : ApproximationOf x) (q : ApproximationOf y): ApproximationOf (x+y).
Proof.
  refine {| approx_val := rlzr2_fun _ add_rlzr n (approx_val p) (approx_val q); phi := add_rlzr (phi _ p) (phi _ q)  |}.
  by rewrite !approx_spec.
Defined.

Definition opp_approx {x} (p : ApproximationOf x) : ApproximationOf (-x).
Proof.
  refine {| approx_val := rlzr_fun _ opp_rlzr n (approx_val p); phi := opp_rlzr (phi _ p)  |}.
  by rewrite !approx_spec.
Defined.

Definition mul_approx {x y} (p : ApproximationOf x) (q : ApproximationOf y): ApproximationOf (x*y).
Proof.
  refine {| approx_val := rlzr2_fun _ mul_rlzr n (approx_val p) (approx_val q); phi := mul_rlzr (phi _ p) (phi _ q)  |}.
  by rewrite !approx_spec.
Defined.

Definition approx_of_name {x} (p : name_of x) : ApproximationOf x.
Proof.
  by refine {| approx_val := name_fun _ p n|}.
Defined.

Coercion approx_of_name : name_of >-> ApproximationOf.

Declare Scope rep_scope.
Delimit Scope rep_scope with CT.
Notation "0" := (zero_approx  ) : rep_scope. 
Notation "1" := (one_approx ) : rep_scope. 
Notation "- x" := (opp_approx x) : rep_scope. 
Notation "x + y" :=  (add_approx x y) : rep_scope.
Notation "x - y" := (x + (-y))%CT : rep_scope. 
Notation "x * y" :=  (mul_approx x y) : rep_scope.
End ForRing.

Module ForField (O : EFFTOP_FIELD_OBJECT).
 Module RingObj.
    Definition T : repNzRingType := O.T.
  End RingObj.
Include ForRing(RingObj).
Definition inv_approx {x} (p : ApproximationOf x): x != 0 -> ApproximationOf (GRing.inv x).
Proof.
move=>h.
refine {| approx_val :=  inv_rlzr_fun n (approx_val p); phi := inv_name (phi _ p)   h |}.
  by rewrite !approx_spec.
Defined.
Notation "y ^-1" :=  (inv_approx y) : rep_scope.
Notation "x %/ y" :=  (x * y^-1)%CT : rep_scope.
End ForField.

End EffectiveTop.
(* Definition eval_name {X : effectiveTopType} {x : X} (phi : name_of x ) := phi.(name_fun x) params.index. *)
(* (* Definition eval_rlzr {X Y : effectiveTopType}  {f : X -> Y} (F : rlzr_of f ) := F.(rlzr_fun f) params.index. *) *)
(* (* Definition eval_rlzr2 {X Y Z: effectiveTopType} {f : X -> Y -> Z} (F : rlzr2_of f ) := F.(rlzr2_fun f) params.index. *) *)


(* Coercion name_to_base *)
(*   {X : effectiveTopType} {x : X} *)
(*   (phi : name_of x) : @nbhd_type X := (eval_name phi). *)
(* End EffectiveTop. *)


