From Stdlib Require Import Reals.
From Stdlib Require Import Lra Lia.
From HB Require Import structures.
From mathcomp Require Import reals all_ssreflect all_boot boolp all_order all_algebra ssrnum ssralg ssrnum mathcomp_extra matrix classical_sets ssrint.
From mathcomp Require Import Rstruct.

From mathcomp Require Import reals topology.
 From CoqEAL Require Import hrel param refinements trivial_seq. 
 From CoqEAL Require Import seqmx seqmx_complements binint binrat. 

From RocqRep Require Import spaces.efftop.
Import Order.Theory GRing.Theory Num.Theory.
(* Import Refinements.Op. *)
(* Local Open Scope ring_scope. *)
(* Local Open Scope hetero_computable_scope. *)

Local Open Scope classical_set_scope.
Section Matrix_rep.
Context {m n : nat} {X : effectiveTopZModType}.
Local Notation MX := 'M[X]_(m,n).
Definition MB := (@hseqmx (@nbhd_type X) m n).

Definition default_approx := name_fun (0 : X) zero_rlzr 0%nat.

Definition Mto_set (x: MB) : set MX :=  [set M  | forall i j, M i j \in (to_set (nth default_approx (nth [::] x (nat_of_ord i)) (nat_of_ord j)))]. 

Lemma  nbhd_base :
    forall x U, open U -> U x -> 
      exists b, interior (Mto_set b) x /\ Mto_set b `<=` U.
Proof.
move => M U Uopen Ux.
(* have [UM /= MP /= HU] : nbhs M U. *)
(*   by move: Uopen; rewrite openE => /(_ M Ux). *)
(* suff  /choice [phi_ij P] : forall ij, exists (q : @nbhd_type X), (to_set q)° (M ij.1 ij.2) /\ to_set q `<=` UM ij.1 ij.2.  *)
(* exists ([seq [seq phi_ij (i,  j) | j <- enum 'I_n] | i <- enum 'I_m]). *)
(* split. *)
(* admit. *)
(* rewrite /Mto_set/=. *)
(* move=>x  H. *)
(* apply HU. *)
(* apply set_mem. *)
(* apply H. *)
(* apply UM. *)
(* apply P. *)
(* suff /choice [phi_ij P] : forall ij, exists phi, phi |= M ij.1 ij.2. *)
(* exists (fun q => [seq [seq phi_ij (i,  j) q | j <- enum 'I_n] | i <- enum 'I_m]).   *)
(* by  exists (fun q => phi_ij q.2 q.1) => i j /=;apply P. *) 
(* Lemma repM_surjective : repM \is_surjective. *)
(* Proof. *)
(* move => M. *)
(* rewrite /repM. *)
(* suff /choice [phi_ij P] : forall ij, exists phi, phi |= M (inord ij.1) (inord ij.2) by  exists (fun q => phi_ij q.2 q.1) => i j /=;apply P. *)
(* move => [i j]. *)
(* exact: rep_total. *)
(* Qed. *)

(* Lemma repM_singlevalued : repM \is_singlevalued. *)
(* Proof. *)
(* move => phi x y phix phiy. *)
(* apply /matrixP => i j. *)
(* have := (rep_singlevalued _ _ _ (phix (val i) (val j))). *)
(* rewrite !inord_val. *)
(* apply => //=. *)
(* have := (phiy i j). *)
(* by rewrite !inord_val. *)
(* Qed. *)
Admitted.

Lemma mx_kolmogorov : kolmogorov_space MX.
Proof.
apply accessible_kolmogorov.
 apply hausdorff_accessible.
Admitted.

HB.instance Definition mx_efftop :=
  effectiveTopological.Build MX mx_kolmogorov MB Mto_set  nbhd_base.

Definition mx_entry (m : @nbhd_type MX) i j : @nbhd_type X :=  (nth default_approx (nth [::] m i) j).
Definition mx_name_entry (phi : names MX) i j : names X := fun q => (nth default_approx (nth [::] (phi q) i) j).
Lemma mx_nameP (x : MX) phi : phi |= x <-> forall (i : 'I_m) (j : 'I_n), mx_name_entry phi (nat_of_ord i) (nat_of_ord j) |= x i j.
Proof.
Admitted.

 Notation tmx := (seq (seq (@names X))). 
 Definition zero : (@names X) := name_fun _ zero_rlzr.
Definition mx_from_seq (phi : tmx ) : names MX   := fun q => [seq [seq (nth zero (nth [::] phi j) i) q | j <- iota 0 n ] |  i <- iota 0 m].

Definition mx_from_fun (phi : nat -> nat -> @names X ) : names MX   := fun q => [seq [seq phi i j q | j <- iota 0 n ] |  i <- iota 0 m].

Lemma mx_from_fun_entry (phi : nat -> nat -> @names X ) i j : mx_name_entry (mx_from_fun phi) i j = phi i j.
Admitted.

Definition mx_name_from_fun {f : nat -> nat -> X} (phi : forall n m, name_of (f n m) ) : name_of (\matrix_(i,j) f i j).
Proof.
refine {| name_fun := mx_from_fun (fun n m => (name_fun _ (phi n m)))|}.
apply /mx_nameP => i j. 
rewrite mxE.
rewrite mx_from_fun_entry.
apply phi.
Defined.
(* Definition mx_query (phi : names MX)  : tmx := *)
(*   mkseq (fun i => *)
(*     mkseq (fun j => fun q => phi (q, (i,j))) n.+1) m.+1. *)


End Matrix_rep.

Section Matrix_ops.

Context {m n : nat} {X : effectiveTopZModType}.
Local Notation MX := 'M[X]_(m,n).
Local Notation MX_t := 'M[X]_(n,m).

Lemma transpose_name (phi : names MX) i j : mx_name_entry (m:=n) (n:=m) (fun q : nat => trmx_seqmx (m:=m) (n:=n) (phi q)) i j = mx_name_entry phi j i.
Proof.
  rewrite /mx_entry.
  apply funext => q.
Admitted.

Definition transpose_rlzr : rlzr_of ((fun (x : MX) => (x^T)%R)).
Proof.
refine {| rlzr_fun := fun q (x : @nbhd_type MX) =>  trmx_seqmx (m:=m) (n:=n) x : @nbhd_type MX_t |}.
move => x phi /mx_nameP h.
apply /mx_nameP => i j.
rewrite /lift_rlzr.
rewrite mxE.
rewrite transpose_name.
exact: h.
Defined.

End Matrix_ops.
Section MatrixZmod.
Context {m n : nat} {X : repNzRingType}.
Local Notation MX := 'M[X]_(m,n).

Lemma mx_entry_fun  f i j: mx_name_entry (X:=X) (n:=n) (m:=m) (mx_from_fun f) i j = f i j.
Proof.
Admitted.

Definition zeromx_name : name_of (0 : MX).
Proof.
refine {|
    name_fun := mx_from_fun (fun i j => name_fun _ zero_rlzr)
  |}.
apply /mx_nameP => i j.
rewrite mx_entry_fun.
rewrite mxE.
apply name_correct.
Defined.

Definition addmx_rlzr_fun (q : nat) (p p' : @nbhd_type MX) : @nbhd_type MX := [seq [seq (rlzr2_fun _ add_rlzr n (mx_entry p i j) (mx_entry p' i j)) | j <- iota 0 n] | i <- iota 0 m].

Lemma addmx_rlzr_correct phi1 phi2 x y :   phi1 |= x -> phi2 |= y ->  lift_rlzr2 addmx_rlzr_fun phi1 phi2 |= x + y.
Admitted.

Definition addmx_rlzr : rlzr2_of (fun (x y : MX) => (Algebra.add x y)).
Proof.
refine {|
    rlzr2_fun := addmx_rlzr_fun
  |}.
move => x y phi1 phi2.
exact: addmx_rlzr_correct.
Defined.

Definition oppmx_rlzr_fun (q : nat) (p : @nbhd_type MX) : @nbhd_type MX := [seq [seq (rlzr_fun _ opp_rlzr n (mx_entry p i j)) | j <- iota 0 n] | i <- iota 0 m].

Lemma oppmx_rlzr_correct phi x  :   phi |= x ->  lift_rlzr oppmx_rlzr_fun phi |= (-x).
Admitted.

Definition oppmx_rlzr : rlzr_of (fun (x : MX) => (Algebra.opp x)).
Proof.
refine {|
    rlzr_fun := oppmx_rlzr_fun
  |}.
move => x phi.
exact: oppmx_rlzr_correct.
Defined.

HB.instance Definition mx_effzmod := repTopZModule.Build MX zeromx_name addmx_rlzr oppmx_rlzr.
End MatrixZmod.


(* Local Notation Q := (@queries X * (nat * nat))%type. *)
(* Local Notation A :=  (@answers X). *)
(* Local Notation MX := 'M[X]_(m.+1,n.+1). *)

(* Open Scope rep_scope. *)

(* Definition mx_zero_rlzr (q : Q) : A:= 0 (q.1). *)


(* Lemma mx_zero_rlzr_spec : mx_zero_rlzr |= (0%R : MX). *)
(* Proof. *)
(* rewrite /mx_zero_rlzr => -i j /=. *)
(* rewrite mxE. *)
(* exact: zero_nameP. *)
(* Qed. *)

(* Definition mx_add_rlzr phi1 phi2 (q : Q) : A := ((fun p => (phi1 (p, (q.2.1, q.2.2)))) + (fun p => (phi2 (p, (q.2.1, q.2.2))))) q.1. *)

(* Lemma mx_add_rlzr_spec px py (x y : MX) : px |= x -> py |= y -> (mx_add_rlzr px py) |= (x+y)%R.  *)
(* Proof. *)
(* move => n1 n2. *)
(* rewrite /mx_add_rlzr => i j /=. *)
(* rewrite !mxE/=. *)
(* by apply add_nameP. *)
(* Qed. *)

(* Definition mx_opp_rlzr phi1 (q : Q) : A := (- (fun p => (phi1 (p, (q.2.1, q.2.2))))) q.1. *)

(* Lemma mx_opp_rlzr_spec px (x : MX) : px |= x -> (mx_opp_rlzr px) |= (-x)%R. *)
(* Proof. *)
(* move => n1 n2. *)
(* rewrite /mx_opp_rlzr => i /=. *)
(* rewrite mxE/=. *)
(* by apply opp_nameP. *)
(* Qed. *)


(* HB.instance Definition mx_isRepZmod := *)
(*   isRepZmod.Build MX mx_zero_rlzr_spec mx_add_rlzr_spec mx_opp_rlzr_spec. *)

(* Definition mx_diag (phi : names MX) : names MX := (fun q => if (q.2.1 =? q.2.2) then (phi (q.1, (q.2.2,q.2.1))) else (0 q.1)). *)
(* End MatrixZmod. *)

(*todo : move to own file *)
(* Section MatrixMult. *)
(* Context {m n p : nat} {X : repComRingType}. *)
(* Local Notation MX := 'M[X]_(m.+1,n.+1). *)
(* Local Notation MY := 'M[X]_(n.+1,p.+1). *)
(* Local Notation MZ := 'M[X]_(m.+1,p.+1). *)
(* Open Scope rep_scope. *)
(* Definition mx_mult_rlzr (phi1 : names MX) (phi2 : names MY) : names MZ := *)
(*   fun q => ((\sum_(i < n.+1) ((mx_entry phi1 (q.2.1) i) * (mx_entry phi2 i (q.2.2))))%rep q.1). *)

(* Opaque sum_rlzr. *)
(* Lemma mx_mult_rlzr_spec phi1 phi2 (x : MX) (y : MY) : phi1 |= x -> phi2 |= y -> mx_mult_rlzr phi1 phi2 |= (x *m y)%R. *)
(* Proof. *)
(* move => name1 name2. *)
(* rewrite /mx_mult_rlzr => i j. *)
(* rewrite mxE/=. *)
(* suff -> : (\sum_(j0 < n.+1) x (inord i) j0 * y j0 (inord j))%R = (\sum_(j0 < n.+1) x (inord i) (inord j0) * y (inord j0) (inord j))%R. *)
(*   apply (sum_rlzr_spec (fun i0 => (mx_entry phi1 i i0) * (mx_entry phi2 i0 j)) (fun i0 => ((x (inord i) (inord i0)) * y (inord i0) (inord j)))%R). *)
(*   move => k k0. *)
(*   by rewrite /mx_entry; apply mul_nameP. *)
(* apply congr1; apply funext => k /=. *)
(* by rewrite inord_val. *)
(* Qed. *)

(* Definition mx_smult_rlzr (phix : names X) (phiM : names MX) : names MX := fun q => (phix * mx_entry phiM q.2.1 q.2.2) q.1. *)

(* Lemma mx_smult_rlzr_spec phix phiM (x : X) (M : MX) : phix |= x -> phiM |= M -> mx_smult_rlzr phix phiM |= (x *: M)%R. *)
(* Proof. *)
(* move => name1 name2. *)
(* rewrite /mx_smult_rlzr => i j. *)
(* rewrite mxE/=. *)
(* rewrite /mx_entry. *)
(* by apply mul_nameP. *)
(* Qed. *)

(* Transparent sum_rlzr. *)
(* End MatrixMult. *)

(* Notation "x *m y" := (mx_mult_rlzr x y) : rep_scope. *)
(* Notation "x *: y" := (mx_smult_rlzr x y) : rep_scope. *)
(* Notation "x ^T" := (mx_transpose_rlzr x) : rep_scope. *)
