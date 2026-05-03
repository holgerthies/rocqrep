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
Import Refinements.Op.
Local Open Scope ring_scope.
Local Open Scope hetero_computable_scope.

Local Open Scope classical_set_scope.
Section Matrix_rep.
Context {m n : nat} {X : effectiveTopType}.
Context {zero : X}.
Local Notation MX := 'M[X]_(m,n).
Local Notation MB := (@hseqmx (@nbhd_type X) m n).
Instance spec_X : spec_of (@nbhd_type X) (set X) := to_set. 

#[local] Instance set_zero : zero_of (set X) := set0.


Definition to_set (x: MB) : set MX:= set0.
(* @spec_seqmx (set X) _ _ spec_X m n x. *)
(* Check to_set. *)
Lemma  nbhd_base :
    forall (x :MX)  U, open U -> U x -> 
      exists b, to_set b x /\ to_set b `<=` U.
Proof.
move => x U Uopen Ux.
Lemma nbhd_base 
Lemma repM_surjective : repM \is_surjective.
Proof.
move => M.
rewrite /repM.
suff /choice [phi_ij P] : forall ij, exists phi, phi |= M (inord ij.1) (inord ij.2) by  exists (fun q => phi_ij q.2 q.1) => i j /=;apply P.
move => [i j].
exact: rep_total.
Qed.

Lemma repM_singlevalued : repM \is_singlevalued.
Proof.
move => phi x y phix phiy.
apply /matrixP => i j.
have := (rep_singlevalued _ _ _ (phix (val i) (val j))).
rewrite !inord_val.
apply => //=.
have := (phiy i j).
by rewrite !inord_val.
Qed.

HB.instance Definition matrixSpace_isRepSpace :=
  isRepSpace.Build MX repM_surjective repM_singlevalued.
Notation tmx := (seq (seq (@names X))).
Definition mx_from_seq {c} (phi : tmx) : names MX   := fun qij => (nth (fun q => c) (nth [::] phi qij.2.1) qij.2.2) qij.1.

Definition mx_query (phi : names MX)  : tmx :=
  mkseq (fun i =>
    mkseq (fun j => fun q => phi (q, (i,j))) n.+1) m.+1.

Definition mx_entry (phi : names MX) i j : names X := fun q => (phi (q, (i,j))).

End Matrix_rep.

Section Matrix_ops.

Context {m n : nat} {X : repType}.
Local Notation MX := 'M[X]_(m.+1,n.+1).
Local Notation MX_t := 'M[X]_(n.+1,m.+1).

Definition mx_transpose_rlzr (phi : names MX) : names MX_t := (fun q => (phi (q.1, (q.2.2,q.2.1)))).

Lemma mx_transpose_rlzr_spec phi (x : MX) : phi |= x -> mx_transpose_rlzr phi |= (x^T)%R.
Proof.
rewrite /mx_transpose_rlzr => -h i j /=.
rewrite mxE.
exact: h.
Qed.

End Matrix_ops.

Section MatrixZmod.
Context {m n : nat} {X : repZmodType}.
Local Notation Q := (@queries X * (nat * nat))%type.
Local Notation A :=  (@answers X).
Local Notation MX := 'M[X]_(m.+1,n.+1).

Open Scope rep_scope.

Definition mx_zero_rlzr (q : Q) : A:= 0 (q.1).


Lemma mx_zero_rlzr_spec : mx_zero_rlzr |= (0%R : MX).
Proof.
rewrite /mx_zero_rlzr => -i j /=.
rewrite mxE.
exact: zero_nameP.
Qed.

Definition mx_add_rlzr phi1 phi2 (q : Q) : A := ((fun p => (phi1 (p, (q.2.1, q.2.2)))) + (fun p => (phi2 (p, (q.2.1, q.2.2))))) q.1.

Lemma mx_add_rlzr_spec px py (x y : MX) : px |= x -> py |= y -> (mx_add_rlzr px py) |= (x+y)%R. 
Proof.
move => n1 n2.
rewrite /mx_add_rlzr => i j /=.
rewrite !mxE/=.
by apply add_nameP.
Qed.

Definition mx_opp_rlzr phi1 (q : Q) : A := (- (fun p => (phi1 (p, (q.2.1, q.2.2))))) q.1.

Lemma mx_opp_rlzr_spec px (x : MX) : px |= x -> (mx_opp_rlzr px) |= (-x)%R.
Proof.
move => n1 n2.
rewrite /mx_opp_rlzr => i /=.
rewrite mxE/=.
by apply opp_nameP.
Qed.


HB.instance Definition mx_isRepZmod :=
  isRepZmod.Build MX mx_zero_rlzr_spec mx_add_rlzr_spec mx_opp_rlzr_spec.

Definition mx_diag (phi : names MX) : names MX := (fun q => if (q.2.1 =? q.2.2) then (phi (q.1, (q.2.2,q.2.1))) else (0 q.1)).
End MatrixZmod.

(*todo : move to own file *)
Section Sum.
Context {X : repZmodType}.
Fixpoint sum_rlzr (F : nat -> names X) n := match n with
                                           | 0%nat => 0%rep
                                           | n'.+1 => (sum_rlzr F n' + F n')%rep
                                         end.
Notation "\sum_ ( i < n ) F" :=
  (sum_rlzr (fun i => F) n) (at level 34, i at level 60, n at level 60, F at level 41) : rep_scope.
Local Open Scope ring_scope.
Lemma sum_rlzr_spec (F: nat -> names X) (G : nat -> X) (n : nat) : (forall i, (i < n)%nat  -> F i |= G i) -> (\sum_(i < n) F i)%rep |= (\sum_(i < n) G i).
Proof.
move => h.
induction n; first by rewrite big_ord0;exact: zero_nameP.
rewrite big_ord_recr /=.
apply add_nameP; first apply IHn => i hi.
  by apply h;rewrite ltnS; apply ltnW.
apply h.
by apply ltnSn.
Qed.
End Sum.

Notation "\sum_ ( i < n ) F" :=
  (sum_rlzr (fun i => F) n) (at level 34, i at level 60, n at level 60, F at level 41) : rep_scope.
Section MatrixMult.
Context {m n p : nat} {X : repComRingType}.
Local Notation MX := 'M[X]_(m.+1,n.+1).
Local Notation MY := 'M[X]_(n.+1,p.+1).
Local Notation MZ := 'M[X]_(m.+1,p.+1).
Open Scope rep_scope.
Definition mx_mult_rlzr (phi1 : names MX) (phi2 : names MY) : names MZ :=
  fun q => ((\sum_(i < n.+1) ((mx_entry phi1 (q.2.1) i) * (mx_entry phi2 i (q.2.2))))%rep q.1).

Opaque sum_rlzr.
Lemma mx_mult_rlzr_spec phi1 phi2 (x : MX) (y : MY) : phi1 |= x -> phi2 |= y -> mx_mult_rlzr phi1 phi2 |= (x *m y)%R.
Proof.
move => name1 name2.
rewrite /mx_mult_rlzr => i j.
rewrite mxE/=.
suff -> : (\sum_(j0 < n.+1) x (inord i) j0 * y j0 (inord j))%R = (\sum_(j0 < n.+1) x (inord i) (inord j0) * y (inord j0) (inord j))%R.
  apply (sum_rlzr_spec (fun i0 => (mx_entry phi1 i i0) * (mx_entry phi2 i0 j)) (fun i0 => ((x (inord i) (inord i0)) * y (inord i0) (inord j)))%R).
  move => k k0.
  by rewrite /mx_entry; apply mul_nameP.
apply congr1; apply funext => k /=.
by rewrite inord_val.
Qed.

Definition mx_smult_rlzr (phix : names X) (phiM : names MX) : names MX := fun q => (phix * mx_entry phiM q.2.1 q.2.2) q.1.

Lemma mx_smult_rlzr_spec phix phiM (x : X) (M : MX) : phix |= x -> phiM |= M -> mx_smult_rlzr phix phiM |= (x *: M)%R.
Proof.
move => name1 name2.
rewrite /mx_smult_rlzr => i j.
rewrite mxE/=.
rewrite /mx_entry.
by apply mul_nameP.
Qed.

Transparent sum_rlzr.
End MatrixMult.

Notation "x *m y" := (mx_mult_rlzr x y) : rep_scope.
Notation "x *: y" := (mx_smult_rlzr x y) : rep_scope.
Notation "x ^T" := (mx_transpose_rlzr x) : rep_scope.
