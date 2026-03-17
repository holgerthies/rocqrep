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
Module FI   := FloatInterval SFBI2.         
Import Interval.Real.Xreal.
Import GRing.Theory Num.Theory.
Import BigN BigZ.

HB.instance Definition _ := Countable.copy Cyclic63.Uint63Cyclic.t (can_type Uint63Axioms.of_to_Z).

Definition zn2z_pickle {t: countType} (w : DoubleType.zn2z t) : option (t * t) :=
  match w with
  | DoubleType.W0 => None
  | DoubleType.WW x y => Some (x,y)
   end.

Definition zn2z_unpickle {t: countType} (n : option (t * t)) :=
  match n with
  | None => DoubleType.W0
  | Some (x,y) => DoubleType.WW x y
  end.
             
Lemma zn2z_pickleK {t: countType} : cancel (zn2z_pickle (t:=t)) zn2z_unpickle.
Proof. by move => [| z1 z2] /=. Qed.

HB.instance Definition _ {t: countType} := Countable.copy (DoubleType.zn2z t) (can_type zn2z_pickleK).



Definition pickle_word  {n : nat} (w: DoubleType.word w6 n) : option nat.
Proof.
induction n.
apply (Some (pickle w)).
destruct w.
apply None.
apply (Some (pickle (IHn w, IHn w0)%type)).
Defined.

Definition unpickle_word n (m : option nat) : option (DoubleType.word w6 n).
Proof.
move : m.
induction n.
case => [x|] /=.
apply (@unpickle (DoubleType.word w6 0) x).
apply None.
case => [x|] /=.
apply (match (@unpickle ((option nat) * option nat)%type x) with
        | None => None
       | Some (a,b) =>
           match (IHn a) with | None => None
                         | Some a' =>
                           match (IHn b) with | None => None
                          | Some b' => Some (DoubleType.WW a' b')
        end
       end
       end).
apply (Some (DoubleType.W0)).
Defined.

Lemma pickleK_word {n} : pcancel pickle_word (unpickle_word n).
Proof.
move => w.
induction n => /=; first by rewrite pickleK.
destruct w =>//.
rewrite pickleK.
by rewrite !IHn.
Qed.

Notation bigN_code := (Cyclic63.Uint63Cyclic.t + (w1 + (w2 + (w3 + (w4 + (w5 + (w6 + nat * option nat)))))))%type.
Definition pickle_bigN (n : bigN) : bigN_code :=
  match n with
  | N0 t => inl t
  | N1 w1 => inr (inl w1)
  | N2 w2 => inr (inr (inl w2))
  | N3 w3 => inr (inr (inr (inl w3)))
  | N4 w4 => inr (inr (inr (inr (inl w4))))
  | N5 w5 => inr (inr (inr (inr (inr (inl w5)))))
  | N6 w6 => inr (inr (inr (inr (inr (inr (inl w6))))))
  | Nn n wn => inr (inr (inr (inr (inr (inr (inr (n, pickle_word wn)))))))
 end.
Definition unpickle_bigN (m : bigN_code) : bigN := match m with
  | inl t => N0 t
  | inr (inl w1) => N1 w1
  | inr (inr (inl w2)) => N2 w2
  | inr (inr (inr (inl w3))) => N3 w3
  | inr (inr (inr (inr (inl w4)))) => N4 w4
  | inr (inr (inr (inr (inr (inl w5))))) => N5 w5
  | inr (inr (inr (inr (inr (inr (inl w6)))))) => N6 w6
  | inr (inr (inr (inr (inr (inr (inr (n, o))))))) =>
    match (unpickle_word n.+1 o) with
   | None => BigN.zero
   | Some w => Nn n w
   end
 end.
Lemma bigN_pickleK : cancel pickle_bigN unpickle_bigN.
Proof.
move => n.
case: n => //.
move => n w.
rewrite /unpickle_bigN/pickle_bigN.
by rewrite pickleK_word.
Qed.

HB.instance Definition _ := Countable.copy bigN (can_type bigN_pickleK).

Definition bigZ_pickle (z : bigZ) : bigN + bigN := 
  match z with
  | Pos n => inl n
  | Neg n => inr n
end.

Definition bigZ_unpickle (z : bigN + bigN) : bigZ := 
  match z with
  | inl n => Pos n
  | inr n => Neg n
end.

Definition bigZ_pickleK : cancel bigZ_pickle bigZ_unpickle.
Proof. by move => [n | n]. Qed.


HB.instance Definition _ := Countable.copy bigZ (can_type bigZ_pickleK).


Definition float_pickle {t1 t2: countType} (f : s_float t1 t2) : option (t1 * t2) :=
  match f with
  | Fnan => None
  | Float m e => Some (m,e)
   end.

Definition float_unpickle {t1 t2: countType} (n : option (t1 * t2)) :=
  match n with
  | None => Fnan
  | Some (m,e) => Float m e
  end.
             
Lemma float_pickleK {t1 t2: countType} : cancel (float_pickle (t1:=t1) (t2:=t2)) float_unpickle.
Proof. by move => [| z1 z2] /=. Qed.


HB.instance Definition _ {t1 t2 : countType} := Countable.copy (s_float t1 t2) (can_type float_pickleK).

Definition interval_pickle {t: countType} (i : f_interval t) : option (t * t) :=
  match i with
  | Inan => None
  | Ibnd a b => Some (a,b)
   end.

Definition interval_unpickle {t: countType} (n : option (t * t)) :=
  match n with
  | None => Inan
  | Some (a,b) => Ibnd a b
  end.
             
Lemma interval_pickleK {t: countType} : cancel (interval_pickle (t:=t) ) interval_unpickle.
Proof. by move => [| z1 z2] /=. Qed.

HB.instance Definition _ {t : countType} := Countable.copy (f_interval t) (can_type interval_pickleK).

