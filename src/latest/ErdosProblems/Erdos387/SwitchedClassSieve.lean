/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.LocalizedSwitchingEstimate
import ErdosProblems.Erdos387.QualitativeSieve

/-!
# Brun sieve inside a switched CRT class

The large-component divisor switch fixes an additional congruence class
modulo the switched tuple value.  This file transports the exact local
density calculation to that thinner progression.
-/

namespace Erdos387

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open Finset Nat ArithmeticFunction

namespace CoverBPZ

noncomputable def switchedClassModulus {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) : ℕ :=
  refinementModulus S * C.val.value

noncomputable def switchedClassResidue {B K X : ℕ}
    {S : BPZSection6Input B K} (C : RefinedTupleCertificate S X) : ℕ :=
  simultaneousResidue C.property (refinementResidue S) C.val.crtResidue

theorem switchedClassModulus_pos {B K X : ℕ}
    {S : BPZSection6Input B K} (C : RefinedTupleCertificate S X) :
    0 < switchedClassModulus C :=
  Nat.mul_pos (refinementModulus_pos S) C.val.value_pos

theorem switchedClassResidue_lt {B K X : ℕ}
    {S : BPZSection6Input B K} (C : RefinedTupleCertificate S X) :
    switchedClassResidue C < switchedClassModulus C :=
  simultaneousResidue_lt C.property (refinementModulus_pos S)
    C.val.value_pos _ _

theorem classIoc_eq_switchedClass {B K X L U : ℕ}
    {S : BPZSection6Input B K} (C : RefinedTupleCertificate S X) :
    C.classIoc L U = modularPreimageIoc L U
      (switchedClassModulus C) {switchedClassResidue C} := by
  rfl

theorem switchedCertificate_value_rough
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large) :
    IsZRough z C.val.value := by
  intro p hp hpz hpValue
  unfold TupleCertificate.value at hpValue
  obtain ⟨i, _hi, hpi⟩ :=
    (hp.prime.dvd_finsetProd_iff C.val.factor).mp hpValue
  exact switchedCertificate_factor_rough hC i p hp hpz hpi

theorem coprime_switchedValue_of_dvd_refinedSievePrimeProduct
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    Nat.Coprime C.val.value d := by
  by_contra hcop
  obtain ⟨p, hp, hpC, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpProd : p ∣ refinedSievePrimeProduct S z := hpd.trans hd
  have hpz := (prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.2
  exact switchedCertificate_value_rough hC p hp hpz hpC

theorem coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    {C : RefinedTupleCertificate S X}
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    Nat.Coprime (switchedClassModulus C) d := by
  unfold switchedClassModulus
  exact Nat.Coprime.mul_left
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (coprime_switchedValue_of_dvd_refinedSievePrimeProduct hC hd)

noncomputable def switchedClassLocalResidue
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) : ℕ :=
  Nat.chineseRemainder
    (coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct hC hd)
    (switchedClassResidue C) a

theorem switchedClassLocalResidue_mod_class
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    switchedClassLocalResidue C hC hd a ≡ switchedClassResidue C
      [MOD switchedClassModulus C] :=
  (Nat.chineseRemainder
    (coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct hC hd)
    (switchedClassResidue C) a).prop.1

theorem switchedClassLocalResidue_mod_local
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    switchedClassLocalResidue C hC hd a ≡ a [MOD d] :=
  (Nat.chineseRemainder
    (coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct hC hd)
    (switchedClassResidue C) a).prop.2

theorem switchedClassLocalResidue_lt
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    switchedClassLocalResidue C hC hd a < switchedClassModulus C * d := by
  exact Nat.chineseRemainder_lt_mul
    (coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct hC hd)
    (switchedClassResidue C) a (switchedClassModulus_pos C).ne'
    (pos_of_dvd_refinedSievePrimeProduct S hd).ne'

noncomputable def switchedClassLocalResidues
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) : Finset ℕ := by
  classical
  exact (localAssignmentResidues d S.k).image
    (switchedClassLocalResidue C hC hd)

theorem card_switchedClassLocalResidues
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    (switchedClassLocalResidues C hC hd).card =
      S.k ^ d.primeFactors.card := by
  classical
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (refinedSievePrimeProduct_squarefree S z)
  have hlarge : ∀ p ∈ d.primeFactors, S.k < p := by
    intro p hpFact
    have hp := (Nat.mem_primeFactors.mp hpFact).1
    have hpProd : p ∣ refinedSievePrimeProduct S z :=
      (Nat.dvd_of_mem_primeFactors hpFact).trans hd
    have hpLower :=
      (prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.1
    have hk3 := S.hk3
    omega
  unfold switchedClassLocalResidues
  rw [(Finset.card_image_iff).mpr]
  · exact card_localAssignmentResidues hlarge
  · intro a ha b hb hab
    have habMod : a ≡ b [MOD d] :=
      (switchedClassLocalResidue_mod_local C hC hd a).symm.trans
        (by simpa [hab] using
          switchedClassLocalResidue_mod_local C hC hd b)
    exact habMod.eq_of_lt_of_lt
      (by
        change a ∈ localAssignmentResidues d S.k at ha
        rw [localAssignmentResidues, Finset.mem_image] at ha
        obtain ⟨A, _, rfl⟩ := ha
        exact localAssignmentResidue_lt hsq A)
      (by
        change b ∈ localAssignmentResidues d S.k at hb
        rw [localAssignmentResidues, Finset.mem_image] at hb
        obtain ⟨A, _, rfl⟩ := hb
        exact localAssignmentResidue_lt hsq A)

theorem switchedClassLocalResidues_lt
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    ∀ a ∈ switchedClassLocalResidues C hC hd,
      a < switchedClassModulus C * d := by
  intro a ha
  rw [switchedClassLocalResidues, Finset.mem_image] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact switchedClassLocalResidue_lt C hC hd b

theorem mod_mem_switchedClassLocalResidues_iff
    {B K X z large d n : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    n % (switchedClassModulus C * d) ∈
        switchedClassLocalResidues C hC hd ↔
      n ≡ switchedClassResidue C [MOD switchedClassModulus C] ∧
        n % d ∈ localAssignmentResidues d S.k := by
  classical
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (refinedSievePrimeProduct_squarefree S z)
  constructor
  · intro hn
    rw [switchedClassLocalResidues, Finset.mem_image] at hn
    obtain ⟨a, ha, hna⟩ := hn
    have hnCombined : n ≡ switchedClassLocalResidue C hC hd a
        [MOD switchedClassModulus C * d] := by
      change n % (switchedClassModulus C * d) =
        switchedClassLocalResidue C hC hd a %
          (switchedClassModulus C * d)
      rw [Nat.mod_eq_of_lt (switchedClassLocalResidue_lt C hC hd a)]
      exact hna.symm
    refine ⟨(hnCombined.of_mul_right d).trans
      (switchedClassLocalResidue_mod_class C hC hd a), ?_⟩
    have hnd : n ≡ a [MOD d] :=
      (hnCombined.of_mul_left (switchedClassModulus C)).trans
        (switchedClassLocalResidue_mod_local C hC hd a)
    have haLt : a < d := by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    have hnmod : n % d = a := Nat.mod_eq_of_modEq hnd haLt
    simpa [hnmod] using ha
  · rintro ⟨hnClass, hnd⟩
    rw [switchedClassLocalResidues, Finset.mem_image]
    refine ⟨n % d, hnd, ?_⟩
    have hnLocal : n ≡ n % d [MOD d] := (Nat.mod_modEq n d).symm
    have hnCombined : n ≡ switchedClassLocalResidue C hC hd (n % d)
        [MOD switchedClassModulus C * d] :=
      Nat.chineseRemainder_modEq_unique
        (coprime_switchedClassModulus_of_dvd_refinedSievePrimeProduct hC hd)
        hnClass hnLocal
    exact (Nat.mod_eq_of_modEq hnCombined
      (switchedClassLocalResidue_lt C hC hd (n % d))).symm

/-- Divisibility subset of one switched progression class. -/
noncomputable def DivisibleSwitchedClassCandidates
    {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (d : ℕ) : Finset ℕ := by
  classical
  exact (C.classIoc (X / 2) X).filter fun n => d ∣ n.choose S.k

theorem divisibleSwitchedClassCandidates_eq_modularPreimageIoc
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    DivisibleSwitchedClassCandidates C d =
      modularPreimageIoc (X / 2) X (switchedClassModulus C * d)
        (switchedClassLocalResidues C hC hd) := by
  classical
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (refinedSievePrimeProduct_squarefree S z)
  have hlarge : ∀ p ∈ d.primeFactors, S.k < p := by
    intro p hpFact
    have hp := (Nat.mem_primeFactors.mp hpFact).1
    have hpProd : p ∣ refinedSievePrimeProduct S z :=
      (Nat.dvd_of_mem_primeFactors hpFact).trans hd
    have hpLower :=
      (prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.1
    have hk3 := S.hk3
    omega
  ext n
  simp only [DivisibleSwitchedClassCandidates, classIoc_eq_switchedClass,
    modularPreimageIoc, Finset.mem_filter, Finset.mem_Ioc,
    Finset.mem_singleton]
  constructor
  · rintro ⟨⟨hnIoc, hnClassMod⟩, hdChoose⟩
    have hnClass : n ≡ switchedClassResidue C
        [MOD switchedClassModulus C] := by
      change n % switchedClassModulus C =
        switchedClassResidue C % switchedClassModulus C
      rw [Nat.mod_eq_of_lt (switchedClassResidue_lt C)]
      exact hnClassMod
    refine ⟨hnIoc,
      (mod_mem_switchedClassLocalResidues_iff C hC hd).mpr
        ⟨hnClass, ?_⟩⟩
    have hkn : S.k ≤ n := hX.trans hnIoc.1.le
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn).mp hdChoose
  · rintro ⟨hnIoc, hnMod⟩
    have hnData :=
      (mod_mem_switchedClassLocalResidues_iff C hC hd).mp hnMod
    have hnClassMod : n % switchedClassModulus C =
        switchedClassResidue C := by
      exact Nat.mod_eq_of_modEq hnData.1 (switchedClassResidue_lt C)
    have hkn : S.k ≤ n := hX.trans hnIoc.1.le
    refine ⟨⟨hnIoc, hnClassMod⟩, ?_⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn).mpr hnData.2

theorem abs_card_divisibleSwitchedClassCandidates_sub_density
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    |((DivisibleSwitchedClassCandidates C d).card : ℝ) -
        (S.k : ℝ) ^ d.primeFactors.card * ((X - X / 2 : ℕ) : ℝ) /
          (switchedClassModulus C * d : ℕ)| ≤
      2 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hmodPos : 0 < switchedClassModulus C * d :=
    Nat.mul_pos (switchedClassModulus_pos C)
      (pos_of_dvd_refinedSievePrimeProduct S hd)
  have h := abs_card_modularPreimageIoc_sub_density
    (L := X / 2) (U := X) (g := switchedClassModulus C * d)
    (Nat.div_le_self X 2) hmodPos
    (switchedClassLocalResidues C hC hd)
    (switchedClassLocalResidues_lt C hC hd)
  rw [← divisibleSwitchedClassCandidates_eq_modularPreimageIoc
    C hC hX hd, card_switchedClassLocalResidues C hC hd] at h
  push_cast at h
  simpa only [Nat.cast_mul] using h

theorem divisibleSwitchedClassCandidates_one
    {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) :
    DivisibleSwitchedClassCandidates C 1 = C.classIoc (X / 2) X := by
  classical
  ext n
  simp [DivisibleSwitchedClassCandidates]

theorem abs_card_switchedClass_sub_density
    {B K X z large : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) :
    |((C.classIoc (X / 2) X).card : ℝ) -
        ((X - X / 2 : ℕ) : ℝ) / switchedClassModulus C| ≤ 2 := by
  have h := abs_card_divisibleSwitchedClassCandidates_sub_density
    C hC hX (one_dvd (refinedSievePrimeProduct S z))
  rw [divisibleSwitchedClassCandidates_one] at h
  simpa using h

theorem abs_card_divisibleSwitchedClass_sub_nu_mul_base_le
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    |((DivisibleSwitchedClassCandidates C d).card : ℝ) -
        binomialSieveNu S.k d * (C.classIoc (X / 2) X).card| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (refinedSievePrimeProduct_squarefree S z)
  rw [binomialSieveNu_squarefree hsq]
  let R : ℝ := (S.k : ℝ) ^ d.primeFactors.card
  let H : ℝ := ((X - X / 2 : ℕ) : ℝ)
  let Q : ℝ := switchedClassModulus C
  let D : ℝ := (DivisibleSwitchedClassCandidates C d).card
  let A : ℝ := (C.classIoc (X / 2) X).card
  let q : ℝ := R / d
  have hD : |D - R * H / (Q * d)| ≤ 2 * R := by
    simpa [R, H, Q, D, Nat.cast_mul] using
      abs_card_divisibleSwitchedClassCandidates_sub_density C hC hX hd
  have hA : |A - H / Q| ≤ 2 := by
    simpa [A, H, Q] using abs_card_switchedClass_sub_density C hC hX
  have hdPosNat : 0 < d := pos_of_dvd_refinedSievePrimeProduct S hd
  have hdPos : (0 : ℝ) < d := by exact_mod_cast hdPosNat
  have hQPos : (0 : ℝ) < Q := by
    dsimp [Q]
    exact_mod_cast switchedClassModulus_pos C
  have hR : 0 ≤ R := by positivity
  have hq : 0 ≤ q := by positivity
  have hqLe : q ≤ R := by
    apply (div_le_iff₀ hdPos).2
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPosNat
    nlinarith
  have hmain : R * H / (Q * d) = q * (H / Q) := by
    dsimp [q]
    field_simp
  have hdecomp :
      D - q * A = (D - R * H / (Q * d)) - q * (A - H / Q) := by
    rw [hmain]
    ring
  change |D - q * A| ≤ 4 * R
  rw [hdecomp]
  calc
    |(D - R * H / (Q * d)) - q * (A - H / Q)| ≤
        |D - R * H / (Q * d)| + |q * (A - H / Q)| := abs_sub _ _
    _ = |D - R * H / (Q * d)| + q * |A - H / Q| := by
      rw [abs_mul, abs_of_nonneg hq]
    _ ≤ 2 * R + q * 2 := add_le_add hD
      (mul_le_mul_of_nonneg_left hA hq)
    _ ≤ 4 * R := by linarith

/-- Bounding sieve supported on one switched CRT class. -/
noncomputable def switchedClassBoundingSieve
    {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (z : ℕ) : BoundingSieve := by
  classical
  let A := C.classIoc (X / 2) X
  exact
    { support := A.image fun n => n.choose S.k
      prodPrimes := refinedSievePrimeProduct S z
      prodPrimes_squarefree := refinedSievePrimeProduct_squarefree S z
      weights := fun m =>
        ((A.filter fun n => n.choose S.k = m).card : ℝ)
      weights_nonneg := fun _ => by positivity
      totalMass := A.card
      nu := binomialSieveNu S.k
      nu_mult := binomialSieveNu_mult S.k
      nu_pos_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hkPos : 0 < S.k := by have := S.hk3; omega
        exact div_pos (by exact_mod_cast hkPos) (by exact_mod_cast hp.pos)
      nu_lt_one_of_prime := by
        intro p hp hdiv
        rw [binomialSieveNu_prime hp]
        have hpLower :=
          (prime_mem_refinedSievePrimes_of_dvd_product S hp hdiv).2.1
        have hkp : S.k < p := by have := S.hk3; omega
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hkp) }

noncomputable def SiftedSwitchedClassCandidates
    {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (z : ℕ) : Finset ℕ := by
  classical
  exact (C.classIoc (X / 2) X).filter fun n => IsZRough z (n.choose S.k)

theorem coprime_refinedSievePrimeProduct_iff_rough_of_mem_class
    {B K X z n : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hX : S.k ≤ X / 2)
    (hnClass : n ∈ C.classIoc (X / 2) X) :
    Nat.Coprime (refinedSievePrimeProduct S z) (n.choose S.k) ↔
      IsZRough z (n.choose S.k) := by
  have hnData := (RefinedTupleCertificate.mem_classIoc_iff C).mp hnClass
  have hkn : S.k < n := lt_of_le_of_lt hX (Finset.mem_Ioc.mp hnData.1).1
  have hprog : (refinementModulus S : ℤ) ∣
      (n : ℤ) - refinementResidue S :=
    (refinement_progression_dvd_iff_modEq S).mpr hnData.2.1
  exact coprime_refinedSievePrimeProduct_iff_rough S hkn hprog

theorem switchedClassBoundingSieve_siftedSum
    {B K X z : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hX : S.k ≤ X / 2) :
    (switchedClassBoundingSieve C z).siftedSum =
      ((SiftedSwitchedClassCandidates C z).card : ℝ) := by
  classical
  let A := C.classIoc (X / 2) X
  let f : ℕ → ℕ := fun n => n.choose S.k
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ A.image f,
      if Nat.Coprime (refinedSievePrimeProduct S z) m then
        ((A.filter fun n => f n = m).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ m ∈ (A.image f).filter fun m =>
          Nat.Coprime (refinedSievePrimeProduct S z) m,
          (A.filter fun n => f n = m).card) =
        (A.filter fun n =>
          Nat.Coprime (refinedSievePrimeProduct S z) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, SiftedSwitchedClassCandidates]
  constructor
  · rintro ⟨hnA, hcop⟩
    exact ⟨hnA,
      (coprime_refinedSievePrimeProduct_iff_rough_of_mem_class
        C hX hnA).mp hcop⟩
  · rintro ⟨hnA, hrough⟩
    exact ⟨hnA,
      (coprime_refinedSievePrimeProduct_iff_rough_of_mem_class
        C hX hnA).mpr hrough⟩

theorem switchedClassBoundingSieve_multSum
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) :
    (switchedClassBoundingSieve C z).multSum d =
      ((DivisibleSwitchedClassCandidates C d).card : ℝ) := by
  classical
  let A := C.classIoc (X / 2) X
  let f : ℕ → ℕ := fun n => n.choose S.k
  rw [BoundingSieve.multSum]
  change (∑ m ∈ A.image f,
      if d ∣ m then ((A.filter fun n => f n = m).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ m ∈ (A.image f).filter fun m => d ∣ m,
          (A.filter fun n => f n = m).card) =
        (A.filter fun n => d ∣ f n).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast

theorem switchedClassBoundingSieve_abs_rem_le
    {B K X z large d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    |(switchedClassBoundingSieve C z).rem d| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  rw [BoundingSieve.rem, switchedClassBoundingSieve_multSum]
  change |((DivisibleSwitchedClassCandidates C d).card : ℝ) -
      binomialSieveNu S.k d * (C.classIoc (X / 2) X).card| ≤ _
  exact abs_card_divisibleSwitchedClass_sub_nu_mul_base_le
    C hC hX hd

theorem switchedClassBoundingSieve_mainSum_eq_refined
    {B K X z : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (w : ℕ → ℝ) :
    (switchedClassBoundingSieve C z).mainSum w =
      (refinedBinomialBoundingSieve S X z).mainSum w := by
  rfl

/-- Uniform accumulated CRT error for an even Brun truncation in one
switched class. -/
theorem switchedClassBoundingSieve_brunUpperErrSum_le
    {B K X z large L : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hk : 0 < S.k) (hz : 1 ≤ z) :
    (switchedClassBoundingSieve C z).errSum (brunUpperWeight L) ≤
      (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by
  let s := switchedClassBoundingSieve C z
  rw [BoundingSieve.errSum]
  calc
    (∑ d ∈ (refinedSievePrimeProduct S z).divisors,
        |brunUpperWeight L d| * |s.rem d|) ≤
        ∑ d ∈ (refinedSievePrimeProduct S z).divisors,
          if d.primeFactors.card ≤ L then
            4 * (S.k : ℝ) ^ L else 0 := by
      apply Finset.sum_le_sum
      intro d hdmem
      by_cases hdL : d.primeFactors.card ≤ L
      · rw [if_pos hdL]
        have hddiv := (Nat.mem_divisors.mp hdmem).1
        have hrem := switchedClassBoundingSieve_abs_rem_le
          C hC hX hddiv
        calc
          |brunUpperWeight L d| * |s.rem d| ≤ 1 * |s.rem d| := by
            gcongr
            exact abs_brunUpperWeight_le_one L d
          _ ≤ 4 * (S.k : ℝ) ^ d.primeFactors.card := by
            simpa [s] using hrem
          _ ≤ 4 * (S.k : ℝ) ^ L := by
            gcongr
            exact_mod_cast hk
      · rw [if_neg hdL]
        have hzero : brunUpperWeight L d = 0 := by
          unfold brunUpperWeight
          rw [if_neg]
          simpa [cardDistinctFactors_eq_primeFactors_card] using hdL
        simp [hzero]
    _ = (((refinedSievePrimeProduct S z).divisors.filter fun d =>
          d.primeFactors.card ≤ L).card : ℝ) *
          (4 * (S.k : ℝ) ^ L) := by
      rw [← Finset.sum_filter]
      simp
    _ ≤ (z ^ L + 1 : ℕ) * (4 * (S.k : ℝ) ^ L) := by
      gcongr
      exact_mod_cast card_brunSupport_le (k := 2 * S.k - 1) hz
    _ = (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by ring

theorem siftedSwitchedClassCandidates_brunUpperBound
    {B K X z large L : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X)
    (_hC : C ∈ SwitchedLargeTupleCertificates S X z large)
    (hX : S.k ≤ X / 2) (hL : Even L) :
    ((SiftedSwitchedClassCandidates C z).card : ℝ) ≤
      (switchedClassBoundingSieve C z).totalMass *
          (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) +
        (switchedClassBoundingSieve C z).errSum (brunUpperWeight L) := by
  rw [← switchedClassBoundingSieve_siftedSum C hX]
  exact brunUpperBound (switchedClassBoundingSieve C z) hL

/-- Every large error lies in the sifted subset of its switched CRT class. -/
theorem refinedLargeErrors_subset_siftedSwitchedClasses
    {B K X z large : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2) :
    RefinedLargeErrors S X z large ⊆
      (SwitchedLargeTupleCertificates S X z large).biUnion
        (fun C => SiftedSwitchedClassCandidates C z) := by
  classical
  intro n hnError
  have hnClass :=
    refinedLargeErrors_subset_switchedCertificateClasses
      (X := X) (z := z) (large := large) S hB hz hXwide hscale hnError
  rw [Finset.mem_biUnion] at hnClass ⊢
  obtain ⟨C, hC, hnC⟩ := hnClass
  refine ⟨C, hC, ?_⟩
  rw [SiftedSwitchedClassCandidates, Finset.mem_filter]
  refine ⟨hnC, ?_⟩
  have hnData := hnError
  rw [RefinedLargeErrors, Finset.mem_filter,
    RefinedSiftedCandidates, Finset.mem_filter] at hnData
  exact hnData.1.2

/-- Sum of the per-class Brun upper bounds for the large-error set. -/
theorem refinedLargeErrors_card_le_sum_switchedBrunUpper
    {B K X z large L : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz : 2 * S.k ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2)
    (hX : S.k ≤ X / 2) (hL : Even L) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ∑ C ∈ SwitchedLargeTupleCertificates S X z large,
        ((switchedClassBoundingSieve C z).totalMass *
            (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) +
          (switchedClassBoundingSieve C z).errSum (brunUpperWeight L)) := by
  let T := SwitchedLargeTupleCertificates S X z large
  have hsubset : RefinedLargeErrors S X z large ⊆
      T.biUnion (fun C => SiftedSwitchedClassCandidates C z) := by
    simpa [T] using refinedLargeErrors_subset_siftedSwitchedClasses
      (X := X) (large := large) S hB hz hXwide hscale
  have hcardNat := Finset.card_le_card hsubset
  have hunionNat :
      (T.biUnion fun C => SiftedSwitchedClassCandidates C z).card ≤
        ∑ C ∈ T, (SiftedSwitchedClassCandidates C z).card :=
    Finset.card_biUnion_le
  have hleft : ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ∑ C ∈ T, ((SiftedSwitchedClassCandidates C z).card : ℝ) := by
    exact_mod_cast hcardNat.trans hunionNat
  change _ ≤ ∑ C ∈ T, _
  refine hleft.trans (Finset.sum_le_sum fun C hC => ?_)
  exact siftedSwitchedClassCandidates_brunUpperBound C hC hX hL

/-- Consolidated finite Proposition 6.2 bound.  The first factor is the same
Brun main sum as for the global refined sieve; the second is the rough
harmonic tensor power; all CRT endpoint errors are explicit. -/
theorem refinedLargeErrors_card_le_brun_switchedSum_endpoint
    {B K X z large L : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz2k : 2 * S.k ≤ z) (hz1 : 1 ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2)
    (hX : S.k ≤ X / 2) (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ((((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
            (∑ C ∈ SwitchedLargeTupleCertificates S X z large,
              (1 : ℝ) / C.val.value) +
          2 * ((SwitchedLargeTupleCertificates S X z large).card : ℝ)) *
        (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
      ((SwitchedLargeTupleCertificates S X z large).card : ℝ) *
        ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L) := by
  let T := SwitchedLargeTupleCertificates S X z large
  let V := (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)
  let E : ℝ := (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L
  let A : ℝ := ((X - X / 2 : ℕ) : ℝ) / refinementModulus S
  let N : ℝ := ((X / (large + 1) + 1) ^ S.k : ℕ)
  let rfun : RefinedTupleCertificate S X → ℝ :=
    fun C => (1 : ℝ) / C.val.value
  let R : ℝ := ∑ C ∈ T, rfun C
  have hraw := refinedLargeErrors_card_le_sum_switchedBrunUpper
    (X := X) (z := z) (large := large) (L := L)
    S hB hz2k hXwide hscale hX hL
  change ((RefinedLargeErrors S X z large).card : ℝ) ≤
    ∑ C ∈ T,
      ((switchedClassBoundingSieve C z).totalMass *
          (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) +
        (switchedClassBoundingSieve C z).errSum (brunUpperWeight L)) at hraw
  have hper : ∀ C ∈ T,
      (switchedClassBoundingSieve C z).totalMass *
          (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) +
        (switchedClassBoundingSieve C z).errSum (brunUpperWeight L) ≤
      (A * rfun C + 2) * V + E := by
    intro C hC
    have hcard := C.card_classIoc_le (Nat.div_le_self X 2)
    have hclassMain :
        ((switchedClassBoundingSieve C z).totalMass : ℝ) *
            (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) =
          ((C.classIoc (X / 2) X).card : ℝ) * V := by
      rw [switchedClassBoundingSieve_mainSum_eq_refined]
      rfl
    have hdenom :
        (((X - X / 2 : ℕ) : ℝ) /
            (refinementModulus S * C.val.value : ℕ)) =
          A * rfun C := by
      have hm : (refinementModulus S : ℝ) ≠ 0 := by
        exact_mod_cast (refinementModulus_pos S).ne'
      have hd : (C.val.value : ℝ) ≠ 0 := by
        exact_mod_cast C.val.value_pos.ne'
      dsimp [A, rfun]
      push_cast
      field_simp
    rw [hdenom] at hcard
    have hmainLe :
        ((C.classIoc (X / 2) X).card : ℝ) * V ≤
          (A * ((1 : ℝ) / C.val.value) + 2) * V :=
      mul_le_mul_of_nonneg_right hcard hmainNonneg
    have herr := switchedClassBoundingSieve_brunUpperErrSum_le
      C hC hX (by have := S.hk3; omega) hz1 (L := L)
    change (switchedClassBoundingSieve C z).errSum (brunUpperWeight L) ≤ E at herr
    rw [hclassMain]
    exact add_le_add hmainLe herr
  have hsum := hraw.trans (Finset.sum_le_sum hper)
  have hsumExplicit :
      ((RefinedLargeErrors S X z large).card : ℝ) ≤
        Finset.sum T (fun C : RefinedTupleCertificate S X =>
          (A * rfun C + 2) * V + E) := hsum
  have hrewrite :
      Finset.sum T (fun C : RefinedTupleCertificate S X =>
          (A * rfun C + 2) * V + E) =
        (A * R + 2 * (T.card : ℝ)) * V + (T.card : ℝ) * E := by
    calc
      Finset.sum T (fun C : RefinedTupleCertificate S X =>
          (A * rfun C + 2) * V + E) =
          Finset.sum T (fun C : RefinedTupleCertificate S X =>
            A * rfun C * V + 2 * V + E) := by
            apply Finset.sum_congr rfl
            intro C hC
            ring
      _ = A * (Finset.sum T rfun) * V +
          2 * (T.card : ℝ) * V + (T.card : ℝ) * E := by
            rw [Finset.sum_add_distrib, Finset.sum_add_distrib,
              Finset.mul_sum, Finset.sum_mul]
            simp
            dsimp [rfun]
            ring_nf
            congr 1
            apply Finset.sum_congr rfl
            intro C hC
            ring
      _ = (A * R + 2 * (T.card : ℝ)) * V + (T.card : ℝ) * E := by
            dsimp [R]
            ring
  have hsum' := hsumExplicit.trans_eq hrewrite
  exact hsum'

/-- The broad cumulative-rough-mass corollary retained for comparison with
the earlier, unlocalized reduction. -/
theorem refinedLargeErrors_card_le_brun_roughMass_endpoint
    {B K X z large L : ℕ} (S : BPZSection6Input B K)
    (hB : 0 < B) (hz2k : 2 * S.k ≤ z) (hz1 : 1 ≤ z)
    (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2)
    (hX : S.k ≤ X / 2) (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ((((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
            (roughReciprocalMass z (X / (large + 1))) ^ S.k +
          2 * ((X / (large + 1) + 1) ^ S.k : ℕ)) *
        (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
      ((X / (large + 1) + 1) ^ S.k : ℕ) *
        ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L) := by
  have hbase := refinedLargeErrors_card_le_brun_switchedSum_endpoint
    S hB hz2k hz1 hXwide hscale hX hL hmainNonneg
  let T := SwitchedLargeTupleCertificates S X z large
  let V := (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)
  let E : ℝ := (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L
  let A : ℝ := ((X - X / 2 : ℕ) : ℝ) / refinementModulus S
  let N : ℝ := ((X / (large + 1) + 1) ^ S.k : ℕ)
  let R : ℝ := ∑ C ∈ T, (1 : ℝ) / C.val.value
  have hmass := switchedCertificate_reciprocalSum_le_mass_pow
    (X := X) (z := z) (large := large) S
  change R ≤ (roughReciprocalMass z (X / (large + 1))) ^ S.k at hmass
  have hcardNat := card_switchedLargeTupleCertificates_le
    (X := X) (large := large) S z
  have hcard : (T.card : ℝ) ≤ N := by
    dsimp [T, N]
    exact_mod_cast hcardNat
  have hA : 0 ≤ A := by
    dsimp [A]
    positivity
  have hN : 0 ≤ N := by positivity
  have hE : 0 ≤ E := by
    dsimp [E]
    positivity
  have hcoef : A * R + 2 * (T.card : ℝ) ≤
      A * (roughReciprocalMass z (X / (large + 1))) ^ S.k + 2 * N :=
    add_le_add (mul_le_mul_of_nonneg_left hmass hA)
      (mul_le_mul_of_nonneg_left hcard (by norm_num))
  have hmain : (A * R + 2 * (T.card : ℝ)) * V ≤
      (A * (roughReciprocalMass z (X / (large + 1))) ^ S.k + 2 * N) * V :=
    mul_le_mul_of_nonneg_right hcoef hmainNonneg
  have herr : (T.card : ℝ) * E ≤ N * E :=
    mul_le_mul_of_nonneg_right hcard hE
  exact hbase.trans (add_le_add hmain herr)

/-- Proposition 6.2 with the fixed-`B` short-interval saving inserted into
the switched Brun-class count.  Unlike the broad cumulative corollary above,
this right-hand side has an explicit factor `1 / log z`. -/
theorem refinedLargeErrors_card_le_brun_localized_endpoint
    {C : ℝ} {N B K X z large L : ℕ} (S : BPZSection6Input B K)
    (hC : 0 < C)
    (hcheb : ∀ t : ℕ, N ≤ t →
      (Nat.primeCounting t : ℝ) ≤ C * t / Real.log t)
    (hzN : N ≤ z) (hz : 2 ≤ z) (hB : 0 < B)
    (hzg : ∀ i : Fin S.k, 6 * S.g i ≤ z)
    (hz2k : 2 * S.k ≤ z) (hXwide : 6 * S.k ≤ X)
    (hscale : (X / (large + 1)) ^ 2 ≤ X / 2)
    (hX : S.k ≤ X / 2) (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)) :
    ((RefinedLargeErrors S X z large).card : ℝ) ≤
      ((((X - X / 2 : ℕ) : ℝ) / refinementModulus S) *
            localizedSwitchedReciprocalEnvelope S C X z large +
          2 * switchedCertificateCountEnvelope S X z large) *
        (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
      switchedCertificateCountEnvelope S X z large *
        ((4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L) := by
  have hbase := refinedLargeErrors_card_le_brun_switchedSum_endpoint
    S hB hz2k (by omega) hXwide hscale hX hL hmainNonneg
  let T := SwitchedLargeTupleCertificates S X z large
  let V := (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)
  let E : ℝ := (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L
  let A : ℝ := ((X - X / 2 : ℕ) : ℝ) / refinementModulus S
  let Ncert : ℝ := switchedCertificateCountEnvelope S X z large
  let R : ℝ := ∑ C ∈ T, (1 : ℝ) / C.val.value
  have hmass := switchedCertificate_reciprocalSum_le_localizedEnvelope
    (X := X) (z := z) (large := large) S hC hcheb hzN hz hB hzg
  change R ≤ localizedSwitchedReciprocalEnvelope S C X z large at hmass
  have hcard : (T.card : ℝ) ≤ Ncert := by
    dsimp [T, Ncert]
    exact card_switchedLargeTupleCertificates_real_le_envelope
      (X := X) (z := z) (large := large) S
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hE : 0 ≤ E := by dsimp [E]; positivity
  have hcoef : A * R + 2 * (T.card : ℝ) ≤
      A * localizedSwitchedReciprocalEnvelope S C X z large + 2 * Ncert :=
    add_le_add (mul_le_mul_of_nonneg_left hmass hA)
      (mul_le_mul_of_nonneg_left hcard (by norm_num))
  have hmain : (A * R + 2 * (T.card : ℝ)) * V ≤
      (A * localizedSwitchedReciprocalEnvelope S C X z large +
        2 * Ncert) * V :=
    mul_le_mul_of_nonneg_right hcoef hmainNonneg
  have herr : (T.card : ℝ) * E ≤ Ncert * E :=
    mul_le_mul_of_nonneg_right hcard hE
  exact hbase.trans (add_le_add hmain herr)

end CoverBPZ

end Erdos387
