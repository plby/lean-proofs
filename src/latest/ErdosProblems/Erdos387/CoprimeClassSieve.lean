/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.SwitchedClassSieve

/-!
# Brun sieve in an arbitrary rough refined CRT class

`SwitchedClassSieve` established this construction for certificates produced
by divisor switching.  The comparable-prime estimate needs the same sieve
for a two-prime certificate.  This file isolates the exact weaker hypothesis:
the certificate value is `z`-rough.  No switching inequalities are used.
-/

namespace Erdos387

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open Finset Nat ArithmeticFunction

namespace CoverBPZ

theorem coprime_roughCertificateValue_of_dvd_refinedSievePrimeProduct
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    Nat.Coprime C.val.value d := by
  by_contra hcop
  obtain ⟨p, hp, hpC, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpProd : p ∣ refinedSievePrimeProduct S z := hpd.trans hd
  have hpz := (prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.2
  exact hrough p hp hpz hpC

theorem coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    Nat.Coprime (switchedClassModulus C) d := by
  unfold switchedClassModulus
  exact Nat.Coprime.mul_left
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (coprime_roughCertificateValue_of_dvd_refinedSievePrimeProduct
      C hrough hd)

noncomputable def roughClassLocalResidue
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) : ℕ :=
  Nat.chineseRemainder
    (coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct C hrough hd)
    (switchedClassResidue C) a

theorem roughClassLocalResidue_mod_class
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    roughClassLocalResidue C hrough hd a ≡ switchedClassResidue C
      [MOD switchedClassModulus C] :=
  (Nat.chineseRemainder
    (coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct C hrough hd)
    (switchedClassResidue C) a).prop.1

theorem roughClassLocalResidue_mod_local
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    roughClassLocalResidue C hrough hd a ≡ a [MOD d] :=
  (Nat.chineseRemainder
    (coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct C hrough hd)
    (switchedClassResidue C) a).prop.2

theorem roughClassLocalResidue_lt
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    roughClassLocalResidue C hrough hd a < switchedClassModulus C * d := by
  exact Nat.chineseRemainder_lt_mul
    (coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct C hrough hd)
    (switchedClassResidue C) a (switchedClassModulus_pos C).ne'
    (pos_of_dvd_refinedSievePrimeProduct S hd).ne'

noncomputable def roughClassLocalResidues
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) : Finset ℕ := by
  classical
  exact (localAssignmentResidues d S.k).image
    (roughClassLocalResidue C hrough hd)

theorem card_roughClassLocalResidues
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    (roughClassLocalResidues C hrough hd).card =
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
    have := S.hk3
    omega
  unfold roughClassLocalResidues
  rw [(Finset.card_image_iff).mpr]
  · exact card_localAssignmentResidues hlarge
  · intro a ha b hb hab
    have habMod : a ≡ b [MOD d] :=
      (roughClassLocalResidue_mod_local C hrough hd a).symm.trans
        (by simpa [hab] using
          roughClassLocalResidue_mod_local C hrough hd b)
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

theorem roughClassLocalResidues_lt
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    ∀ a ∈ roughClassLocalResidues C hrough hd,
      a < switchedClassModulus C * d := by
  intro a ha
  rw [roughClassLocalResidues, Finset.mem_image] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact roughClassLocalResidue_lt C hrough hd b

theorem mod_mem_roughClassLocalResidues_iff
    {B K X z d n : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    n % (switchedClassModulus C * d) ∈
        roughClassLocalResidues C hrough hd ↔
      n ≡ switchedClassResidue C [MOD switchedClassModulus C] ∧
        n % d ∈ localAssignmentResidues d S.k := by
  classical
  have hsq : Squarefree d := Squarefree.squarefree_of_dvd hd
    (refinedSievePrimeProduct_squarefree S z)
  constructor
  · intro hn
    rw [roughClassLocalResidues, Finset.mem_image] at hn
    obtain ⟨a, ha, hna⟩ := hn
    have hnCombined : n ≡ roughClassLocalResidue C hrough hd a
        [MOD switchedClassModulus C * d] := by
      change n % (switchedClassModulus C * d) =
        roughClassLocalResidue C hrough hd a %
          (switchedClassModulus C * d)
      rw [Nat.mod_eq_of_lt (roughClassLocalResidue_lt C hrough hd a)]
      exact hna.symm
    refine ⟨(hnCombined.of_mul_right d).trans
      (roughClassLocalResidue_mod_class C hrough hd a), ?_⟩
    have hnd : n ≡ a [MOD d] :=
      (hnCombined.of_mul_left (switchedClassModulus C)).trans
        (roughClassLocalResidue_mod_local C hrough hd a)
    have haLt : a < d := by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    have hnmod : n % d = a := Nat.mod_eq_of_modEq hnd haLt
    simpa [hnmod] using ha
  · rintro ⟨hnClass, hnd⟩
    rw [roughClassLocalResidues, Finset.mem_image]
    refine ⟨n % d, hnd, ?_⟩
    have hnLocal : n ≡ n % d [MOD d] := (Nat.mod_modEq n d).symm
    have hnCombined : n ≡ roughClassLocalResidue C hrough hd (n % d)
        [MOD switchedClassModulus C * d] :=
      Nat.chineseRemainder_modEq_unique
        (coprime_roughClassModulus_of_dvd_refinedSievePrimeProduct
          C hrough hd)
        hnClass hnLocal
    exact (Nat.mod_eq_of_modEq hnCombined
      (roughClassLocalResidue_lt C hrough hd (n % d))).symm

theorem divisibleSwitchedClassCandidates_eq_modularPreimageIoc_of_rough
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    DivisibleSwitchedClassCandidates C d =
      modularPreimageIoc (X / 2) X (switchedClassModulus C * d)
        (roughClassLocalResidues C hrough hd) := by
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
    have := S.hk3
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
      (mod_mem_roughClassLocalResidues_iff C hrough hd).mpr
        ⟨hnClass, ?_⟩⟩
    have hkn : S.k ≤ n := hX.trans hnIoc.1.le
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn).mp hdChoose
  · rintro ⟨hnIoc, hnMod⟩
    have hnData :=
      (mod_mem_roughClassLocalResidues_iff C hrough hd).mp hnMod
    have hnClassMod : n % switchedClassModulus C =
        switchedClassResidue C :=
      Nat.mod_eq_of_modEq hnData.1 (switchedClassResidue_lt C)
    have hkn : S.k ≤ n := hX.trans hnIoc.1.le
    refine ⟨⟨hnIoc, hnClassMod⟩, ?_⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn).mpr hnData.2

theorem abs_card_divisibleSwitchedClassCandidates_sub_density_of_rough
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
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
    (roughClassLocalResidues C hrough hd)
    (roughClassLocalResidues_lt C hrough hd)
  rw [← divisibleSwitchedClassCandidates_eq_modularPreimageIoc_of_rough
    C hrough hX hd, card_roughClassLocalResidues C hrough hd] at h
  push_cast at h
  simpa only [Nat.cast_mul] using h

theorem abs_card_switchedClass_sub_density_general
    {B K X : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) :
    |((C.classIoc (X / 2) X).card : ℝ) -
        ((X - X / 2 : ℕ) : ℝ) / switchedClassModulus C| ≤ 2 := by
  have h := abs_card_modularPreimageIoc_sub_density
    (L := X / 2) (U := X) (g := switchedClassModulus C)
    (Nat.div_le_self X 2) (switchedClassModulus_pos C)
    ({switchedClassResidue C} : Finset ℕ) (by
      intro a ha
      rw [Finset.mem_singleton] at ha
      subst a
      exact switchedClassResidue_lt C)
  simpa [classIoc_eq_switchedClass] using h

theorem abs_card_divisibleSwitchedClass_sub_nu_mul_base_le_of_rough
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
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
      abs_card_divisibleSwitchedClassCandidates_sub_density_of_rough
        C hrough hX hd
  have hA : |A - H / Q| ≤ 2 := by
    simpa [A, H, Q] using abs_card_switchedClass_sub_density_general C
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

theorem switchedClassBoundingSieve_abs_rem_le_of_rough
    {B K X z d : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hX : S.k ≤ X / 2) (hd : d ∣ refinedSievePrimeProduct S z) :
    |(switchedClassBoundingSieve C z).rem d| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  rw [BoundingSieve.rem, switchedClassBoundingSieve_multSum]
  change |((DivisibleSwitchedClassCandidates C d).card : ℝ) -
      binomialSieveNu S.k d * (C.classIoc (X / 2) X).card| ≤ _
  exact abs_card_divisibleSwitchedClass_sub_nu_mul_base_le_of_rough
    C hrough hX hd

theorem switchedClassBoundingSieve_brunUpperErrSum_le_of_rough
    {B K X z L : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
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
        have hrem := switchedClassBoundingSieve_abs_rem_le_of_rough
          C hrough hX hddiv
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

/-- Uniform even-Brun upper bound for every refined certificate whose value
is rough at the ambient threshold. -/
theorem siftedSwitchedClassCandidates_card_le_brun_of_rough
    {B K X z L : ℕ} {S : BPZSection6Input B K}
    (C : RefinedTupleCertificate S X) (hrough : IsZRough z C.val.value)
    (hX : S.k ≤ X / 2) (hk : 0 < S.k) (hz : 1 ≤ z) (hL : Even L)
    (hmainNonneg : 0 ≤
      (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L)) :
    ((SiftedSwitchedClassCandidates C z).card : ℝ) ≤
      (((X - X / 2 : ℕ) : ℝ) /
          (CoverBPZ.refinementModulus S * C.val.value : ℕ) + 2) *
        (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
      (4 : ℝ) * (z ^ L + 1 : ℕ) * (S.k : ℝ) ^ L := by
  have habstract :
      ((SiftedSwitchedClassCandidates C z).card : ℝ) ≤
        (switchedClassBoundingSieve C z).totalMass *
            (switchedClassBoundingSieve C z).mainSum (brunUpperWeight L) +
          (switchedClassBoundingSieve C z).errSum (brunUpperWeight L) := by
    rw [← switchedClassBoundingSieve_siftedSum C hX]
    exact brunUpperBound (switchedClassBoundingSieve C z) hL
  have htotal :
      ((switchedClassBoundingSieve C z).totalMass : ℝ) ≤
        ((X - X / 2 : ℕ) : ℝ) /
            (CoverBPZ.refinementModulus S * C.val.value : ℕ) + 2 := by
    change ((C.classIoc (X / 2) X).card : ℝ) ≤ _
    exact C.card_classIoc_le (Nat.div_le_self X 2)
  have hmainEq := switchedClassBoundingSieve_mainSum_eq_refined
    (z := z) C (brunUpperWeight L)
  have herr := switchedClassBoundingSieve_brunUpperErrSum_le_of_rough
    (L := L) C hrough hX hk hz
  rw [hmainEq] at habstract
  exact habstract.trans (add_le_add
    (mul_le_mul_of_nonneg_right htotal hmainNonneg) herr)

end CoverBPZ

end Erdos387
