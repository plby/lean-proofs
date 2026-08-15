/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.RefinedCover

/-!
# Exact sieve on the refined BNPZ progression

Section 6 of BNPZ works modulo
`M = N_k * ∏_{k < p < 2k} p`.  This file transports the exact CRT-density
calculation and the finite Brun sieve to that refined progression.  The
remaining sieving primes are those at least `2k` and below `z`.
-/

namespace Erdos387

open scoped ArithmeticFunction.Moebius
open scoped BigOperators
open Finset Nat ArithmeticFunction

namespace CoverBPZ

/-- The literal modulus of the canonical refined progression. -/
noncomputable def refinementModulus {B K : ℕ} (S : BPZSection6Input B K) : ℕ :=
  Nk_formula S.k * refinementPrimeProduct S.k

theorem refinementModulus_pos {B K : ℕ} (S : BPZSection6Input B K) :
    0 < refinementModulus S :=
  Nat.mul_pos (Nk_formula_pos S.k) (refinementPrimeProduct_pos S.k)

theorem refinementResidue_lt {B K : ℕ} (S : BPZSection6Input B K) :
    refinementResidue S < refinementModulus S := by
  exact progressionLocalResidue_lt S
    (dvd_refl (refinementPrimeProduct S.k)) S.k

theorem refinement_progression_dvd_iff_modEq {B K n : ℕ}
    (S : BPZSection6Input B K) :
    (refinementModulus S : ℤ) ∣ (n : ℤ) - refinementResidue S ↔
      n ≡ refinementResidue S [MOD refinementModulus S] := by
  constructor
  · intro h
    apply Int.natCast_modEq_iff.mp
    exact (Int.modEq_iff_dvd.mpr h).symm
  · intro h
    have hz := Int.natCast_modEq_iff.mpr h
    exact Int.modEq_iff_dvd.mp hz.symm

/-- Every prime divisor of the refined modulus is strictly below `2k`. -/
theorem prime_lt_two_mul_k_of_dvd_refinementModulus
    {B K p : ℕ} (S : BPZSection6Input B K) (hp : p.Prime)
    (hpM : p ∣ refinementModulus S) : p < 2 * S.k := by
  rcases hp.dvd_mul.mp hpM with hpNk | hpP
  · have hk3 := S.hk3
    exact lt_of_le_of_lt (prime_le_of_dvd_Nk_formula hp hpNk) (by omega)
  · have hmem := prime_mem_sievePrimes_of_dvd_product hp hpP
    exact (mem_sievePrimes.mp hmem).2.2

/-- The primes left for the sieve after the finite refinement.  The lower
parameter `2k-1` makes the strict inequality in `sievePrimes` express
`p ≥ 2k`. -/
def refinedSievePrimeProduct {B K : ℕ}
    (S : BPZSection6Input B K) (z : ℕ) : ℕ :=
  sievePrimeProduct (2 * S.k - 1) z

theorem refinedSievePrimeProduct_squarefree {B K : ℕ}
    (S : BPZSection6Input B K) (z : ℕ) :
    Squarefree (refinedSievePrimeProduct S z) :=
  sievePrimeProduct_squarefree (2 * S.k - 1) z

theorem refinedSievePrimeProduct_pos {B K : ℕ}
    (S : BPZSection6Input B K) (z : ℕ) :
    0 < refinedSievePrimeProduct S z :=
  sievePrimeProduct_pos (2 * S.k - 1) z

theorem prime_mem_refinedSievePrimes_of_dvd_product
    {B K z p : ℕ} (S : BPZSection6Input B K) (hp : p.Prime)
    (hpP : p ∣ refinedSievePrimeProduct S z) :
    p.Prime ∧ 2 * S.k - 1 < p ∧ p < z := by
  exact mem_sievePrimes.mp (prime_mem_sievePrimes_of_dvd_product hp hpP)

theorem coprime_refinementModulus_of_dvd_refinedSievePrimeProduct
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    Nat.Coprime (refinementModulus S) d := by
  by_contra hcop
  obtain ⟨p, hp, hpM, hpd⟩ := Nat.Prime.not_coprime_iff_dvd.mp hcop
  have hpSmall := prime_lt_two_mul_k_of_dvd_refinementModulus S hp hpM
  have hpProd : p ∣ refinedSievePrimeProduct S z := hpd.trans hd
  have hpLarge :=
    (prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.1
  omega

theorem pos_of_dvd_refinedSievePrimeProduct
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) : 0 < d :=
  Nat.pos_of_dvd_of_pos hd (refinedSievePrimeProduct_pos S z)

/-- CRT combination of the canonical refined class with one local class
modulo a squarefree sieve divisor. -/
noncomputable def refinedProgressionLocalResidue
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) : ℕ :=
  Nat.chineseRemainder
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (refinementResidue S) a

theorem refinedProgressionLocalResidue_mod_M
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    refinedProgressionLocalResidue S hd a ≡ refinementResidue S
      [MOD refinementModulus S] :=
  (Nat.chineseRemainder
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (refinementResidue S) a).prop.1

theorem refinedProgressionLocalResidue_mod_local
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    refinedProgressionLocalResidue S hd a ≡ a [MOD d] :=
  (Nat.chineseRemainder
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (refinementResidue S) a).prop.2

theorem refinedProgressionLocalResidue_lt
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) (a : ℕ) :
    refinedProgressionLocalResidue S hd a < refinementModulus S * d := by
  exact Nat.chineseRemainder_lt_mul
    (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
    (refinementResidue S) a (refinementModulus_pos S).ne'
    (pos_of_dvd_refinedSievePrimeProduct S hd).ne'

noncomputable def refinedProgressionLocalResidues
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) : Finset ℕ := by
  classical
  exact (localAssignmentResidues d S.k).image
    (refinedProgressionLocalResidue S hd)

theorem card_refinedProgressionLocalResidues
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    (refinedProgressionLocalResidues S hd).card =
      S.k ^ d.primeFactors.card := by
  classical
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
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
  unfold refinedProgressionLocalResidues
  rw [(Finset.card_image_iff).mpr]
  · exact card_localAssignmentResidues hlarge
  · intro a ha b hb hab
    have habMod : a ≡ b [MOD d] :=
      (refinedProgressionLocalResidue_mod_local S hd a).symm.trans
        (by simpa [hab] using
          refinedProgressionLocalResidue_mod_local S hd b)
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

theorem refinedProgressionLocalResidues_lt
    {B K z d : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    ∀ a ∈ refinedProgressionLocalResidues S hd,
      a < refinementModulus S * d := by
  intro a ha
  rw [refinedProgressionLocalResidues, Finset.mem_image] at ha
  obtain ⟨b, _, rfl⟩ := ha
  exact refinedProgressionLocalResidue_lt S hd b

theorem mod_mem_refinedProgressionLocalResidues_iff
    {B K z d n : ℕ} (S : BPZSection6Input B K)
    (hd : d ∣ refinedSievePrimeProduct S z) :
    n % (refinementModulus S * d) ∈ refinedProgressionLocalResidues S hd ↔
      n ≡ refinementResidue S [MOD refinementModulus S] ∧
        n % d ∈ localAssignmentResidues d S.k := by
  classical
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (refinedSievePrimeProduct_squarefree S z)
  constructor
  · intro hn
    rw [refinedProgressionLocalResidues, Finset.mem_image] at hn
    obtain ⟨a, ha, hna⟩ := hn
    have hnCombined : n ≡ refinedProgressionLocalResidue S hd a
        [MOD refinementModulus S * d] := by
      change n % (refinementModulus S * d) =
        refinedProgressionLocalResidue S hd a %
          (refinementModulus S * d)
      rw [Nat.mod_eq_of_lt (refinedProgressionLocalResidue_lt S hd a)]
      exact hna.symm
    refine ⟨(hnCombined.of_mul_right d).trans
      (refinedProgressionLocalResidue_mod_M S hd a), ?_⟩
    have hnd : n ≡ a [MOD d] :=
      (hnCombined.of_mul_left (refinementModulus S)).trans
        (refinedProgressionLocalResidue_mod_local S hd a)
    have haLt : a < d := by
      rw [localAssignmentResidues, Finset.mem_image] at ha
      obtain ⟨A, _, rfl⟩ := ha
      exact localAssignmentResidue_lt hsq A
    have hnmod : n % d = a := Nat.mod_eq_of_modEq hnd haLt
    simpa [hnmod] using ha
  · rintro ⟨hnM, hnd⟩
    rw [refinedProgressionLocalResidues, Finset.mem_image]
    refine ⟨n % d, hnd, ?_⟩
    have hnLocal : n ≡ n % d [MOD d] := (Nat.mod_modEq n d).symm
    have hnCombined : n ≡ refinedProgressionLocalResidue S hd (n % d)
        [MOD refinementModulus S * d] :=
      Nat.chineseRemainder_modEq_unique
        (coprime_refinementModulus_of_dvd_refinedSievePrimeProduct S hd)
        hnM hnLocal
    exact (Nat.mod_eq_of_modEq hnCombined
      (refinedProgressionLocalResidue_lt S hd (n % d))).symm

end CoverBPZ

/-- The half-dyadic interval restricted to the canonical refined
progression. -/
noncomputable def RefinedBaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Ioc (X / 2) X).filter fun n =>
    S.k < n ∧ (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S

theorem mem_RefinedBaseCandidates {B K X n : ℕ}
    {S : CoverBPZ.BPZSection6Input B K} :
    n ∈ RefinedBaseCandidates S X ↔
      n ∈ Finset.Ioc (X / 2) X ∧ S.k < n ∧
        (CoverBPZ.refinementModulus S : ℤ) ∣
          (n : ℤ) - CoverBPZ.refinementResidue S := by
  classical
  simp [RefinedBaseCandidates]

/-- The refined progression is a subprogression of the original public
covering class. -/
theorem refinedBaseCandidates_subset_baseCandidates {B K X : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    RefinedBaseCandidates S X ⊆ BaseCandidates S X := by
  intro n hn
  have hdata := (mem_RefinedBaseCandidates (S := S)).mp hn
  apply (mem_BaseCandidates (S := S)).mpr
  refine ⟨hdata.1, hdata.2.1, ?_⟩
  apply (progression_dvd_iff_modEq S).mpr
  have hmod := (CoverBPZ.refinement_progression_dvd_iff_modEq S).mp hdata.2.2
  exact (hmod.of_mul_right (CoverBPZ.refinementPrimeProduct S.k)).trans
    (CoverBPZ.refinementResidue_mod_Nk S)

/-- Members of the canonical refined progression satisfy the literal
`BPZSection6InputRefined` conclusion. -/
theorem refinedProgression_property {B K n : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (hn : S.k < n)
    (hprog : (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S) :
    (∀ p : ℕ, p.Prime → p < 2 * S.k → ¬p ∣ n.choose S.k) ∧
      (∀ i j : Fin S.k, i ≠ j →
        Nat.Coprime ((n - i.val) / S.g i) ((n - j.val) / S.g j)) := by
  have h := (S.refine).refined (n : ℤ) (by exact_mod_cast hn) hprog
  refine ⟨?_, h.2⟩
  intro p hp hp2 hpChoose
  apply h.1 p hp hp2
  exact_mod_cast hpChoose

/-- The divisibility subset needed by the refined local-density sieve. -/
noncomputable def DivisibleRefinedBaseCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X d : ℕ) : Finset ℕ := by
  classical
  exact (RefinedBaseCandidates S X).filter fun n => d ∣ n.choose S.k

theorem divisibleRefinedBaseCandidates_eq_modularPreimageIoc
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hd : d ∣ CoverBPZ.refinedSievePrimeProduct S z) :
    DivisibleRefinedBaseCandidates S X d =
      modularPreimageIoc (X / 2) X
        (CoverBPZ.refinementModulus S * d)
        (CoverBPZ.refinedProgressionLocalResidues S hd) := by
  classical
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (CoverBPZ.refinedSievePrimeProduct_squarefree S z)
  have hlarge : ∀ p ∈ d.primeFactors, S.k < p := by
    intro p hpFact
    have hp := (Nat.mem_primeFactors.mp hpFact).1
    have hpProd : p ∣ CoverBPZ.refinedSievePrimeProduct S z :=
      (Nat.dvd_of_mem_primeFactors hpFact).trans hd
    have hpLower :=
      (CoverBPZ.prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd).2.1
    have hk3 := S.hk3
    omega
  ext n
  simp only [DivisibleRefinedBaseCandidates, RefinedBaseCandidates,
    modularPreimageIoc, Finset.mem_filter, Finset.mem_Ioc]
  constructor
  · rintro ⟨⟨hnIoc, hkn, hprog⟩, hdChoose⟩
    refine ⟨hnIoc,
      (CoverBPZ.mod_mem_refinedProgressionLocalResidues_iff S hd).mpr
        ⟨(CoverBPZ.refinement_progression_dvd_iff_modEq S).mp hprog, ?_⟩⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn.le).mp hdChoose
  · rintro ⟨hnIoc, hnMod⟩
    have hkn : S.k < n := lt_of_le_of_lt hX hnIoc.1
    have hnData :=
      (CoverBPZ.mod_mem_refinedProgressionLocalResidues_iff S hd).mp hnMod
    refine ⟨⟨hnIoc, hkn,
      (CoverBPZ.refinement_progression_dvd_iff_modEq S).mpr hnData.1⟩, ?_⟩
    exact (squarefree_dvd_choose_iff_mod_mem_localAssignmentResidues
      hsq hlarge hkn.le).mpr hnData.2

/-- Exact endpoint discrepancy for a squarefree local modulus on the
refined progression. -/
theorem abs_card_divisibleRefinedBaseCandidates_sub_density
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hd : d ∣ CoverBPZ.refinedSievePrimeProduct S z) :
    |((DivisibleRefinedBaseCandidates S X d).card : ℝ) -
        (S.k : ℝ) ^ d.primeFactors.card * ((X - X / 2 : ℕ) : ℝ) /
          (CoverBPZ.refinementModulus S * d : ℕ)| ≤
      2 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hmodPos : 0 < CoverBPZ.refinementModulus S * d :=
    Nat.mul_pos (CoverBPZ.refinementModulus_pos S)
      (CoverBPZ.pos_of_dvd_refinedSievePrimeProduct S hd)
  have h := abs_card_modularPreimageIoc_sub_density
    (L := X / 2) (U := X)
    (g := CoverBPZ.refinementModulus S * d)
    (Nat.div_le_self X 2) hmodPos
    (CoverBPZ.refinedProgressionLocalResidues S hd)
    (CoverBPZ.refinedProgressionLocalResidues_lt S hd)
  rw [← divisibleRefinedBaseCandidates_eq_modularPreimageIoc S hX hd,
    CoverBPZ.card_refinedProgressionLocalResidues S hd] at h
  push_cast at h
  simpa only [Nat.cast_mul] using h

theorem divisibleRefinedBaseCandidates_one {B K X : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    DivisibleRefinedBaseCandidates S X 1 = RefinedBaseCandidates S X := by
  classical
  ext n
  simp [DivisibleRefinedBaseCandidates]

theorem abs_card_RefinedBaseCandidates_sub_density
    {B K X : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) :
    |((RefinedBaseCandidates S X).card : ℝ) -
        ((X - X / 2 : ℕ) : ℝ) / CoverBPZ.refinementModulus S| ≤ 2 := by
  have h := abs_card_divisibleRefinedBaseCandidates_sub_density
    (z := 0) (d := 1) S hX (one_dvd _)
  rw [divisibleRefinedBaseCandidates_one] at h
  simpa using h

/-- Uniform remainder estimate for the refined progression. -/
theorem abs_card_DivisibleRefinedBaseCandidates_sub_nu_mul_base_le
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2) (hd : d ∣ CoverBPZ.refinedSievePrimeProduct S z) :
    |((DivisibleRefinedBaseCandidates S X d).card : ℝ) -
        binomialSieveNu S.k d * (RefinedBaseCandidates S X).card| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  have hsq : Squarefree d :=
    Squarefree.squarefree_of_dvd hd
      (CoverBPZ.refinedSievePrimeProduct_squarefree S z)
  rw [binomialSieveNu_squarefree hsq]
  let R : ℝ := (S.k : ℝ) ^ d.primeFactors.card
  let H : ℝ := ((X - X / 2 : ℕ) : ℝ)
  let M : ℝ := CoverBPZ.refinementModulus S
  let D : ℝ := (DivisibleRefinedBaseCandidates S X d).card
  let A : ℝ := (RefinedBaseCandidates S X).card
  let q : ℝ := R / d
  have hD : |D - R * H / (M * d)| ≤ 2 * R := by
    simpa [R, H, M, D, Nat.cast_mul] using
      abs_card_divisibleRefinedBaseCandidates_sub_density S hX hd
  have hA : |A - H / M| ≤ 2 := by
    simpa [A, H, M] using
      abs_card_RefinedBaseCandidates_sub_density S hX
  have hdPosNat : 0 < d :=
    CoverBPZ.pos_of_dvd_refinedSievePrimeProduct S hd
  have hdPos : (0 : ℝ) < d := by exact_mod_cast hdPosNat
  have hMPos : (0 : ℝ) < M := by
    dsimp [M]
    exact_mod_cast CoverBPZ.refinementModulus_pos S
  have hR : 0 ≤ R := by positivity
  have hq : 0 ≤ q := by positivity
  have hqLe : q ≤ R := by
    apply (div_le_iff₀ hdPos).2
    have hdOne : (1 : ℝ) ≤ d := by exact_mod_cast hdPosNat
    nlinarith
  have hmain : R * H / (M * d) = q * (H / M) := by
    dsimp [q]
    field_simp
  have hdecomp :
      D - q * A = (D - R * H / (M * d)) - q * (A - H / M) := by
    rw [hmain]
    ring
  change |D - q * A| ≤ 4 * R
  rw [hdecomp]
  calc
    |(D - R * H / (M * d)) - q * (A - H / M)| ≤
        |D - R * H / (M * d)| + |q * (A - H / M)| := abs_sub _ _
    _ = |D - R * H / (M * d)| + q * |A - H / M| := by
      rw [abs_mul, abs_of_nonneg hq]
    _ ≤ 2 * R + q * 2 := add_le_add hD (mul_le_mul_of_nonneg_left hA hq)
    _ ≤ 4 * R := by linarith

/-- The abstract bounding sieve attached to the canonical refined
progression. -/
noncomputable def refinedBinomialBoundingSieve {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : BoundingSieve := by
  classical
  let A := RefinedBaseCandidates S X
  exact
    { support := A.image fun n => n.choose S.k
      prodPrimes := CoverBPZ.refinedSievePrimeProduct S z
      prodPrimes_squarefree :=
        CoverBPZ.refinedSievePrimeProduct_squarefree S z
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
          (CoverBPZ.prime_mem_refinedSievePrimes_of_dvd_product
            S hp hdiv).2.1
        have hkp : S.k < p := by have := S.hk3; omega
        exact (div_lt_one (by exact_mod_cast hp.pos)).mpr
          (by exact_mod_cast hkp) }

/-- On the refined progression, coprimality with the remaining sieve-prime
product is exactly `z`-roughness. -/
theorem coprime_refinedSievePrimeProduct_iff_rough
    {B K n z : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hn : S.k < n)
    (hprog : (CoverBPZ.refinementModulus S : ℤ) ∣
      (n : ℤ) - CoverBPZ.refinementResidue S) :
    Nat.Coprime (CoverBPZ.refinedSievePrimeProduct S z) (n.choose S.k) ↔
      IsZRough z (n.choose S.k) := by
  constructor
  · intro hcop p hp hpz hpChoose
    by_cases hpSmall : p < 2 * S.k
    · exact (refinedProgression_property S hn hprog).1 p hp hpSmall hpChoose
    · have hpLower : 2 * S.k - 1 < p := by
        have hk3 := S.hk3
        omega
      have hmem : p ∈ sievePrimes (2 * S.k - 1) z :=
        mem_sievePrimes.mpr ⟨hp, hpLower, hpz⟩
      have hpProd : p ∣ CoverBPZ.refinedSievePrimeProduct S z := by
        unfold CoverBPZ.refinedSievePrimeProduct sievePrimeProduct
        exact Finset.dvd_prod_of_mem id hmem
      have hpcop : Nat.Coprime p (n.choose S.k) :=
        Nat.Coprime.of_dvd_left hpProd hcop
      exact (hp.coprime_iff_not_dvd.mp hpcop) hpChoose
  · intro hrough
    by_contra hcop
    obtain ⟨p, hp, hpProd, hpChoose⟩ :=
      Nat.Prime.not_coprime_iff_dvd.mp hcop
    have hmem :=
      CoverBPZ.prime_mem_refinedSievePrimes_of_dvd_product S hp hpProd
    exact hrough p hp hmem.2.2 hpChoose

/-- The exact refined set denoted by `S` in BNPZ (6.3). -/
noncomputable def RefinedSiftedCandidates {B K : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) (X z : ℕ) : Finset ℕ := by
  classical
  exact (RefinedBaseCandidates S X).filter fun n =>
    IsZRough z (n.choose S.k)

/-- The refined sieve's weighted sifted sum is literally the cardinality of
`RefinedSiftedCandidates`. -/
theorem refinedBinomialBoundingSieve_siftedSum {B K X z : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    (refinedBinomialBoundingSieve S X z).siftedSum =
      ((RefinedSiftedCandidates S X z).card : ℝ) := by
  classical
  let A := RefinedBaseCandidates S X
  let f : ℕ → ℕ := fun n => n.choose S.k
  rw [BoundingSieve.siftedSum]
  change (∑ m ∈ A.image f,
      if Nat.Coprime (CoverBPZ.refinedSievePrimeProduct S z) m then
        ((A.filter fun n => f n = m).card : ℝ) else 0) = _
  simp_rw [← Finset.sum_filter]
  have hcard :
      (∑ m ∈ (A.image f).filter fun m =>
          Nat.Coprime (CoverBPZ.refinedSievePrimeProduct S z) m,
          (A.filter fun n => f n = m).card) =
        (A.filter fun n =>
          Nat.Coprime (CoverBPZ.refinedSievePrimeProduct S z) (f n)).card := by
    rw [Finset.sum_card_fiberwise_eq_card_filter]
    congr 1
    ext n
    simp only [Finset.mem_filter, Finset.mem_image]
    aesop
  rw [← Nat.cast_sum, hcard]
  norm_cast
  apply congrArg Finset.card
  ext n
  simp only [Finset.mem_filter, RefinedSiftedCandidates]
  constructor
  · rintro ⟨hnA, hcop⟩
    have hnData := (mem_RefinedBaseCandidates (S := S)).mp hnA
    exact ⟨hnA, (coprime_refinedSievePrimeProduct_iff_rough S
      hnData.2.1 hnData.2.2).mp hcop⟩
  · rintro ⟨hnA, hrough⟩
    have hnData := (mem_RefinedBaseCandidates (S := S)).mp hnA
    exact ⟨hnA, (coprime_refinedSievePrimeProduct_iff_rough S
      hnData.2.1 hnData.2.2).mpr hrough⟩

theorem refinedBinomialBoundingSieve_multSum {B K X z d : ℕ}
    (S : CoverBPZ.BPZSection6Input B K) :
    (refinedBinomialBoundingSieve S X z).multSum d =
      ((DivisibleRefinedBaseCandidates S X d).card : ℝ) := by
  classical
  let A := RefinedBaseCandidates S X
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

theorem refinedBinomialBoundingSieve_abs_rem_le
    {B K X z d : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hX : S.k ≤ X / 2)
    (hd : d ∣ CoverBPZ.refinedSievePrimeProduct S z) :
    |(refinedBinomialBoundingSieve S X z).rem d| ≤
      4 * (S.k : ℝ) ^ d.primeFactors.card := by
  rw [BoundingSieve.rem, refinedBinomialBoundingSieve_multSum]
  change |((DivisibleRefinedBaseCandidates S X d).card : ℝ) -
      binomialSieveNu S.k d * (RefinedBaseCandidates S X).card| ≤ _
  exact abs_card_DivisibleRefinedBaseCandidates_sub_nu_mul_base_le
    S hX hd

/-- Ready-to-use finite lower Brun bound for BNPZ's refined set. -/
theorem refinedSiftedCandidates_brunLowerBound
    {B K X z L : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hL : Odd L) :
    (refinedBinomialBoundingSieve S X z).totalMass *
          (refinedBinomialBoundingSieve S X z).mainSum (brunLowerWeight L) -
        (refinedBinomialBoundingSieve S X z).errSum (brunLowerWeight L) ≤
      ((RefinedSiftedCandidates S X z).card : ℝ) := by
  rw [← refinedBinomialBoundingSieve_siftedSum S]
  exact brunLowerBound (refinedBinomialBoundingSieve S X z) hL

/-- Matching finite upper Brun bound on the refined set. -/
theorem refinedSiftedCandidates_brunUpperBound
    {B K X z L : ℕ} (S : CoverBPZ.BPZSection6Input B K)
    (hL : Even L) :
    ((RefinedSiftedCandidates S X z).card : ℝ) ≤
      (refinedBinomialBoundingSieve S X z).totalMass *
          (refinedBinomialBoundingSieve S X z).mainSum (brunUpperWeight L) +
        (refinedBinomialBoundingSieve S X z).errSum (brunUpperWeight L) := by
  rw [← refinedBinomialBoundingSieve_siftedSum S]
  exact brunUpperBound (refinedBinomialBoundingSieve S X z) hL

end Erdos387
