/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralCollisionKernelBound

/-!
# Matrix estimates for the collision transform

The fixed-lcm estimate is applied to the two families of row and column
constraints.  Coprimality with the pre-sieve modulus is retained before
enlarging the finite matrix sum to a prime Euler product.
-/

namespace Erdos4b

noncomputable section

open scoped ArithmeticFunction.omega BigOperators

noncomputable local instance (p : Prop) : Decidable p :=
  Classical.propDecidable p

/-- If both allocated `Y` factors are nonzero, every constraint coordinate
is coprime to the pre-sieve modulus. -/
theorem constraintProduct_coprime_of_allocatedYFactors_ne_zero
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    {u v : H → ℕ} {x : TupleLcmAllocation A}
    (hl : tupleLcmAllocationCommonFirstYFactor y u x ≠ 0)
    (hr : tupleLcmAllocationCommonSecondYFactor y v x ≠ 0) :
    (BoundedGaps.Maynard.divisorTupleProduct H A).Coprime W := by
  have hlSupport := hy _
    (tupleLcmAllocationCommonFirstYFactor_ne_zero_y_ne_zero hl)
  have hrSupport := hy _
    (tupleLcmAllocationCommonSecondYFactor_ne_zero_y_ne_zero hr)
  unfold BoundedGaps.Maynard.divisorTupleProduct
  apply Nat.Coprime.prod_left
  intro h hh
  have hconstraint := tupleLcmAllocation_constraint_dvd_lcm_commonLowers
    hASq u v x h
  exact Nat.Coprime.of_dvd_left
    (hconstraint.trans (Nat.lcm_dvd_mul _ _))
    ((hlSupport.coordinate_coprime_W h).mul_left
      (hrSupport.coordinate_coprime_W h))

/-- A fixed constraint meeting the pre-sieve modulus contributes zero to
the complete transformed quadratic. -/
theorem fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime_modulus
    {H : Finset ℕ} {R W : ℕ} {A : H → ℕ}
    {y : (H → ℕ) → ℝ}
    (hy : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hASq : ∀ h : H, Squarefree (A h))
    (hnot : ¬(BoundedGaps.Maynard.divisorTupleProduct H A).Coprime W) :
    fixedLcmCompatiblePairYValue R y A = 0 := by
  unfold fixedLcmCompatiblePairYValue
  apply Finset.sum_eq_zero
  intro s hs
  apply Finset.sum_eq_zero
  intro u hu
  have hsum : (∑ x : TupleLcmAllocation A,
      tupleLcmAllocationMobiusWeight x *
        tupleLcmAllocationCommonFirstYFactor y
          (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x *
        tupleLcmAllocationCommonSecondYFactor y
          (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x) = 0 := by
    apply Finset.sum_eq_zero
    intro x hx
    by_cases hl : tupleLcmAllocationCommonFirstYFactor y
        (BoundedGaps.Maynard.leftCrossLowerTuple H u s) x = 0
    · simp [hl]
    by_cases hr : tupleLcmAllocationCommonSecondYFactor y
        (BoundedGaps.Maynard.rightCrossLowerTuple H u s) x = 0
    · simp [hr]
    exact (hnot
      (constraintProduct_coprime_of_allocatedYFactors_ne_zero
        hy hASq hl hr)).elim
  rw [hsum, mul_zero]

/-- The combinatorial allocation loss for one prime. -/
def fixedLcmPrimeCost (H : Finset ℕ) : ℕ :=
  4 ^ Fintype.card H * 2 ^ Fintype.card (CrossBaseLabel H)

/-- The complete constraint cost after removing the ordinary base Euler
product and the square of the `Y` bound. -/
noncomputable def fixedLcmTotientCost (H : Finset ℕ) (a : ℕ) : ℝ :=
  (fixedLcmPrimeCost H : ℝ) ^ ω a / Nat.totient a

theorem fixedLcmTotientCost_nonneg (H : Finset ℕ) (a : ℕ) :
    0 ≤ fixedLcmTotientCost H a := by
  unfold fixedLcmTotientCost
  positivity

theorem fixedLcmTotientCost_eq_primeFactors_product
    (H : Finset ℕ) {a : ℕ} (ha : Squarefree a) :
    fixedLcmTotientCost H a =
      ∏ p ∈ a.primeFactors,
        (fixedLcmPrimeCost H : ℝ) / Nat.totient p := by
  symm
  rw [Finset.prod_div_distrib, Finset.prod_const, ← Nat.cast_prod,
    ← BoundedGaps.Maynard.totient_eq_prod_primeFactors_of_squarefree ha]
  rfl

theorem abs_fixedLcmCompatiblePairYValue_le_totientCost
    {H : Finset ℕ} {A : H → ℕ} {y : (H → ℕ) → ℝ} {B : ℝ}
    (hB : 0 ≤ B) (hyBound : ∀ r, |y r| ≤ B)
    {R W : ℕ}
    (hySupport : BoundedGaps.Maynard.IsSupportedMaynardY H R W y)
    (hAtotal : Squarefree
      (BoundedGaps.Maynard.divisorTupleProduct H A)) :
    |fixedLcmCompatiblePairYValue R y A| ≤
      (B ^ 2 * crossBaseEulerProduct H R) *
        fixedLcmTotientCost H
          (BoundedGaps.Maynard.divisorTupleProduct H A) := by
  have hbound := abs_fixedLcmCompatiblePairYValue_le_baseEulerProduct
    hB hyBound hySupport hAtotal
  convert hbound using 1
  unfold fixedLcmTotientCost fixedLcmPrimeCost
  push_cast
  ring

/-- Matching incidence has a unique edge above each prime. -/
theorem crossAuxiliaryPrimeIncidence_fst_injOn
    {H : Finset ℕ} (Q : ℕ) {A : CrossAuxiliaryValueMatrix H}
    (hmatch : IsCrossAuxiliaryPrimeMatching A) :
    Set.InjOn Prod.fst
      (crossAuxiliaryPrimeIncidence Q A : Set (ℕ × (H × H))) := by
  rintro ⟨p, ba⟩ hpa ⟨p', bb⟩ hpb hpp
  change p = p' at hpp
  subst p'
  have hpa' := mem_crossAuxiliaryPrimeIncidence_iff.mp hpa
  have hpb' := mem_crossAuxiliaryPrimeIncidence_iff.mp hpb
  have hba := eq_of_prime_dvd_crossAuxiliary_entries_of_matching
    hmatch hpa'.2.1 hpa'.2.2 hpb'.2.2
  exact Prod.ext rfl hba

/-- The primes represented in the matrix incidence set are exactly the
prime factors of the product of its entries. -/
theorem crossAuxiliaryPrimeIncidence_fst_image
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q) :
    (crossAuxiliaryPrimeIncidence Q A).image Prod.fst =
      (∏ ba : H × H, A ba).primeFactors := by
  have hAData := mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA
  have hprodPos : 0 < ∏ ba : H × H, A ba :=
    Finset.prod_pos fun ba hba ↦ (hAData.1 ba).1
  ext p
  constructor
  · intro hpMem
    obtain ⟨⟨p', ba⟩, hinc, heq⟩ := Finset.mem_image.mp hpMem
    change p' = p at heq
    subst p'
    have hpData := mem_crossAuxiliaryPrimeIncidence_iff.mp hinc
    exact Nat.mem_primeFactors.mpr ⟨hpData.2.1,
      hpData.2.2.trans (Finset.dvd_prod_of_mem A (Finset.mem_univ ba)),
      hprodPos.ne'⟩
  · intro hpMem
    have hp := Nat.prime_of_mem_primeFactors hpMem
    obtain ⟨ba, hba, hpA⟩ := (hp.prime.dvd_finsetProd_iff A).mp
      (Nat.dvd_of_mem_primeFactors hpMem)
    refine Finset.mem_image.mpr ⟨(p, ba), ?_, rfl⟩
    exact mem_crossAuxiliaryPrimeIncidence_iff.mpr ⟨
      prime_le_cutoff_of_dvd_crossAuxiliary_entry
        (hAData.1 ba).1 (hAData.1 ba).2 hp hpA, hp, hpA⟩

theorem prod_entryPrimeFactors_eq_prod_totalPrimeFactors
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (hmatch : IsCrossAuxiliaryPrimeMatching A) (f : ℕ → ℝ) :
    (∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p) =
      ∏ p ∈ (∏ ba : H × H, A ba).primeFactors, f p := by
  rw [prod_entryPrimeFactors_eq_prod_primeIncidence hA (fun p _ ↦ f p)]
  rw [← crossAuxiliaryPrimeIncidence_fst_image hA]
  exact (Finset.prod_image (f := f)
    (crossAuxiliaryPrimeIncidence_fst_injOn Q hmatch)).symm

theorem fixedLcmTotientCost_eq_entryPrimeFactors_product
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (hmatch : IsCrossAuxiliaryPrimeMatching A) :
    fixedLcmTotientCost H (∏ ba : H × H, A ba) =
      ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
        (fixedLcmPrimeCost H : ℝ) / Nat.totient p := by
  rw [prod_entryPrimeFactors_eq_prod_totalPrimeFactors hA hmatch]
  exact fixedLcmTotientCost_eq_primeFactors_product H
    (squarefree_crossAuxiliary_entryProduct_of_matching hmatch
      (mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA).2)

/-- The absolute local matrix factor.  At an affine collision it is of
order `1 / p`; at a generic prime it is of order `1 / p²`. -/
noncomputable def crossMatrixPrimeWeight
    {H : Finset ℕ} (m q p : ℕ) (ba : H × H) : ℝ :=
  ((fixedLcmPrimeCost H : ℝ) / Nat.totient p) ^ 2 *
    (if (p : ℤ) ∣ crossAffineDifference m q ba then
      (Nat.totient p : ℝ) else 1)

theorem crossMatrixPrimeWeight_nonneg
    {H : Finset ℕ} (m q p : ℕ) (ba : H × H) :
    0 ≤ crossMatrixPrimeWeight m q p ba := by
  unfold crossMatrixPrimeWeight
  apply mul_nonneg (sq_nonneg _)
  split <;> positivity

theorem abs_affineCollisionWeight_prime_eq_totient
    {H : Finset ℕ} (m q : ℕ) (ba : H × H) {p : ℕ}
    (hp : p.Prime) :
    |affineCollisionWeight m q ba p| =
      if (p : ℤ) ∣ crossAffineDifference m q ba then
        (Nat.totient p : ℝ) else 1 := by
  rw [abs_affineCollisionWeight_prime m q ba hp,
    Nat.totient_prime hp, Nat.cast_sub hp.one_le, Nat.cast_one]

theorem fixedLcmTotientCost_sq_mul_abs_affineWeight_eq_primeProducts
    {H : Finset ℕ} {Q : ℕ} {A : CrossAuxiliaryValueMatrix H}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (hmatch : IsCrossAuxiliaryPrimeMatching A) (m q : ℕ) :
    fixedLcmTotientCost H (∏ ba : H × H, A ba) ^ 2 *
        |crossAuxiliaryAffineMobiusWeight m q A| =
      ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
        crossMatrixPrimeWeight m q p ba := by
  rw [fixedLcmTotientCost_eq_entryPrimeFactors_product hA hmatch,
    crossAuxiliaryAffineMobiusWeight_eq_entryPrimeProducts m q
      (mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA).2,
    Finset.abs_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro ba hba
  rw [Finset.abs_prod, ← Finset.prod_pow, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro p hpMem
  rw [abs_affineCollisionWeight_prime_eq_totient m q ba
    (Nat.prime_of_mem_primeFactors hpMem)]
  rfl

/-- The two fixed-lcm bounds combine into a common ordinary scale and an
explicit product of prime-local auxiliary factors. -/
theorem abs_crossAuxiliaryYMatrixTerm_le_primeProducts
    {H : Finset ℕ} {Q RD RE WD WE m q : ℕ}
    {A : CrossAuxiliaryValueMatrix H}
    {yD yE : (H → ℕ) → ℝ} {BD BE : ℝ}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (hmatch : IsCrossAuxiliaryPrimeMatching A)
    (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hyDBound : ∀ r, |yD r| ≤ BD) (hyEBound : ∀ r, |yE r| ≤ BE) :
    |crossAuxiliaryAffineMobiusWeight m q A *
        (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
          fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))| ≤
      ((BD ^ 2 * crossBaseEulerProduct H RD) *
        (BE ^ 2 * crossBaseEulerProduct H RE)) *
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
          crossMatrixPrimeWeight m q p ba := by
  let a := ∏ ba : H × H, A ba
  let SD := BD ^ 2 * crossBaseEulerProduct H RD
  let SE := BE ^ 2 * crossBaseEulerProduct H RE
  let c := fixedLcmTotientCost H a
  have haSq : Squarefree a :=
    squarefree_crossAuxiliary_entryProduct_of_matching hmatch
      (mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA).2
  have hcol := divisorTupleProduct_crossAuxiliaryColumnLcm_eq_entryProduct hmatch
  have hrow := divisorTupleProduct_crossAuxiliaryRowLcm_eq_entryProduct hmatch
  have hcolSq : Squarefree (BoundedGaps.Maynard.divisorTupleProduct H
      (crossAuxiliaryColumnLcm A)) := by
    rw [hcol]
    exact haSq
  have hrowSq : Squarefree (BoundedGaps.Maynard.divisorTupleProduct H
      (crossAuxiliaryRowLcm A)) := by
    rw [hrow]
    exact haSq
  have hD : |fixedLcmCompatiblePairYValue RD yD
      (crossAuxiliaryColumnLcm A)| ≤ SD * c := by
    simpa only [hcol] using
      abs_fixedLcmCompatiblePairYValue_le_totientCost
        hBD hyDBound hyD hcolSq
  have hE : |fixedLcmCompatiblePairYValue RE yE
      (crossAuxiliaryRowLcm A)| ≤ SE * c := by
    simpa only [hrow] using
      abs_fixedLcmCompatiblePairYValue_le_totientCost
        hBE hyEBound hyE hrowSq
  have hSD : 0 ≤ SD := mul_nonneg (sq_nonneg BD)
    (crossBaseEulerProduct_nonneg H RD)
  have hc : 0 ≤ c := fixedLcmTotientCost_nonneg H a
  calc
    _ = |crossAuxiliaryAffineMobiusWeight m q A| *
        (|fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A)| *
          |fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A)|) := by
      simp only [abs_mul]
    _ ≤ |crossAuxiliaryAffineMobiusWeight m q A| *
        ((SD * c) * (SE * c)) := by
      exact mul_le_mul_of_nonneg_left
        (mul_le_mul hD hE (abs_nonneg _) (mul_nonneg hSD hc))
        (abs_nonneg _)
    _ = (SD * SE) *
        (c ^ 2 * |crossAuxiliaryAffineMobiusWeight m q A|) := by ring
    _ = _ := by
      rw [show c ^ 2 * |crossAuxiliaryAffineMobiusWeight m q A| =
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
          crossMatrixPrimeWeight m q p ba from
        fixedLcmTotientCost_sq_mul_abs_affineWeight_eq_primeProducts
          hA hmatch m q]

/-- Local exclusion of every prime occurring in either pre-sieve modulus. -/
noncomputable def crossMatrixSievedPrimeWeight
    {H : Finset ℕ} (WD WE m q p : ℕ) (ba : H × H) : ℝ :=
  if p ∣ WD ∨ p ∣ WE then 0 else crossMatrixPrimeWeight m q p ba

theorem crossMatrixSievedPrimeWeight_nonneg
    {H : Finset ℕ} (WD WE m q p : ℕ) (ba : H × H) :
    0 ≤ crossMatrixSievedPrimeWeight WD WE m q p ba := by
  unfold crossMatrixSievedPrimeWeight
  split
  · exact le_rfl
  · exact crossMatrixPrimeWeight_nonneg m q p ba

theorem crossMatrixSievedPrimeProducts_eq_of_coprime
    {H : Finset ℕ} {A : CrossAuxiliaryValueMatrix H}
    {WD WE : ℕ} (m q : ℕ)
    (hD : (∏ ba : H × H, A ba).Coprime WD)
    (hE : (∏ ba : H × H, A ba).Coprime WE) :
    (∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
      crossMatrixSievedPrimeWeight WD WE m q p ba) =
      ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
        crossMatrixPrimeWeight m q p ba := by
  apply Finset.prod_congr rfl
  intro ba hba
  apply Finset.prod_congr rfl
  intro p hpMem
  have hp := Nat.prime_of_mem_primeFactors hpMem
  have hpProd : p ∣ ∏ bb : H × H, A bb :=
    (Nat.dvd_of_mem_primeFactors hpMem).trans
      (Finset.dvd_prod_of_mem A (Finset.mem_univ ba))
  have hnot : ¬(p ∣ WD ∨ p ∣ WE) := by
    rintro (hpD | hpE)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hD hpProd hpD)
    · exact hp.ne_one (Nat.eq_one_of_dvd_coprimes hE hpProd hpE)
  exact if_neg hnot

/-- Support-aware matrix majorant.  A forbidden auxiliary prime makes the
actual term vanish before any estimate is used. -/
theorem abs_crossAuxiliaryYMatrixTerm_le_sievedPrimeProducts
    {H : Finset ℕ} {Q RD RE WD WE m q : ℕ}
    {A : CrossAuxiliaryValueMatrix H}
    {yD yE : (H → ℕ) → ℝ} {BD BE : ℝ}
    (hA : A ∈ crossAuxiliarySquarefreeValueMatrixBox H Q)
    (hmatch : IsCrossAuxiliaryPrimeMatching A)
    (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hyDBound : ∀ r, |yD r| ≤ BD) (hyEBound : ∀ r, |yE r| ≤ BE) :
    |crossAuxiliaryAffineMobiusWeight m q A *
        (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
          fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))| ≤
      ((BD ^ 2 * crossBaseEulerProduct H RD) *
        (BE ^ 2 * crossBaseEulerProduct H RE)) *
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
          crossMatrixSievedPrimeWeight WD WE m q p ba := by
  have hscale : 0 ≤ (BD ^ 2 * crossBaseEulerProduct H RD) *
      (BE ^ 2 * crossBaseEulerProduct H RE) := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg BD) (crossBaseEulerProduct_nonneg H RD))
      (mul_nonneg (sq_nonneg BE) (crossBaseEulerProduct_nonneg H RE))
  have hprod : 0 ≤ ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
      crossMatrixSievedPrimeWeight WD WE m q p ba := by
    exact Finset.prod_nonneg fun ba hba ↦ Finset.prod_nonneg fun p hp ↦
      crossMatrixSievedPrimeWeight_nonneg WD WE m q p ba
  have hASq := (mem_crossAuxiliarySquarefreeValueMatrixBox_iff.mp hA).2
  by_cases hD : (∏ ba : H × H, A ba).Coprime WD
  · by_cases hE : (∏ ba : H × H, A ba).Coprime WE
    · rw [crossMatrixSievedPrimeProducts_eq_of_coprime m q hD hE]
      exact abs_crossAuxiliaryYMatrixTerm_le_primeProducts
        hA hmatch hBD hBE hyD hyE hyDBound hyEBound
    · have hnot : ¬(BoundedGaps.Maynard.divisorTupleProduct H
          (crossAuxiliaryRowLcm A)).Coprime WE := by
        simpa only [divisorTupleProduct_crossAuxiliaryRowLcm_eq_entryProduct
          hmatch] using hE
      rw [fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime_modulus
        hyE (crossAuxiliaryRowLcm_squarefree_of_entries hASq) hnot,
        mul_zero, mul_zero, abs_zero]
      exact mul_nonneg hscale hprod
  · have hnot : ¬(BoundedGaps.Maynard.divisorTupleProduct H
        (crossAuxiliaryColumnLcm A)).Coprime WD := by
      simpa only [divisorTupleProduct_crossAuxiliaryColumnLcm_eq_entryProduct
        hmatch] using hD
    rw [fixedLcmCompatiblePairYValue_eq_zero_of_not_coprime_modulus
      hyD (crossAuxiliaryColumnLcm_squarefree_of_entries hASq) hnot,
      zero_mul, mul_zero, abs_zero]
    exact mul_nonneg hscale hprod

theorem oneCrossAuxiliaryValueMatrix_isMatching (H : Finset ℕ) :
    IsCrossAuxiliaryPrimeMatching (oneCrossAuxiliaryValueMatrix H) := by
  constructor <;> intro a b hab <;> simp

theorem oneCrossAuxiliaryValueMatrix_mem_matchingBox
    {H : Finset ℕ} {Q : ℕ} (hQ : 0 < Q) :
    oneCrossAuxiliaryValueMatrix H ∈
      crossAuxiliaryMatchingValueMatrixBox H Q := by
  exact Finset.mem_filter.mpr ⟨
    oneCrossAuxiliaryValueMatrix_mem_squarefreeBox hQ,
    oneCrossAuxiliaryValueMatrix_isMatching H⟩

/-- Deleting the unit matrix deletes exactly the constant term of the
Euler-product majorant. -/
theorem sum_matchingMatrix_erase_primeProducts_le_eulerProduct_sub_one
    {H : Finset ℕ} {Q : ℕ} (hQ : 0 < Q) (f : ℕ → H × H → ℝ)
    (hf : ∀ p ba, 0 ≤ f p ba) :
    (∑ A ∈ (crossAuxiliaryMatchingValueMatrixBox H Q).erase
        (oneCrossAuxiliaryValueMatrix H),
      ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p ba) ≤
      (∏ x ∈ crossAuxiliaryPrimeEdgeUniverse H Q,
        (1 + f x.1 x.2)) - 1 := by
  let F : CrossAuxiliaryValueMatrix H → ℝ := fun A ↦
    ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors, f p ba
  have hone : F (oneCrossAuxiliaryValueMatrix H) = 1 := by
    simp [F, oneCrossAuxiliaryValueMatrix]
  have hsplit := Finset.sum_erase_add
    (s := crossAuxiliaryMatchingValueMatrixBox H Q) (f := F)
    (oneCrossAuxiliaryValueMatrix_mem_matchingBox (H := H) hQ)
  have hfull := sum_matchingMatrix_primeProducts_le_eulerProduct
    (H := H) (Q := Q) f hf
  change (∑ A ∈ (crossAuxiliaryMatchingValueMatrixBox H Q).erase
    (oneCrossAuxiliaryValueMatrix H), F A) ≤ _
  change (∑ A ∈ crossAuxiliaryMatchingValueMatrixBox H Q, F A) ≤ _ at hfull
  rw [hone] at hsplit
  linarith

theorem doubledSelbergCrossYTail_eq_matching_sum
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {yD yE : (H → ℕ) → ℝ}
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE) :
    doubledSelbergCrossYTail H RD RE yD yE m q =
      ∑ A ∈ (crossAuxiliaryMatchingValueMatrixBox H (RD * RD)).erase
          (oneCrossAuxiliaryValueMatrix H),
        crossAuxiliaryAffineMobiusWeight m q A *
          (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
            fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A)) := by
  unfold doubledSelbergCrossYTail
  symm
  apply Finset.sum_subset
  · intro A hA
    have hdata := Finset.mem_erase.mp hA
    exact Finset.mem_erase.mpr ⟨hdata.1, (Finset.mem_filter.mp hdata.2).1⟩
  · intro A hA hnot
    have hdata := Finset.mem_erase.mp hA
    have hnotmatch : ¬IsCrossAuxiliaryPrimeMatching A := by
      intro hmatch
      exact hnot (Finset.mem_erase.mpr ⟨hdata.1,
        Finset.mem_filter.mpr ⟨hdata.2, hmatch⟩⟩)
    exact crossAuxiliaryYMatrixTerm_eq_zero_of_not_matching
      hdata.2 hyD hyE hnotmatch

/-- Finite Euler-product bound for the entire transformed collision tail,
with the small-prime support conditions and the missing constant term kept
explicitly. -/
theorem abs_doubledSelbergCrossYTail_le_sievedEulerProduct
    {H : Finset ℕ} {RD RE WD WE m q : ℕ}
    {yD yE : (H → ℕ) → ℝ} {BD BE : ℝ}
    (hRD : 0 < RD) (hBD : 0 ≤ BD) (hBE : 0 ≤ BE)
    (hyD : BoundedGaps.Maynard.IsSupportedMaynardY H RD WD yD)
    (hyE : BoundedGaps.Maynard.IsSupportedMaynardY H RE WE yE)
    (hyDBound : ∀ r, |yD r| ≤ BD) (hyEBound : ∀ r, |yE r| ≤ BE) :
    |doubledSelbergCrossYTail H RD RE yD yE m q| ≤
      ((BD ^ 2 * crossBaseEulerProduct H RD) *
        (BE ^ 2 * crossBaseEulerProduct H RE)) *
      ((∏ x ∈ crossAuxiliaryPrimeEdgeUniverse H (RD * RD),
        (1 + crossMatrixSievedPrimeWeight WD WE m q x.1 x.2)) - 1) := by
  let S := (crossAuxiliaryMatchingValueMatrixBox H (RD * RD)).erase
    (oneCrossAuxiliaryValueMatrix H)
  let scale := (BD ^ 2 * crossBaseEulerProduct H RD) *
    (BE ^ 2 * crossBaseEulerProduct H RE)
  have hscale : 0 ≤ scale := by
    exact mul_nonneg
      (mul_nonneg (sq_nonneg BD) (crossBaseEulerProduct_nonneg H RD))
      (mul_nonneg (sq_nonneg BE) (crossBaseEulerProduct_nonneg H RE))
  rw [doubledSelbergCrossYTail_eq_matching_sum hyD hyE]
  calc
    _ ≤ ∑ A ∈ S,
        |crossAuxiliaryAffineMobiusWeight m q A *
          (fixedLcmCompatiblePairYValue RD yD (crossAuxiliaryColumnLcm A) *
            fixedLcmCompatiblePairYValue RE yE (crossAuxiliaryRowLcm A))| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ A ∈ S, scale *
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
          crossMatrixSievedPrimeWeight WD WE m q p ba := by
      apply Finset.sum_le_sum
      intro A hA
      have hdata := Finset.mem_filter.mp (Finset.mem_erase.mp hA).2
      exact abs_crossAuxiliaryYMatrixTerm_le_sievedPrimeProducts
        hdata.1 hdata.2 hBD hBE hyD hyE hyDBound hyEBound
    _ = scale * ∑ A ∈ S,
        ∏ ba : H × H, ∏ p ∈ (A ba).primeFactors,
          crossMatrixSievedPrimeWeight WD WE m q p ba := by
      rw [Finset.mul_sum]
    _ ≤ _ := by
      apply mul_le_mul_of_nonneg_left _ hscale
      exact sum_matchingMatrix_erase_primeProducts_le_eulerProduct_sub_one
        (Nat.mul_pos hRD hRD) (crossMatrixSievedPrimeWeight WD WE m q)
        (crossMatrixSievedPrimeWeight_nonneg WD WE m q)

end

end Erdos4b
