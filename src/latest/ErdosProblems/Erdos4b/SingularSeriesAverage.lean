/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.SingularPrimeAverage

/-!
# Factorization of the averaged large-gap singular series

This file reconnects the averaged inverse-amplification estimate with the
actual truncated singular series.  The identities are finite Euler-product
identities, so no limiting argument or analytic assumption occurs here.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

noncomputable local instance singularSeriesAverageDecidable
    (P : Prop) : Decidable P :=
  Classical.propDecidable P

/-- Split the primes through `y` at the pre-sieve cutoff `w`. -/
theorem primesLE_eq_primesLE_union_roughPrimeSupport
    {w y : ℕ} (hwy : w ≤ y) :
    Nat.primesLE y = Nat.primesLE w ∪
      BoundedGaps.Maynard.roughPrimeSupport w y := by
  ext p
  simp only [Nat.mem_primesLE, Finset.mem_union,
    BoundedGaps.Maynard.roughPrimeSupport, Finset.mem_filter,
    Finset.mem_Icc]
  constructor
  · rintro ⟨hpy, hp⟩
    by_cases hpw : p ≤ w
    · exact Or.inl ⟨hpw, hp⟩
    · exact Or.inr ⟨⟨by omega, hpy⟩, hp⟩
  · rintro (⟨hpw, hp⟩ | ⟨⟨hwp, hpy⟩, hp⟩)
    · exact ⟨hpw.trans hwy, hp⟩
    · exact ⟨hpy, hp⟩

theorem primesLE_disjoint_roughPrimeSupport (w y : ℕ) :
    Disjoint (Nat.primesLE w)
      (BoundedGaps.Maynard.roughPrimeSupport w y) := by
  rw [Finset.disjoint_left]
  intro p hpSmall hpRough
  have hpw := (Nat.mem_primesLE.mp hpSmall).1
  have hwp := (Finset.mem_Icc.mp
    (Finset.mem_filter.mp hpRough).1).1
  omega

/-- Product of the local factors obtained when all `2K` rough forbidden
classes are distinct. -/
noncomputable def genericRoughSingularProduct
    (K w y : ℕ) : ℝ :=
  ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
    genericLargeGapLocalFactor K p

/-- Product of the actual-over-generic local amplifications. -/
noncomputable def roughSingularAmplificationProduct
    (K w y m q : ℕ) : ℝ :=
  ∏ p ∈ BoundedGaps.Maynard.roughPrimeSupport w y,
    largeGapLocalAmplification (preSievedShifts K w) m q p

/-- Exact finite factorization into the pre-sieve part, the universal rough
product, and the actual collision amplification. -/
theorem largeGapSingularSeries_eq_preSieve_mul_generic_mul_amplification
    {K w y m q : ℕ} (hfour : 4 * K ≤ w) (hwy : w ≤ y) :
    largeGapSingularSeries (preSievedShifts K w) m q y =
      largeGapSingularSeries (preSievedShifts K w) m q w *
        genericRoughSingularProduct K w y *
          roughSingularAmplificationProduct K w y m q := by
  let R := BoundedGaps.Maynard.roughPrimeSupport w y
  unfold largeGapSingularSeries
  rw [primesLE_eq_primesLE_union_roughPrimeSupport hwy,
    Finset.prod_union (primesLE_disjoint_roughPrimeSupport w y)]
  change
    (∏ p ∈ Nat.primesLE w,
        largeGapLocalFactor (preSievedShifts K w) m q p) *
      (∏ p ∈ R,
        largeGapLocalFactor (preSievedShifts K w) m q p) = _
  unfold genericRoughSingularProduct roughSingularAmplificationProduct
  change _ * (∏ p ∈ R,
      largeGapLocalFactor (preSievedShifts K w) m q p) =
    _ * (∏ p ∈ R, genericLargeGapLocalFactor K p) *
      ∏ p ∈ R,
        largeGapLocalAmplification (preSievedShifts K w) m q p
  have hrough :
      (∏ p ∈ R,
          largeGapLocalFactor (preSievedShifts K w) m q p) =
        (∏ p ∈ R, genericLargeGapLocalFactor K p) *
          ∏ p ∈ R,
            largeGapLocalAmplification (preSievedShifts K w) m q p := by
    rw [← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    intro p hp
    have hpData := Finset.mem_filter.mp hp
    have hpIcc := Finset.mem_Icc.mp hpData.1
    exact largeGapLocalFactor_eq_generic_mul_amplification
      hpData.2.pos (card_preSievedShifts K w) (by omega)
  rw [hrough]
  ring

theorem roughSingularAmplificationProduct_pos
    {K w y m q : ℕ} (hfour : 4 * K ≤ w) :
    0 < roughSingularAmplificationProduct K w y m q := by
  unfold roughSingularAmplificationProduct
  apply Finset.prod_pos
  intro p hp
  have hpData := Finset.mem_filter.mp hp
  have hpIcc := Finset.mem_Icc.mp hpData.1
  exact lt_of_lt_of_le zero_lt_one
    (one_le_largeGapLocalAmplification (by
      rw [card_preSievedShifts]
      omega))

/-- The previously defined inverse product is literally the inverse of the
amplification product. -/
theorem roughSingularInverseProduct_eq_inv_amplification
    (K w y m q : ℕ) :
    roughSingularInverseProduct K w y m q =
      (roughSingularAmplificationProduct K w y m q)⁻¹ := by
  unfold roughSingularInverseProduct roughSingularAmplificationProduct
  rw [Finset.prod_inv_distrib]

/-- Multiplying the actual singular series by its rough inverse removes all
rough collision factors and leaves the universal base product exactly. -/
theorem roughSingularInverseProduct_mul_largeGapSingularSeries
    {K w y m q : ℕ} (hfour : 4 * K ≤ w) (hwy : w ≤ y) :
    roughSingularInverseProduct K w y m q *
        largeGapSingularSeries (preSievedShifts K w) m q y =
      largeGapSingularSeries (preSievedShifts K w) m q w *
        genericRoughSingularProduct K w y := by
  rw [largeGapSingularSeries_eq_preSieve_mul_generic_mul_amplification
    hfour hwy,
    roughSingularInverseProduct_eq_inv_amplification]
  have hne : roughSingularAmplificationProduct K w y m q ≠ 0 :=
    (roughSingularAmplificationProduct_pos hfour).ne'
  field_simp

/-- Quotient form of the cancellation identity. -/
theorem roughSingularInverseProduct_eq_universal_div_singularSeries
    {K w y m q : ℕ} (hfour : 4 * K ≤ w) (hwy : w ≤ y)
    (hm : Even m) :
    roughSingularInverseProduct K w y m q =
      (largeGapSingularSeries (preSievedShifts K w) m q w *
          genericRoughSingularProduct K w y) /
        largeGapSingularSeries (preSievedShifts K w) m q y := by
  apply (eq_div_iff
    (largeGapSingularSeries_preSievedShifts_pos
      (m := m) (q := q) (y := y) (by omega) hm).ne').mpr
  exact roughSingularInverseProduct_mul_largeGapSingularSeries hfour hwy

/-- The explicit total loss appearing in the auxiliary-prime average. -/
noncomputable def singularAverageLossBound
    (K w A B : ℕ) (C exponent : ℝ) : ℝ :=
  ((4 * K : ℕ) : ℝ) *
    ((BoundedGaps.Maynard.offDiagonalPairs
      (preSievedShifts K w)).card : ℝ) *
      ((((auxiliaryPrimeInterval A B).card : ℝ) *
          (8 / (w : ℝ))) +
        (C * ((B - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
          (w : ℝ) +
        (C * ((A - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
          (w : ℝ))

/-- Source-facing form of the averaged inverse singular-series estimate.
The numerator of every quotient is independent of the auxiliary prime. -/
theorem sum_universal_div_largeGapSingularSeries_primeInterval_lower
    {theta exponent C : ℝ} {X₀ K w A B m y : ℕ}
    (hlevel : BoundedGaps.Maynard.PrimeLevelWitness
      theta exponent C X₀)
    (hfour : 4 * K ≤ w) (hw : 0 < w) (hwy : w ≤ y)
    (hyA : y < A) (hA : 0 < A) (hAB : A ≤ B) (hm : Even m)
    (hBthreshold : X₀ ≤ B - 1) (hAthreshold : X₀ ≤ A - 1)
    (hyBcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (B - 1))
    (hyAcut : y ≤ BoundedGaps.Maynard.modulusCutoff theta (A - 1)) :
    fixedSingularInverseFactor K w y m *
        (((auxiliaryPrimeInterval A B).card : ℝ) -
          singularAverageLossBound K w A B C exponent) ≤
      ∑ q ∈ auxiliaryPrimeInterval A B,
        (largeGapSingularSeries (preSievedShifts K w) m q w *
            genericRoughSingularProduct K w y) /
          largeGapSingularSeries (preSievedShifts K w) m q y := by
  have hrough := sum_roughSingularInverseProduct_primeInterval_lower
    (m := m) (y := y) hlevel hfour hw hyA hA hAB hBthreshold
      hAthreshold hyBcut hyAcut
  rw [show singularAverageLossBound K w A B C exponent =
      ((4 * K : ℕ) : ℝ) *
        ((BoundedGaps.Maynard.offDiagonalPairs
          (preSievedShifts K w)).card : ℝ) *
          ((((auxiliaryPrimeInterval A B).card : ℝ) *
              (8 / (w : ℝ))) +
            (C * ((B - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((B - 1 : ℕ) : ℝ)) exponent) /
              (w : ℝ) +
            (C * ((A - 1 : ℕ) : ℝ) /
                Real.rpow (Real.log ((A - 1 : ℕ) : ℝ)) exponent) /
              (w : ℝ)) by rfl]
  calc
    _ ≤ ∑ q ∈ auxiliaryPrimeInterval A B,
        roughSingularInverseProduct K w y m q := hrough
    _ = _ := by
      apply Finset.sum_congr rfl
      intro q hq
      exact roughSingularInverseProduct_eq_universal_div_singularSeries
        hfour hwy hm

end

end Erdos4b
