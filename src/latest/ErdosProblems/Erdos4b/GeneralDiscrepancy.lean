/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralPinned

/-!
# Aggregate discrepancy bounds for the general pinned system

The arbitrary-overlap CRT reduction in `GeneralPinned.lean` bounds one
divisor quadruple by maximal prime-progression discrepancies.  This file
performs the exact finite triangle-inequality aggregation over the pinned
coordinate and all four divisor tuples.  The result is the direct input to
Bombieri--Vinogradov after grouping equal lcm moduli.
-/

namespace Erdos4b

open scoped BigOperators

noncomputable section

/-- A reusable fivefold finite triangle inequality in the exact indexing
shape of the doubled pinned Selberg expansion. -/
theorem abs_fivefold_sum_le_sum_bound
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    (f g : H → (H → ℕ) → (H → ℕ) → (H → ℕ) → (H → ℕ) → ℝ)
    (hfg : ∀ h : H, ∀ d ∈ D, ∀ e ∈ E, ∀ d' ∈ D, ∀ e' ∈ E,
      |f h d e d' e'| ≤ g h d e d' e') :
    |∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        f h d e d' e'| ≤
      ∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        g h d e d' e' := by
  calc
    |∑ h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
        f h d e d' e'| ≤
        ∑ h : H, |∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
          f h d e d' e'| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro h hh
      calc
        |∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
            f h d e d' e'| ≤
            ∑ d ∈ D, |∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
              f h d e d' e'| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ _ := by
          apply Finset.sum_le_sum
          intro d hd
          calc
            |∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E, f h d e d' e'| ≤
                ∑ e ∈ E, |∑ d' ∈ D, ∑ e' ∈ E,
                  f h d e d' e'| := Finset.abs_sum_le_sum_abs _ _
            _ ≤ _ := by
              apply Finset.sum_le_sum
              intro e he
              calc
                |∑ d' ∈ D, ∑ e' ∈ E, f h d e d' e'| ≤
                    ∑ d' ∈ D, |∑ e' ∈ E,
                      f h d e d' e'| := Finset.abs_sum_le_sum_abs _ _
                _ ≤ _ := by
                  apply Finset.sum_le_sum
                  intro d' hd'
                  calc
                    |∑ e' ∈ E, f h d e d' e'| ≤
                        ∑ e' ∈ E, |f h d e d' e'| :=
                          Finset.abs_sum_le_sum_abs _ _
                    _ ≤ _ := by
                      apply Finset.sum_le_sum
                      intro e' he'
                      exact hfg h d hd e he d' hd' e' he'

/-- The literal coefficient-weighted maximal discrepancy sum produced by
the unseparated pinned lcm system. -/
noncomputable def pinnedGeneralWeightedDiscrepancySum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (x₁ x₂ : ℕ) : ℝ :=
  ∑ _h : H, ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
    |lambda d e| * |lambda d' e'| *
      (BoundedGaps.Maynard.maxProgressionDiscrepancy x₁
          (pinnedGeneralCrtModulus H d e d' e') +
        BoundedGaps.Maynard.maxProgressionDiscrepancy x₂
          (pinnedGeneralCrtModulus H d e d' e'))

/-- A convenient single index for the four divisor tuples. -/
abbrev PinnedGeneralQuadrupleIndex (H : Finset ℕ) :=
  (H → ℕ) × ((H → ℕ) × ((H → ℕ) × (H → ℕ)))

def pinnedGeneralQuadrupleIndex
    {H : Finset ℕ} (D E : Finset (H → ℕ)) :
    Finset (PinnedGeneralQuadrupleIndex H) :=
  D.product (E.product (D.product E))

def pinnedGeneralIndexModulus {H : Finset ℕ}
    (i : PinnedGeneralQuadrupleIndex H) : ℕ :=
  pinnedGeneralCrtModulus H i.1 i.2.1 i.2.2.1 i.2.2.2

noncomputable def pinnedGeneralIndexCoefficient {H : Finset ℕ}
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (i : PinnedGeneralQuadrupleIndex H) : ℝ :=
  |lambda i.1 i.2.1| * |lambda i.2.2.1 i.2.2.2|

/-- The finite set of lcm moduli that actually occur in the divisor
quadruple expansion. -/
def pinnedGeneralModulusSet
    {H : Finset ℕ} (D E : Finset (H → ℕ)) : Finset ℕ :=
  (pinnedGeneralQuadrupleIndex D E).image pinnedGeneralIndexModulus

/-- Total absolute coefficient mass over the fiber of one lcm modulus.
Bounding this fiber mass by a divisor-power envelope is the exact remaining
multiplicity estimate before Bombieri--Vinogradov. -/
noncomputable def pinnedGeneralModulusCoefficientMass
    {H : Finset ℕ} (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (M : ℕ) : ℝ :=
  ∑ i ∈ pinnedGeneralQuadrupleIndex D E with
      pinnedGeneralIndexModulus i = M,
    pinnedGeneralIndexCoefficient lambda i

noncomputable def pinnedGeneralGroupedDiscrepancySum
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (x₁ x₂ : ℕ) : ℝ :=
  ∑ M ∈ pinnedGeneralModulusSet D E,
    pinnedGeneralModulusCoefficientMass D E lambda M *
      (BoundedGaps.Maynard.maxProgressionDiscrepancy x₁ M +
        BoundedGaps.Maynard.maxProgressionDiscrepancy x₂ M)

/-- Group the repeated divisor-quadruple moduli into coefficient fibers.
This is an exact identity, not an estimate. -/
theorem pinnedGeneralWeightedDiscrepancySum_eq_card_mul_grouped
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (x₁ x₂ : ℕ) :
    pinnedGeneralWeightedDiscrepancySum H D E lambda x₁ x₂ =
      (H.card : ℝ) *
        pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂ := by
  classical
  let S := pinnedGeneralQuadrupleIndex D E
  let g : PinnedGeneralQuadrupleIndex H → ℕ := pinnedGeneralIndexModulus
  let c : PinnedGeneralQuadrupleIndex H → ℝ :=
    pinnedGeneralIndexCoefficient lambda
  let Δ : ℕ → ℝ := fun M =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy x₁ M +
      BoundedGaps.Maynard.maxProgressionDiscrepancy x₂ M
  let T : ℝ :=
    ∑ d ∈ D, ∑ e ∈ E, ∑ d' ∈ D, ∑ e' ∈ E,
      |lambda d e| * |lambda d' e'| *
        (BoundedGaps.Maynard.maxProgressionDiscrepancy x₁
            (pinnedGeneralCrtModulus H d e d' e') +
          BoundedGaps.Maynard.maxProgressionDiscrepancy x₂
            (pinnedGeneralCrtModulus H d e d' e'))
  have hmaps : ∀ i ∈ S, g i ∈ pinnedGeneralModulusSet D E := by
    intro i hi
    exact Finset.mem_image.mpr ⟨i, hi, rfl⟩
  have hfiber :
      (∑ M ∈ pinnedGeneralModulusSet D E,
          ∑ i ∈ S with g i = M, c i * Δ (g i)) =
        ∑ i ∈ S, c i * Δ (g i) :=
    Finset.sum_fiberwise_of_maps_to hmaps (fun i => c i * Δ (g i))
  have hgroup :
      (∑ i ∈ S, c i * Δ (g i)) =
        pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂ := by
    rw [← hfiber]
    unfold pinnedGeneralGroupedDiscrepancySum
    apply Finset.sum_congr rfl
    intro M hM
    unfold pinnedGeneralModulusCoefficientMass
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i hi
    have hgi : g i = M := (Finset.mem_filter.mp hi).2
    have hgi' : pinnedGeneralIndexModulus i = M := by
      simpa [g] using hgi
    simp only [c, g, Δ]
    rw [hgi']
  have hT : T =
      pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂ := by
    calc
      T = ∑ i ∈ S, c i * Δ (g i) := by
        dsimp [T, S, c, g, Δ, pinnedGeneralQuadrupleIndex,
          pinnedGeneralIndexCoefficient, pinnedGeneralIndexModulus]
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro d hd
        rw [Finset.sum_product]
        apply Finset.sum_congr rfl
        intro e he
        rw [Finset.sum_product]
      _ = _ := hgroup
  unfold pinnedGeneralWeightedDiscrepancySum
  change (∑ _h : H, T) =
    (H.card : ℝ) * pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂
  rw [show (∑ _h : H, T) = (H.card : ℝ) * T by simp, hT]

theorem pinnedGeneralWeightedDiscrepancySum_nonneg
    (H : Finset ℕ) (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (x₁ x₂ : ℕ) :
    0 ≤ pinnedGeneralWeightedDiscrepancySum H D E lambda x₁ x₂ := by
  unfold pinnedGeneralWeightedDiscrepancySum
  apply Finset.sum_nonneg
  intro h hh
  apply Finset.sum_nonneg
  intro d hd
  apply Finset.sum_nonneg
  intro e he
  apply Finset.sum_nonneg
  intro d' hd'
  apply Finset.sum_nonneg
  intro e' he'
  exact mul_nonneg (mul_nonneg (abs_nonneg _) (abs_nonneg _))
    (add_nonneg
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
      (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _))

theorem pinnedGeneralModulusCoefficientMass_nonneg
    {H : Finset ℕ} (D E : Finset (H → ℕ))
    (lambda : (H → ℕ) → (H → ℕ) → ℝ) (M : ℕ) :
    0 ≤ pinnedGeneralModulusCoefficientMass D E lambda M := by
  unfold pinnedGeneralModulusCoefficientMass pinnedGeneralIndexCoefficient
  positivity

/-- Bombieri--Vinogradov controls the grouped discrepancy once the absolute
coefficient mass in every lcm-modulus fiber has a uniform envelope. -/
theorem primeLevelWitness_pinnedGeneralGroupedDiscrepancySum_le
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    {theta exponent C L : ℝ} {X₀ x₁ x₂ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta exponent C X₀)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hx₁ : X₀ ≤ x₁) (hx₂ : X₀ ≤ x₂)
    (hmod₁ : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₁))
    (hmod₂ : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1 (BoundedGaps.Maynard.modulusCutoff theta x₂))
    (hL : 0 ≤ L)
    (hcoeff : ∀ M ∈ pinnedGeneralModulusSet D E,
      pinnedGeneralModulusCoefficientMass D E lambda M ≤ L) :
    pinnedGeneralGroupedDiscrepancySum H D E lambda x₁ x₂ ≤
      L * (C * (x₁ : ℝ) /
          Real.rpow (Real.log (x₁ : ℝ)) exponent +
        C * (x₂ : ℝ) /
          Real.rpow (Real.log (x₂ : ℝ)) exponent) := by
  let S := pinnedGeneralModulusSet D E
  let Δ₁ : ℕ → ℝ := fun M =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy x₁ M
  let Δ₂ : ℕ → ℝ := fun M =>
    BoundedGaps.Maynard.maxProgressionDiscrepancy x₂ M
  have hBV₁ : (∑ M ∈ S, Δ₁ M) ≤
      C * (x₁ : ℝ) / Real.rpow (Real.log (x₁ : ℝ)) exponent := by
    exact hw.sum_maxProgressionDiscrepancy_subset hx₁ S hmod₁
  have hBV₂ : (∑ M ∈ S, Δ₂ M) ≤
      C * (x₂ : ℝ) / Real.rpow (Real.log (x₂ : ℝ)) exponent := by
    exact hw.sum_maxProgressionDiscrepancy_subset hx₂ S hmod₂
  unfold pinnedGeneralGroupedDiscrepancySum
  calc
    (∑ M ∈ S,
        pinnedGeneralModulusCoefficientMass D E lambda M *
          (Δ₁ M + Δ₂ M)) ≤
        ∑ M ∈ S, L * (Δ₁ M + Δ₂ M) := by
      apply Finset.sum_le_sum
      intro M hM
      exact mul_le_mul_of_nonneg_right (hcoeff M hM)
        (add_nonneg
          (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _)
          (BoundedGaps.Maynard.maxProgressionDiscrepancy_nonneg _ _))
    _ = L * ((∑ M ∈ S, Δ₁ M) + ∑ M ∈ S, Δ₂ M) := by
      rw [← Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hBV₁ hBV₂) hL

/-- Complete finite aggregation of the general pinned prime-count errors.
No cross-family coprimality is imposed: incompatible systems and systems
whose pinned coordinates are nontrivial have already been totalized to
zero by `GeneralPinned.lean`. -/
theorem abs_pinnedGeneralErrorSum_primeInterval_le_weightedDiscrepancy
    {H : Finset ℕ} {D E : Finset (H → ℕ)} {RD RE W m p Y A B : ℕ}
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ h : H, ∀ q ∈ Finset.Ico A B,
      h.1 * (W * q) < p)
    (hA : 0 < A) (hAB : A ≤ B) :
    |pinnedGeneralErrorSum H D E lambda W m p
        (auxiliaryPrimeInterval A B)| ≤
      pinnedGeneralWeightedDiscrepancySum H D E lambda (B - 1) (A - 1) := by
  unfold pinnedGeneralErrorSum pinnedGeneralWeightedDiscrepancySum
  apply abs_fivefold_sum_le_sum_bound
  intro h d hd e he d' hd' e' he'
  have hpoint := abs_pinnedGeneralCountError_primeInterval_le_max_total
    h (hD d hd) (hD d' hd') (hE e he) (hE e' he') hm hcover hp
    hRDp hREY hpre (hmargin h) hA hAB
  rw [abs_mul, abs_mul]
  exact mul_le_mul_of_nonneg_left hpoint
    (mul_nonneg (abs_nonneg _) (abs_nonneg _))

/-- End-to-end Bombieri--Vinogradov bound for the arbitrary-overlap pinned
error.  The only arithmetic hypotheses left exposed are the modulus cutoff
and a uniform absolute coefficient-mass bound on each modulus fiber. -/
theorem primeLevelWitness_abs_pinnedGeneralErrorSum_primeInterval_le
    {H : Finset ℕ} {D E : Finset (H → ℕ)}
    {RD RE W m p Y A B : ℕ} {theta exponent C L : ℝ} {X₀ : ℕ}
    (hw : BoundedGaps.Maynard.PrimeLevelWitness theta exponent C X₀)
    (lambda : (H → ℕ) → (H → ℕ) → ℝ)
    (hD : ∀ d ∈ D,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RD W d)
    (hE : ∀ e ∈ E,
      BoundedGaps.Maynard.IsMaynardDivisorTuple H RE (W * m) e)
    (hm : 0 < m)
    (hcover : BoundedGaps.Maynard.CoversShiftDifferencePrimes H W)
    (hp : p.Prime) (hRDp : RD ≤ p) (hREY : RE ≤ Y)
    (hpre : largeGapPreSieved Y m p)
    (hmargin : ∀ h : H, ∀ q ∈ Finset.Ico A B,
      h.1 * (W * q) < p)
    (hA : 0 < A) (hAB : A ≤ B)
    (hxB : X₀ ≤ B - 1) (hxA : X₀ ≤ A - 1)
    (hmodB : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1
        (BoundedGaps.Maynard.modulusCutoff theta (B - 1)))
    (hmodA : pinnedGeneralModulusSet D E ⊆
      Finset.Icc 1
        (BoundedGaps.Maynard.modulusCutoff theta (A - 1)))
    (hL : 0 ≤ L)
    (hcoeff : ∀ M ∈ pinnedGeneralModulusSet D E,
      pinnedGeneralModulusCoefficientMass D E lambda M ≤ L) :
    |pinnedGeneralErrorSum H D E lambda W m p
        (auxiliaryPrimeInterval A B)| ≤
      (H.card : ℝ) *
        (L * (C * ((B - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log (((B - 1 : ℕ) : ℝ)) ) exponent +
          C * ((A - 1 : ℕ) : ℝ) /
            Real.rpow (Real.log (((A - 1 : ℕ) : ℝ)) ) exponent)) := by
  have hpoint :=
    abs_pinnedGeneralErrorSum_primeInterval_le_weightedDiscrepancy
      lambda hD hE hm hcover hp hRDp hREY hpre hmargin hA hAB
  have hgroup := pinnedGeneralWeightedDiscrepancySum_eq_card_mul_grouped
    H D E lambda (B - 1) (A - 1)
  have hBV := primeLevelWitness_pinnedGeneralGroupedDiscrepancySum_le
    hw lambda hxB hxA hmodB hmodA hL hcoeff
  calc
    _ ≤ pinnedGeneralWeightedDiscrepancySum H D E lambda
          (B - 1) (A - 1) := hpoint
    _ = (H.card : ℝ) *
          pinnedGeneralGroupedDiscrepancySum H D E lambda
            (B - 1) (A - 1) := hgroup
    _ ≤ _ := mul_le_mul_of_nonneg_left hBV (by positivity)

end

end Erdos4b
