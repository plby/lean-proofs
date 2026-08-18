/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceUniformBoxWeightedPostCFP
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenBoxWeightedScalarClosure
import ErdosProblems.Erdos186.PZ.Intersection.FrozenBoundedSupportSourceHierarchy

/-!
# Power-range frozen-source post-CFP assembly

All source parameters are evaluated at the initial population.  The terminal
input may be any canonical CFP input whose population is at least an arbitrary
fixed positive power of the initial population.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

namespace Theorem4PostCFPData

/-- Uniform frozen-source zero-cutoff post-CFP construction throughout every
fixed positive power range.  This is the form consumed by trace persistence,
whose exponent is fixed before the initial population is chosen. -/
theorem exists_powerRangeSource_boxWeightedFullCoefficientPostCFP_threshold
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hK : 0 < K) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        (initialCard : ℝ) ^ p ≤ (A.card : ℝ) →
        A.card ≤ initialCard →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        delta kappa initialCard * (A.card : ℝ) ≤
          (((((context.scaleSelector exponent).chosen A hA).identifiedCore.card -
            2) / 2 : ℕ) : ℝ) →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard)),
          Reduction.IsBoundedCoordinateIrreducible
            (context.scaleSelector exponent) A hA
              (delta kappa initialCard) (gamma kappa K initialCard) →
          (context.scaleSelector exponent).CandidateClosedAt A hA
            (delta kappa initialCard) →
          ∃ Dout : Theorem4PostCFPData
              ((context.scaleSelector exponent).chosen A hA).identifiedCore,
            Dout.a = D.a := by
  let constant := sourceBoxWeightedJohnUniformConstant rankCeiling
  have hconstant : 1 ≤ constant := by
    dsimp only [constant]
    exact sourceBoxWeightedJohnUniformConstant_one_le rankCeiling
  obtain ⟨scalarThreshold, hscalar⟩ :=
    exists_powerRange_boxWeightedZeroCutoffScalarHierarchyThreshold
      context rankCeiling heta p hp kappa K hkappa hkappaOne hK constant
        hconstant
  obtain ⟨boundedThreshold, hbounded⟩ :=
    exists_powerRange_highCoefficientBoundedSupportHierarchyThreshold
      context rankCeiling heta p hp kappa K hK
  have hanalytic : ∀ᶠ N : ℕ in atTop,
      0 < delta kappa N ∧ 0 < gamma kappa K N ∧ 0 < mu kappa N ∧
        delta kappa N < mu kappa N / 8 ∧
        32 ≤ mu kappa N * (N : ℝ) ^ p := by
    have hdelta := eventually_delta_pos kappa
    have hgamma := eventually_gamma_pos kappa hK
    have hmu := eventually_mu_mem_Ioo hkappa
    have hdeltaMu := eventually_delta_lt_mu_div
      hkappa hkappaOne (by norm_num : (0 : ℝ) < 8)
    have hpopulation :=
      eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
        kappa K 0 hp 32
    filter_upwards [hdelta, hgamma, hmu, hdeltaMu, hpopulation]
      with N hdeltaN hgammaN hmuN hdeltaMuN hpopulationN
    refine ⟨hdeltaN, hgammaN, hmuN.1, hdeltaMuN, ?_⟩
    simpa only [pow_zero, one_mul] using hpopulationN
  obtain ⟨analyticThreshold, hanalyticThreshold⟩ :=
    Filter.eventually_atTop.mp hanalytic
  let threshold := max scalarThreshold (max boundedThreshold analyticThreshold)
  refine ⟨threshold, ?_⟩
  intro initialCard ambient hlarge A hA hlower hupper hrank hcoreRetention
    hhalf a₀ c D hirr hclosed
  have hlargeScalar : scalarThreshold ≤ initialCard :=
    (le_max_left scalarThreshold (max boundedThreshold analyticThreshold)).trans
      hlarge
  have hlargeBounded : boundedThreshold ≤ initialCard :=
    (le_max_left boundedThreshold analyticThreshold).trans
      ((le_max_right scalarThreshold
        (max boundedThreshold analyticThreshold)).trans hlarge)
  have hlargeAnalytic : analyticThreshold ≤ initialCard :=
    (le_max_right boundedThreshold analyticThreshold).trans
      ((le_max_right scalarThreshold
        (max boundedThreshold analyticThreshold)).trans hlarge)
  obtain ⟨hdelta, hgamma, hmu, hdeltaMu, hmuPower⟩ :=
    hanalyticThreshold initialCard hlargeAnalytic
  have hpopulation : 32 / mu kappa initialCard ≤ (A.card : ℝ) := by
    apply (div_le_iff₀ hmu).2
    have hmul := mul_le_mul_of_nonneg_left hlower hmu.le
    exact hmuPower.trans (by simpa only [mul_comm] using hmul)
  have hd : 0 <
      ((context.scaleSelector exponent).chosen A hA).dimension :=
    selectedDimension_pos_of_coreRetention (context.scaleSelector exponent)
      hdelta hcoreRetention
  let hcap : 0 < (mu kappa initialCard *
      ((context.scaleSelector exponent).chosen A hA).identifiedCore.card)⁻¹ :=
    inv_mu_mul_coreCard_pos_of_coreRetention
      ((context.scaleSelector exponent).eligible_nonempty hA).card_pos
        hdelta hmu hcoreRetention
  let hmass := highCoefficient_zeroCutoff_massBudget_of_halfCore
    ((context.scaleSelector exponent).eligible_nonempty hA).card_pos hmu
      hdeltaMu hhalf hpopulation
  let E := chooseHighCoefficientSideSelectionData
    (context.scaleSelector exponent) D hirr hclosed hdelta
      (show (0 : ℝ) ≤ 0 by rfl) hcap hmass
  have hcoreCard :
      ((context.scaleSelector exponent).chosen A hA).identifiedCore.card ≤
        A.card := by
    rw [Reduction.SelectedCFP.card_identifiedCore]
    exact Finset.card_le_card
      ((context.scaleSelector exponent).chosen A hA).witness.core_subset
  have hdense₁ : delta kappa initialCard * (A.card : ℝ) ≤
      ((D.largeA₁ 0).card : ℝ) := by
    exact D.card_largeA₁_of_budget A.card 0 (delta kappa initialCard)
      hcoreCard (show (0 : ℝ) ≤ 0 by rfl) hcap hdelta.le hmass
  have hdense₂ : delta kappa initialCard * (A.card : ℝ) ≤
      ((D.largeA₂ 0).card : ℝ) := by
    exact D.card_largeA₂_of_budget A.card 0 (delta kappa initialCard)
      hcoreCard (show (0 : ℝ) ≤ 0 by rfl) hcap hdelta.le hmass
  have Hbounded : HighCoefficientBoundedSupportScalarHierarchies E := by
    exact hbounded hlargeBounded A hA hlower hrank D E hdense₁ hdense₂
  let slab := sourceFunctionalSlabBudget (delta kappa initialCard) A.card
  let t := sourceFunctionalSlabThickness context rankCeiling constant constant
    (gamma kappa K initialCard)
  let radius := gamma kappa K initialCard * mu kappa initialCard *
    (A.card : ℝ) /
      sourceFrozenBoxWeightedRadiusDenominator context rankCeiling constant
  have Hscalar : BoxWeightedZeroCutoffScalarHierarchies
      (delta := delta kappa initialCard) E constant slab t radius := by
    exact hscalar hlargeScalar A hA hlower hupper hrank hd hhalf D E
      hdense₁ hdense₂
  exact of_sourceUniformBoxWeightedFullCoefficientSource_halfCore
    (context.scaleSelector exponent) rankCeiling hrank D hirr hclosed
      hcoreRetention hhalf hpopulation hdeltaMu hdelta hmu hgamma
      slab t radius Hbounded (by simpa only [constant] using Hscalar)

end Theorem4PostCFPData

end

end Erdos186.PZ.Intersection
