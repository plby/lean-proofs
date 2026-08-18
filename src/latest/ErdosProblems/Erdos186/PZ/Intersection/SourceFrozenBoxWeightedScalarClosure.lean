/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.BoxWeightedZeroCutoffAssembly
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabFrozenClosure
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenSideCost
import ErdosProblems.Erdos186.PZ.Intersection.SourceCoveringRadiusNumerics
import ErdosProblems.Erdos186.PZ.Intersection.SourceFrozenCoveringAsymptotics
import ErdosProblems.Erdos186.PZ.Intersection.WeightedSourceMassNumerics

/-!
# Frozen source closure of the anisotropic zero-cutoff scalar hierarchy
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- A fixed denominator leaving room for both the weighted-mass and target
radius estimates. -/
def sourceFrozenBoxWeightedRadiusDenominator
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (constant : ℝ) : ℝ :=
  128 * (sourceFunctionalSlabTermBound context rankCeiling
    constant constant + 1)

theorem sourceFrozenBoxWeightedRadiusDenominator_pos
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling : ℕ} {constant : ℝ} (hconstant : 0 ≤ constant) :
    0 < sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
      constant := by
  unfold sourceFrozenBoxWeightedRadiusDenominator
  have hbound := sourceFunctionalSlabTermBound_nonneg
    (context := context) (rankCeiling := rankCeiling)
    hconstant hconstant
  positivity

theorem sourceFrozenBoxWeightedRadiusDenominator_ge
    {beta eta : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {rankCeiling : ℕ} {constant : ℝ} (hconstant : 0 ≤ constant) :
    128 ≤ sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
      constant := by
  unfold sourceFrozenBoxWeightedRadiusDenominator
  have hbound := sourceFunctionalSlabTermBound_nonneg
    (context := context) (rankCeiling := rankCeiling)
    hconstant hconstant
  nlinarith

/-- With the source parameters frozen at `initialCard`, the canonical slab,
thickness and radius satisfy the complete anisotropic zero-cutoff scalar
record uniformly for every terminal population above an arbitrary fixed
positive power of the initial population. -/
theorem eventually_powerRange_boxWeightedZeroCutoffScalarHierarchies
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hK : 0 < K) (constant : ℝ) (hconstant : 1 ≤ constant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ} (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
        A.card ≤ initialCard →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        0 < ((context.scaleSelector exponent).chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₁ 0).card : ℝ) →
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₂ 0).card : ℝ) →
          let slab := sourceFunctionalSlabBudget
            (delta kappa initialCard) A.card
          let t := sourceFunctionalSlabThickness context rankCeiling
            constant constant (gamma kappa K initialCard)
          let radius := gamma kappa K initialCard * mu kappa initialCard *
            (A.card : ℝ) /
              sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
                constant
          BoxWeightedZeroCutoffScalarHierarchies
            (delta := delta kappa initialCard) E constant slab t radius := by
  have hconstantNonneg : 0 ≤ constant := zero_le_one.trans hconstant
  let Q := sourceFrozenBoxWeightedRadiusDenominator context rankCeiling constant
  let C := (sourceCommonCoveringRadiusBound context rankCeiling : ℝ)
  have hQ : 0 < Q := by
    dsimp only [Q]
    exact sourceFrozenBoxWeightedRadiusDenominator_pos hconstantNonneg
  have hQ128 : 128 ≤ Q := by
    dsimp only [Q]
    exact sourceFrozenBoxWeightedRadiusDenominator_ge hconstantNonneg
  have hslab := eventually_sourceFunctionalSlabPowerRangeScalarHierarchies
    context rankCeiling heta p hp kappa K hK constant constant
      hconstantNonneg hconstantNonneg
  have hcost := eventually_powerRange_scaleSelector_sideCost
    (exponent := exponent) context rankCeiling p hp kappa K hkappa hK Q hQ
  have hcover :=
    eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
      kappa K (2 * rankCeiling + 1) hp (Q * C)
  have hradiusLarge :=
    eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
      kappa K 1 hp Q
  have hmassLarge :=
    eventually_const_le_gamma_natPow_mul_mu_mul_nat_rpow
      kappa K 0 hp 256
  have hdeltaMu := eventually_delta_lt_mu_div
    hkappa hkappaOne (by norm_num : (0 : ℝ) < 64)
  filter_upwards [hslab, hcost, hcover, hradiusLarge, hmassLarge,
      hdeltaMu, eventually_delta_pos kappa,
      eventually_gamma_mem_Ioo hkappa hK, eventually_mu_mem_Ioo hkappa]
    with initialCard hslabN hcostN hcoverN hradiusLargeN hmassLargeN
      hdeltaMuN hdeltaPos hgammaRange hmuRange
  intro ambient A hA hlower hcurrentUpper hrank hd hhalf a₀ c D E
    hdense₁ hdense₂
  let slab := sourceFunctionalSlabBudget (delta kappa initialCard) A.card
  let t := sourceFunctionalSlabThickness context rankCeiling constant constant
    (gamma kappa K initialCard)
  let radius := gamma kappa K initialCard * mu kappa initialCard *
    (A.card : ℝ) / Q
  let cost₁ : ℝ := ((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ)
  let cost₂ : ℝ := ((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ)
  have hcoreCard :
      ((context.scaleSelector exponent).chosen A hA).identifiedCore.card ≤
        A.card := by
    rw [Reduction.SelectedCFP.card_identifiedCore]
    exact Finset.card_le_card
      ((context.scaleSelector exponent).chosen A hA).witness.core_subset
  have hlarge₁ : (D.largeA₁ 0).card ≤ A.card := by
    exact (Finset.card_le_card ((D.largeA₁_subset 0).trans
      (D.A₁_subset_erase.trans (Finset.erase_subset _ _)))).trans hcoreCard
  have hlarge₂ : (D.largeA₂ 0).card ≤ A.card := by
    exact (Finset.card_le_card ((D.largeA₂_subset 0).trans
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _)))).trans hcoreCard
  have hdense₁' : delta kappa initialCard * (A.card : ℝ) ≤
      ((Reduction.identifiedTranslate (D.largeA₁ 0) D.a).card : ℝ) := by
    simpa only [Reduction.card_identifiedTranslate] using hdense₁
  have hdense₂' : delta kappa initialCard * (A.card : ℝ) ≤
      ((Reduction.identifiedTranslate (D.largeA₂ 0) D.a).card : ℝ) := by
    simpa only [Reduction.card_identifiedTranslate] using hdense₂
  have hlarge₁' :
      (Reduction.identifiedTranslate (D.largeA₁ 0) D.a).card ≤ A.card := by
    simpa only [Reduction.card_identifiedTranslate] using hlarge₁
  have hlarge₂' :
      (Reduction.identifiedTranslate (D.largeA₂ 0) D.a).card ≤ A.card := by
    simpa only [Reduction.card_identifiedTranslate] using hlarge₂
  have hcost₁raw : Q * (cost₁ + 1) ≤
      gamma kappa K initialCard * mu kappa initialCard * (A.card : ℝ) := by
    simpa only [cost₁] using
      hcostN A.card hlower hcurrentUpper
        (Reduction.identifiedTranslate (D.largeA₁ 0) D.a) E.eligible₁
        hrank hdense₁' hlarge₁'
  have hcost₂raw : Q * (cost₂ + 1) ≤
      gamma kappa K initialCard * mu kappa initialCard * (A.card : ℝ) := by
    simpa only [cost₂] using
      hcostN A.card hlower hcurrentUpper
        (Reduction.identifiedTranslate (D.largeA₂ 0) D.a) E.eligible₂
        hrank hdense₂' hlarge₂'
  have hcost₁radius : cost₁ + 1 ≤ radius := by
    dsimp only [radius]
    exact (le_div_iff₀ hQ).2 (by simpa only [mul_comm] using hcost₁raw)
  have hcost₂radius : cost₂ + 1 ≤ radius := by
    dsimp only [radius]
    exact (le_div_iff₀ hQ).2 (by simpa only [mul_comm] using hcost₂raw)
  have hgamma : 0 < gamma kappa K initialCard := hgammaRange.1
  have hgammaOne : gamma kappa K initialCard ≤ 1 := hgammaRange.2.le
  have hmu : 0 < mu kappa initialCard := hmuRange.1
  have hcoveringBase := E.gamma_pow_mul_commonCoveringRadius_le
    hrank hgamma hgammaOne
  have hcoveringScaled : Q * (E.commonCoveringRadius : ℝ) ≤
      gamma kappa K initialCard * mu kappa initialCard * (A.card : ℝ) := by
    have hpowerScaled :
        gamma kappa K initialCard ^ (2 * rankCeiling + 1) *
            mu kappa initialCard * Real.rpow (initialCard : ℝ) p ≤
          gamma kappa K initialCard ^ (2 * rankCeiling + 1) *
            mu kappa initialCard * (A.card : ℝ) := by
      gcongr
    have hscaled :
        gamma kappa K initialCard ^ (2 * rankCeiling) *
            (Q * (E.commonCoveringRadius : ℝ)) ≤
          gamma kappa K initialCard ^ (2 * rankCeiling) *
            (gamma kappa K initialCard * mu kappa initialCard *
              (A.card : ℝ)) := by
      calc
        gamma kappa K initialCard ^ (2 * rankCeiling) *
              (Q * (E.commonCoveringRadius : ℝ)) =
            Q * (gamma kappa K initialCard ^ (2 * rankCeiling) *
              (E.commonCoveringRadius : ℝ)) := by ring
        _ ≤ Q * C := mul_le_mul_of_nonneg_left hcoveringBase hQ.le
        _ ≤ gamma kappa K initialCard ^ (2 * rankCeiling + 1) *
              mu kappa initialCard * Real.rpow (initialCard : ℝ) p := hcoverN
        _ ≤ gamma kappa K initialCard ^ (2 * rankCeiling + 1) *
              mu kappa initialCard * (A.card : ℝ) := hpowerScaled
        _ = gamma kappa K initialCard ^ (2 * rankCeiling) *
              (gamma kappa K initialCard * mu kappa initialCard *
                (A.card : ℝ)) := by
          rw [show 2 * rankCeiling + 1 = 2 * rankCeiling + 1 by rfl,
            pow_succ]
          ring
    exact le_of_mul_le_mul_left hscaled
      (pow_pos hgamma (2 * rankCeiling))
  have hcoveringRadius : (E.commonCoveringRadius : ℝ) ≤ radius := by
    dsimp only [radius]
    exact (le_div_iff₀ hQ).2
      (by simpa only [mul_comm] using hcoveringScaled)
  have hradiusOne : 1 ≤ radius := by
    have hpowerScaled :
        gamma kappa K initialCard * mu kappa initialCard *
            Real.rpow (initialCard : ℝ) p ≤
          gamma kappa K initialCard * mu kappa initialCard *
            (A.card : ℝ) := by
      gcongr
    have hQtotal : Q ≤ gamma kappa K initialCard *
        mu kappa initialCard * (A.card : ℝ) := by
      calc
        Q ≤ gamma kappa K initialCard ^ 1 * mu kappa initialCard *
            Real.rpow (initialCard : ℝ) p := hradiusLargeN
        _ = gamma kappa K initialCard * mu kappa initialCard *
            Real.rpow (initialCard : ℝ) p := by rw [pow_one]
        _ ≤ _ := hpowerScaled
    dsimp only [radius]
    exact (le_div_iff₀ hQ).2 (by simpa only [one_mul] using hQtotal)
  have hmuPopulation : 256 ≤ mu kappa initialCard * (A.card : ℝ) := by
    have hpowerScaled : mu kappa initialCard *
        Real.rpow (initialCard : ℝ) p ≤
        mu kappa initialCard * (A.card : ℝ) :=
      mul_le_mul_of_nonneg_left hlower hmu.le
    calc
      256 ≤ gamma kappa K initialCard ^ 0 * mu kappa initialCard *
          Real.rpow (initialCard : ℝ) p := hmassLargeN
      _ = mu kappa initialCard * Real.rpow (initialCard : ℝ) p := by
        rw [pow_zero, one_mul]
      _ ≤ _ := hpowerScaled
  have hcost₁mass : 128 * (cost₁ + 1) ≤
      mu kappa initialCard * (A.card : ℝ) := by
    calc
      128 * (cost₁ + 1) ≤ Q * (cost₁ + 1) := by gcongr
      _ ≤ gamma kappa K initialCard * mu kappa initialCard *
          (A.card : ℝ) := hcost₁raw
      _ ≤ mu kappa initialCard * (A.card : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hgammaOne
          (mul_nonneg hmu.le (by positivity : (0 : ℝ) ≤ A.card))]
  have hcost₂mass : 128 * (cost₂ + 1) ≤
      mu kappa initialCard * (A.card : ℝ) := by
    calc
      128 * (cost₂ + 1) ≤ Q * (cost₂ + 1) := by gcongr
      _ ≤ gamma kappa K initialCard * mu kappa initialCard *
          (A.card : ℝ) := hcost₂raw
      _ ≤ mu kappa initialCard * (A.card : ℝ) := by
        nlinarith [mul_le_mul_of_nonneg_right hgammaOne
          (mul_nonneg hmu.le (by positivity : (0 : ℝ) ≤ A.card))]
  have hslabUpper : (slab : ℝ) ≤
      delta kappa initialCard * (A.card : ℝ) + 1 := by
    dsimp only [slab]
    exact sourceFunctionalSlabBudget_cast_le hdeltaPos.le A.card
  have hdeltaPopulation : delta kappa initialCard * (A.card : ℝ) ≤
      mu kappa initialCard * (A.card : ℝ) / 64 := by
    exact (mul_le_mul_of_nonneg_right hdeltaMuN.le (by positivity)).trans_eq
      (by ring)
  have hslabMass : (slab : ℝ) ≤
      mu kappa initialCard * (A.card : ℝ) / 64 + 1 :=
    hslabUpper.trans (by linarith only [hdeltaPopulation])
  have hmissing₁ :
      ((((E.side₁.loss + E.side₁.reserveBound + slab : ℕ) : ℝ)) + 1) ≤
        mu kappa initialCard * (A.card : ℝ) / 32 := by
    have hcostBound : cost₁ ≤
        mu kappa initialCard * (A.card : ℝ) / 128 - 1 := by
      linarith only [hcost₁mass]
    calc
      ((((E.side₁.loss + E.side₁.reserveBound + slab : ℕ) : ℝ)) + 1) =
          cost₁ + (slab : ℝ) + 1 := by
        dsimp only [cost₁]
        push_cast
        ring
      _ ≤ (mu kappa initialCard * (A.card : ℝ) / 128 - 1) +
          (mu kappa initialCard * (A.card : ℝ) / 64 + 1) + 1 := by
        gcongr
      _ ≤ mu kappa initialCard * (A.card : ℝ) / 32 := by
        linarith only [hmuPopulation]
  have hmissing₂ :
      ((((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ)) + 1) ≤
        mu kappa initialCard * (A.card : ℝ) / 32 := by
    have hcostBound : cost₂ ≤
        mu kappa initialCard * (A.card : ℝ) / 128 - 1 := by
      linarith only [hcost₂mass]
    calc
      ((((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ)) + 1) =
          cost₂ + (slab : ℝ) + 1 := by
        dsimp only [cost₂]
        push_cast
        ring
      _ ≤ (mu kappa initialCard * (A.card : ℝ) / 128 - 1) +
          (mu kappa initialCard * (A.card : ℝ) / 64 + 1) + 1 := by
        gcongr
      _ ≤ mu kappa initialCard * (A.card : ℝ) / 32 := by
        linarith only [hmuPopulation]
  have hcoreMass : mu kappa initialCard * (A.card : ℝ) / 8 ≤
      mu kappa initialCard *
        (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) /
          4 := by
    linarith only [mul_le_mul_of_nonneg_left hhalf hmu.le]
  have hmass₁ : mu kappa initialCard * (A.card : ℝ) / 64 ≤
      highCoefficientZonotopeScale D *
          ((1 - 2 * (mu kappa initialCard *
            ((context.scaleSelector exponent).chosen A hA).identifiedCore.card)⁻¹) /
              2 -
            (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) *
              0) -
        (((E.side₁.loss + E.side₁.reserveBound + slab : ℕ) : ℝ) *
          (highCoefficientZonotopeScale D *
            (mu kappa initialCard *
              ((context.scaleSelector exponent).chosen A hA).identifiedCore.card)⁻¹)) := by
    rw [mul_zero, sub_zero,
      D.weightedRetainedMass_highCoefficientZonotopeScale hmu]
    linarith only [hcoreMass, hmissing₁]
  have hmass₂ : mu kappa initialCard * (A.card : ℝ) / 64 ≤
      highCoefficientZonotopeScale D *
          ((1 - 2 * (mu kappa initialCard *
            ((context.scaleSelector exponent).chosen A hA).identifiedCore.card)⁻¹) /
              2 -
            (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) *
              0) -
        (((E.side₂.loss + E.side₂.reserveBound + slab : ℕ) : ℝ) *
          (highCoefficientZonotopeScale D *
            (mu kappa initialCard *
              ((context.scaleSelector exponent).chosen A hA).identifiedCore.card)⁻¹)) := by
    rw [mul_zero, sub_zero,
      D.weightedRetainedMass_highCoefficientZonotopeScale hmu]
    linarith only [hcoreMass, hmissing₂]
  have hradiusFormula : radius =
      t * (mu kappa initialCard * (A.card : ℝ) / 64) := by
    dsimp only [radius, t, Q, sourceFunctionalSlabThickness,
      sourceFrozenBoxWeightedRadiusDenominator]
    have hden : sourceFunctionalSlabTermBound context rankCeiling
        constant constant + 1 ≠ 0 := by
      have hbound := sourceFunctionalSlabTermBound_nonneg
        (context := context) (rankCeiling := rankCeiling)
        hconstantNonneg hconstantNonneg
      positivity
    field_simp [hden]
    ring
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hconstantNonneg
      hconstantNonneg hgamma
  have htarget₁ :
      ((3 * E.commonCoveringRadius + 2 : ℕ) : ℝ) / 2 +
          (((E.side₁.loss + E.side₁.reserveBound : ℕ) : ℝ) / 2 +
            E.side₁.reserveBound) ≤
        radius *
          (4 * context.scaleDen
            ((context.scaleSelector exponent).chosen A hA).dimension) := by
    have hreserve : (E.side₁.reserveBound : ℝ) ≤ cost₁ := by
      dsimp only [cost₁]
      exact_mod_cast Nat.le_add_left E.side₁.reserveBound E.side₁.loss
    have hscale : (4 : ℝ) ≤
        4 * context.scaleDen
          ((context.scaleSelector exponent).chosen A hA).dimension := by
      exact_mod_cast Nat.mul_le_mul_left 4
        (context.scaleDen_pos
          ((context.scaleSelector exponent).chosen A hA).dimension)
    have hcostCast : (E.side₁.loss : ℝ) + E.side₁.reserveBound = cost₁ := by
      dsimp only [cost₁]
      norm_cast
    push_cast
    rw [hcostCast]
    have hradiusNonneg : 0 ≤ radius := zero_le_one.trans hradiusOne
    have hscaled := mul_le_mul_of_nonneg_left hscale hradiusNonneg
    calc
      (3 * (E.commonCoveringRadius : ℝ) + 2) / 2 +
          (cost₁ / 2 + (E.side₁.reserveBound : ℝ)) ≤
          4 * radius := by
        linarith only [hcoveringRadius, hcost₁radius, hreserve, hradiusOne]
      _ = radius * 4 := by ring
      _ ≤ radius * (4 *
          (context.scaleDen
            ((context.scaleSelector exponent).chosen A hA).dimension : ℝ)) :=
        hscaled
  have htarget₂ :
      ((3 * E.commonCoveringRadius + 2 : ℕ) : ℝ) / 2 +
          (((E.side₂.loss + E.side₂.reserveBound : ℕ) : ℝ) / 2 +
            E.side₂.reserveBound) ≤
        radius *
          (4 * context.scaleDen
            ((context.scaleSelector exponent).chosen A hA).dimension) := by
    have hreserve : (E.side₂.reserveBound : ℝ) ≤ cost₂ := by
      dsimp only [cost₂]
      exact_mod_cast Nat.le_add_left E.side₂.reserveBound E.side₂.loss
    have hscale : (4 : ℝ) ≤
        4 * context.scaleDen
          ((context.scaleSelector exponent).chosen A hA).dimension := by
      exact_mod_cast Nat.mul_le_mul_left 4
        (context.scaleDen_pos
          ((context.scaleSelector exponent).chosen A hA).dimension)
    have hcostCast : (E.side₂.loss : ℝ) + E.side₂.reserveBound = cost₂ := by
      dsimp only [cost₂]
      norm_cast
    push_cast
    rw [hcostCast]
    have hradiusNonneg : 0 ≤ radius := zero_le_one.trans hradiusOne
    have hscaled := mul_le_mul_of_nonneg_left hscale hradiusNonneg
    calc
      (3 * (E.commonCoveringRadius : ℝ) + 2) / 2 +
          (cost₂ / 2 + (E.side₂.reserveBound : ℝ)) ≤
          4 * radius := by
        linarith only [hcoveringRadius, hcost₂radius, hreserve, hradiusOne]
      _ = radius * 4 := by ring
      _ ≤ radius * (4 *
          (context.scaleDen
            ((context.scaleSelector exponent).chosen A hA).dimension : ℝ)) :=
        hscaled
  dsimp only
  refine {
    slab_hierarchy := (hslabN (context.scaleSelector exponent) A hA hlower
      hrank hd hhalf).1
    forward_mass_radius := ?_
    reverse_mass_radius := ?_
    forward_target_radius := htarget₁
    reverse_target_radius := htarget₂ }
  · change radius ≤ t * _
    rw [hradiusFormula]
    exact mul_le_mul_of_nonneg_left hmass₁ ht.le
  · change radius ≤ t * _
    rw [hradiusFormula]
    exact mul_le_mul_of_nonneg_left hmass₂ ht.le

/-- Square-root-range compatibility form of the frozen box-weighted scalar
closure. -/
theorem eventually_frozen_boxWeightedZeroCutoffScalarHierarchies
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hK : 0 < K) (constant : ℝ) (hconstant : 1 ≤ constant) :
    ∀ᶠ initialCard : ℕ in atTop,
      ∀ {ambient : ℕ} (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        A.card ≤ initialCard →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        0 < ((context.scaleSelector exponent).chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₁ 0).card : ℝ) →
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₂ 0).card : ℝ) →
          let slab := sourceFunctionalSlabBudget
            (delta kappa initialCard) A.card
          let t := sourceFunctionalSlabThickness context rankCeiling
            constant constant (gamma kappa K initialCard)
          let radius := gamma kappa K initialCard * mu kappa initialCard *
            (A.card : ℝ) /
              sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
                constant
          BoxWeightedZeroCutoffScalarHierarchies
            (delta := delta kappa initialCard) E constant slab t radius := by
  have hpower := eventually_powerRange_boxWeightedZeroCutoffScalarHierarchies
    (exponent := exponent) context rankCeiling heta
      (1 / 2 : ℝ) (by norm_num) kappa K hkappa
      hkappaOne hK constant hconstant
  filter_upwards [hpower] with initialCard hpowerN
  intro ambient A hA hsqrt hupper hrank hd hhalf a₀ c D E hdense₁ hdense₂
  apply hpowerN A hA
  · calc
      Real.rpow (initialCard : ℝ) (1 / 2 : ℝ) =
          Real.sqrt (initialCard : ℝ) := by
        rw [Real.rpow_eq_pow]
        exact (Real.sqrt_eq_rpow _).symm
      _ ≤ (A.card : ℝ) := hsqrt
  · exact hupper
  · exact hrank
  · exact hd
  · exact hhalf
  · exact hdense₁
  · exact hdense₂

/-- Population-threshold form of the frozen arbitrary power-range
box-weighted scalar closure. -/
theorem exists_powerRange_boxWeightedZeroCutoffScalarHierarchyThreshold
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (p : ℝ) (hp : 0 < p)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hK : 0 < K) (constant : ℝ) (hconstant : 1 ≤ constant) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        Real.rpow (initialCard : ℝ) p ≤ (A.card : ℝ) →
        A.card ≤ initialCard →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        0 < ((context.scaleSelector exponent).chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₁ 0).card : ℝ) →
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₂ 0).card : ℝ) →
          let slab := sourceFunctionalSlabBudget
            (delta kappa initialCard) A.card
          let t := sourceFunctionalSlabThickness context rankCeiling
            constant constant (gamma kappa K initialCard)
          let radius := gamma kappa K initialCard * mu kappa initialCard *
            (A.card : ℝ) /
              sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
                constant
          BoxWeightedZeroCutoffScalarHierarchies
            (delta := delta kappa initialCard) E constant slab t radius := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_powerRange_boxWeightedZeroCutoffScalarHierarchies
      context rankCeiling heta p hp kappa K hkappa hkappaOne hK
        constant hconstant)
  refine ⟨threshold, ?_⟩
  intro initialCard ambient hlarge A hA hlower hupper hrank hd hhalf
    a₀ c D E hdense₁ hdense₂
  exact hthreshold initialCard hlarge A hA hlower hupper hrank hd hhalf
    D E hdense₁ hdense₂

/-- Population-threshold form of the frozen box-weighted scalar closure. -/
theorem exists_frozen_boxWeightedZeroCutoffScalarHierarchyThreshold
    {beta eta exponent : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (heta : 0 < eta)
    (kappa K : ℝ) (hkappa : 0 < kappa) (hkappaOne : kappa < 1)
    (hK : 0 < K) (constant : ℝ) (hconstant : 1 ≤ constant) :
    ∃ threshold : ℕ, ∀ {initialCard ambient : ℕ},
      threshold ≤ initialCard →
      ∀ (A : Finset (LatticePoint ambient))
        (hA : (context.scaleSelector exponent).Eligible A),
        Real.sqrt (initialCard : ℝ) ≤ (A.card : ℝ) →
        A.card ≤ initialCard →
        ((context.scaleSelector exponent).chosen A hA).dimension ≤
          rankCeiling →
        0 < ((context.scaleSelector exponent).chosen A hA).dimension →
        (1 / 2 : ℝ) * (A.card : ℝ) ≤
          (((context.scaleSelector exponent).chosen A hA).identifiedCore.card : ℝ) →
        ∀ {a₀ : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore}
          {c : realImage
            ((context.scaleSelector exponent).chosen A hA).identifiedCore → ℝ}
          (D : ConvexPoolsData
            ((context.scaleSelector exponent).chosen A hA).identifiedCore a₀ c
              (mu kappa initialCard))
          (E : HighCoefficientSideSelectionData
            (context.scaleSelector exponent) hA D 0
              (gamma kappa K initialCard)),
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₁ 0).card : ℝ) →
          delta kappa initialCard * (A.card : ℝ) ≤
              ((D.largeA₂ 0).card : ℝ) →
          let slab := sourceFunctionalSlabBudget
            (delta kappa initialCard) A.card
          let t := sourceFunctionalSlabThickness context rankCeiling
            constant constant (gamma kappa K initialCard)
          let radius := gamma kappa K initialCard * mu kappa initialCard *
            (A.card : ℝ) /
              sourceFrozenBoxWeightedRadiusDenominator context rankCeiling
                constant
          BoxWeightedZeroCutoffScalarHierarchies
            (delta := delta kappa initialCard) E constant slab t radius := by
  obtain ⟨threshold, hthreshold⟩ := Filter.eventually_atTop.mp
    (eventually_frozen_boxWeightedZeroCutoffScalarHierarchies
      context rankCeiling heta kappa K hkappa hkappaOne hK constant hconstant)
  refine ⟨threshold, ?_⟩
  intro initialCard ambient hlarge A hA hsqrt hupper hrank hd hhalf
    a₀ c D E hdense₁ hdense₂
  exact hthreshold initialCard hlarge A hA hsqrt hupper hrank hd hhalf
    D E hdense₁ hdense₂

end

end Erdos186.PZ.Intersection
