/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceControlBoxContainment
import ErdosProblems.Erdos186.PZ.Intersection.SourceFunctionalSlabThicknessChoice
import ErdosProblems.Erdos186.PZ.SourceParameterAsymptotics

/-!
# The source-parameter box-scale inequality

The chosen source core occupies at least half of the population and embeds
in the fixed control box.  Since `gamma * mu * N` is unbounded and eventually
`mu ≤ 1`, the thinner quantity `gamma * N` still dominates the fixed
denominator in the common slab thickness.
-/

namespace Erdos186.PZ.Intersection

open Filter
open scoped Topology

noncomputable section

set_option autoImplicit false

/-- Every fixed constant is eventually bounded by `gamma * N`.  This is kept
as a local source-parameter corollary of the stronger `gamma * mu * N`
growth statement used by the anisotropic radius estimates. -/
theorem eventually_const_le_gamma_mul_natCast
    {kappa K : ℝ} (hkappa : 0 < kappa) (hK : 0 < K) (C : ℝ) :
    ∀ᶠ N : ℕ in atTop, C ≤ gamma kappa K N * (N : ℝ) := by
  have hgrowth := eventually_const_le_gamma_mul_mu_mul_natCast kappa K C
  filter_upwards [hgrowth, eventually_mu_mem_Ioo hkappa,
      eventually_gamma_pos kappa hK]
    with N hgrowthN hmuN hgammaN
  calc
    C ≤ gamma kappa K N * mu kappa N * (N : ℝ) := hgrowthN
    _ ≤ gamma kappa K N * 1 * (N : ℝ) := by
      gcongr
      exact hmuN.2.le
    _ = gamma kappa K N * (N : ℝ) := by ring

/-- Eventually the common source thickness is large enough relative to the
cardinality of every positive-dimensional control box whose selected core
retains half of the source population. -/
theorem eventually_sourceFunctionalSlab_boxScale
    {beta eta : ℝ}
    (context : Reduction.HigherDimensionalContext beta eta)
    (rankCeiling : ℕ) (kappa K : ℝ)
    (hkappa : 0 < kappa) (hK : 0 < K)
    (forwardConstant reverseConstant : ℝ)
    (hforward : 0 ≤ forwardConstant) (hreverse : 0 ≤ reverseConstant) :
    ∀ᶠ N : ℕ in atTop,
      ∀ {ambient : ℕ} (selector : Reduction.BoundedCFPSelector context)
        (A : Finset (LatticePoint ambient)) (hA : selector.Eligible A),
        A.card = N →
        0 < (selector.chosen A hA).dimension →
        (1 / 2 : ℝ) * (N : ℝ) ≤
          ((selector.chosen A hA).identifiedCore.card : ℝ) →
        1 ≤
          (2 * ((selector.chosen A hA).dimension : ℝ) *
              sourceFunctionalSlabThickness context rankCeiling
                forwardConstant reverseConstant (gamma kappa K N)) *
            ((controlIntegerBox (selector.chosen A hA).progression
              (2 * context.scaleDen
                (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
  let B := sourceFunctionalSlabTermBound context rankCeiling
    forwardConstant reverseConstant
  have hB : 0 ≤ B := sourceFunctionalSlabTermBound_nonneg
    (context := context) hforward hreverse
  have hgrowth := eventually_const_le_gamma_mul_natCast
    hkappa hK (2 * (B + 1))
  filter_upwards [hgrowth, eventually_gamma_pos kappa hK]
    with N hgrowthN hgammaN
  intro ambient selector A hA hcard hd hhalf
  let S := selector.chosen A hA
  let m : ℕ := 2 * context.scaleDen S.dimension
  let boxCard : ℝ := ((controlIntegerBox S.progression m).carrier.card : ℝ)
  let t := sourceFunctionalSlabThickness context rankCeiling
    forwardConstant reverseConstant (gamma kappa K N)
  have hm : 1 ≤ m := by
    dsimp only [m]
    have hden := context.scaleDen_pos S.dimension
    omega
  have hcoreSubset : S.identifiedCore ⊆
      (controlIntegerBox S.progression m).carrier :=
    S.identifiedCore_subset_coefficientBox.trans
      (gapCoefficientBox_subset_controlIntegerBox S.progression hm)
  have hcoreCard : (S.identifiedCore.card : ℝ) ≤ boxCard := by
    dsimp only [boxCard]
    exact_mod_cast Finset.card_le_card hcoreSubset
  have hNbox : (N : ℝ) ≤ 2 * boxCard := by
    linarith
  have hdreal : (1 : ℝ) ≤ S.dimension := by exact_mod_cast hd
  have hNfactor : (N : ℝ) ≤ 2 * (S.dimension : ℝ) * boxCard := by
    calc
      (N : ℝ) ≤ 2 * boxCard := hNbox
      _ ≤ 2 * (S.dimension : ℝ) * boxCard := by
        have hboxNonneg : 0 ≤ boxCard := by positivity
        nlinarith
  have ht : 0 < t := by
    dsimp only [t]
    exact sourceFunctionalSlabThickness_pos hforward hreverse hgammaN
  have hdenom : 0 < 2 * (B + 1) := by positivity
  have hone : 1 ≤ t * (N : ℝ) := by
    calc
      1 ≤ gamma kappa K N * (N : ℝ) / (2 * (B + 1)) :=
        (le_div_iff₀ hdenom).2 (by simpa only [one_mul] using hgrowthN)
      _ = t * (N : ℝ) := by
        dsimp only [t, sourceFunctionalSlabThickness]
        ring
  have hmul := mul_le_mul_of_nonneg_left hNfactor ht.le
  dsimp only [S, m, boxCard, t] at hone hmul ⊢
  calc
    1 ≤ sourceFunctionalSlabThickness context rankCeiling
        forwardConstant reverseConstant (gamma kappa K N) * (N : ℝ) := hone
    _ ≤ (2 * ((selector.chosen A hA).dimension : ℝ) *
          sourceFunctionalSlabThickness context rankCeiling
            forwardConstant reverseConstant (gamma kappa K N)) *
        ((controlIntegerBox (selector.chosen A hA).progression
          (2 * context.scaleDen
            (selector.chosen A hA).dimension)).carrier.card : ℝ) := by
      nlinarith

end

end Erdos186.PZ.Intersection
