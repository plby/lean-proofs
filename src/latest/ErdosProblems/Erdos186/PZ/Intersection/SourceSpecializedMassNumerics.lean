/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SourceSpecializedPostCFP
import ErdosProblems.Erdos186.PZ.Reduction.CoreFraction

/-!
# Near-full core numerics for the source-specialized intersection theorem

Once `delta < mu / 4`, a sufficiently small fixed CFP loss fraction leaves
the two strict mass margins used by the source proof.  The canonical selector
has such a loss fraction beyond a uniform threshold by `CoreFraction.lean`.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- A half-population core is already sufficient for the exact
high-coefficient selection budget if the source parameters are chosen with
the slightly stronger separation `delta < mu / 8`.  This route avoids any
dependence on the ambient dimension of the internal replacement terminal. -/
theorem highCoefficient_massBudget_of_halfCore
    {population core : ℕ} {delta mu : ℝ}
    (hpopulation : 0 < population) (hmu : 0 < mu)
    (hdeltaMu : delta < mu / 8)
    (hhalf : (1 / 2 : ℝ) * (population : ℝ) ≤ (core : ℝ))
    (hlarge : 32 / mu ≤ (population : ℝ)) :
    (population : ℝ) * sourceCoefficientThreshold population +
          delta * (population : ℝ) * (mu * core)⁻¹ <
        (1 - 2 * (mu * core)⁻¹) / 2 := by
  have hpopulationReal : (0 : ℝ) < (population : ℝ) := by
    exact_mod_cast hpopulation
  have hcoreMassLower : mu * (population : ℝ) / 2 ≤ mu * core := by
    have hmul := mul_le_mul_of_nonneg_left hhalf hmu.le
    nlinarith
  have hmuPopulation : 32 ≤ mu * (population : ℝ) := by
    simpa [mul_comm] using (div_le_iff₀ hmu).mp hlarge
  have hsixteen : 16 ≤ mu * core := by nlinarith
  have hcoreMassPos : 0 < mu * core := (by norm_num : (0 : ℝ) < 16).trans_le hsixteen
  have hcap : (mu * core)⁻¹ ≤ (1 : ℝ) / 16 := by
    rw [inv_le_iff_one_le_mul₀ hcoreMassPos]
    nlinarith
  have hdensity : 4 * delta * (population : ℝ) < mu * core := by
    have hdeltaScaled : 4 * delta < mu / 2 := by nlinarith
    have hcoreMassLower' :
        (mu / 2) * (population : ℝ) ≤ mu * core := by
      nlinarith [hcoreMassLower]
    exact (mul_lt_mul_of_pos_right hdeltaScaled hpopulationReal).trans_le
      hcoreMassLower'
  have hscaled :
      delta * (population : ℝ) * (mu * core)⁻¹ < (1 : ℝ) / 4 := by
    rw [mul_inv_lt_iff₀ hcoreMassPos]
    nlinarith
  rw [card_mul_sourceCoefficientThreshold hpopulation]
  linarith

/-- A near-full selected core implies the exact two source mass inequalities.
The hypotheses are deliberately scalar, so the result can be combined with
any uniform loss estimate. -/
theorem sourceSpecializedMassHierarchy_of_loss_fraction
    {beta eta xi : ℝ}
    {context : Reduction.HigherDimensionalContext beta eta}
    {selector : Reduction.BoundedCFPSelector context}
    {d : ℕ} {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta mu : ℝ}
    (hmu : 0 < mu) (hcard : 0 < A.card)
    (hgap : 4 * delta + mu * xi < mu)
    (hloss : ((selector.chosen A hA).loss : ℝ) ≤
      xi * (A.card : ℝ))
    (hcap : 16 ≤ mu * (1 - xi) * (A.card : ℝ))
    (hdeltaMu : delta < mu / 4) :
    SourceSpecializedMassHierarchy selector A hA delta mu := by
  have hcardReal : (0 : ℝ) < (A.card : ℝ) := by exact_mod_cast hcard
  have hmulLoss :
      mu * ((selector.chosen A hA).loss : ℝ) ≤
        mu * xi * (A.card : ℝ) := by
    calc
      mu * ((selector.chosen A hA).loss : ℝ) ≤
          mu * (xi * (A.card : ℝ)) :=
        mul_le_mul_of_nonneg_left hloss hmu.le
      _ = mu * xi * (A.card : ℝ) := by ring
  refine {
    delta_lt_mu_div_four := hdeltaMu
    cap_after_selectedLoss := ?_
    density_after_selectedLoss := ?_ }
  · calc
      16 + mu * ((selector.chosen A hA).loss : ℝ) ≤
          mu * (1 - xi) * (A.card : ℝ) +
            mu * xi * (A.card : ℝ) := add_le_add hcap hmulLoss
      _ = mu * (A.card : ℝ) := by ring
  · calc
      4 * delta * (A.card : ℝ) +
          mu * ((selector.chosen A hA).loss : ℝ) ≤
        (4 * delta + mu * xi) * (A.card : ℝ) := by
          calc
            4 * delta * (A.card : ℝ) +
                mu * ((selector.chosen A hA).loss : ℝ) ≤
              4 * delta * (A.card : ℝ) +
                mu * xi * (A.card : ℝ) := by linarith
            _ = (4 * delta + mu * xi) * (A.card : ℝ) := by ring
      _ < mu * (A.card : ℝ) :=
        mul_lt_mul_of_pos_right hgap hcardReal

/-- The strict source relation `delta < mu / 4` determines a positive loss
fraction and a finite population threshold after which every selected loss
below that fraction satisfies `SourceSpecializedMassHierarchy`. -/
theorem exists_lossFraction_threshold_sourceSpecializedMassHierarchy
    {delta mu : ℝ} (hdelta : 0 < delta) (hmu : 0 < mu)
    (hdeltaMu : delta < mu / 4) :
    ∃ xi : ℝ, 0 < xi ∧ xi ≤ 1 ∧ ∃ threshold : ℕ, 1 ≤ threshold ∧
      ∀ {beta eta : ℝ}
        {context : Reduction.HigherDimensionalContext beta eta}
        {selector : Reduction.BoundedCFPSelector context}
        {d : ℕ} (A : Finset (LatticePoint d))
        (hA : selector.Eligible A),
        threshold ≤ A.card →
        (((selector.chosen A hA).loss : ℝ) ≤ xi * (A.card : ℝ)) →
        SourceSpecializedMassHierarchy selector A hA delta mu := by
  let xi : ℝ := (mu - 4 * delta) / (2 * mu)
  have hnumerator : 0 < mu - 4 * delta := by nlinarith
  have hxi : 0 < xi := div_pos hnumerator (mul_pos (by norm_num) hmu)
  have hxiLtOne : xi < 1 := by
    dsimp only [xi]
    apply (div_lt_one (mul_pos (by norm_num) hmu)).2
    nlinarith
  have hxiOne : xi ≤ 1 := hxiLtOne.le
  have hgap : 4 * delta + mu * xi < mu := by
    dsimp only [xi]
    field_simp [hmu.ne']
    nlinarith
  have honeSubXi : 0 < 1 - xi := sub_pos.mpr hxiLtOne
  have hcoefficient : 0 < mu * (1 - xi) := mul_pos hmu honeSubXi
  obtain ⟨threshold, hthreshold⟩ :=
    exists_nat_gt (16 / (mu * (1 - xi)))
  have hthresholdPos : 1 ≤ threshold := by
    have hquotNonneg : 0 ≤ 16 / (mu * (1 - xi)) :=
      div_nonneg (by norm_num) hcoefficient.le
    have hthresholdReal : (0 : ℝ) < (threshold : ℝ) :=
      hquotNonneg.trans_lt hthreshold
    exact_mod_cast hthresholdReal
  refine ⟨xi, hxi, hxiOne, threshold, hthresholdPos, ?_⟩
  intro beta eta context selector d A hA hlarge hloss
  have hcard : 0 < A.card := hthresholdPos.trans hlarge
  have hlargeReal : (threshold : ℝ) ≤ (A.card : ℝ) := by
    exact_mod_cast hlarge
  have hcap : 16 ≤ mu * (1 - xi) * (A.card : ℝ) := by
    have hthreshold' : 16 <
        (threshold : ℝ) * (mu * (1 - xi)) := by
      exact (div_lt_iff₀ hcoefficient).mp hthreshold
    calc
      (16 : ℝ) ≤ (threshold : ℝ) * (mu * (1 - xi)) :=
        hthreshold'.le
      _ ≤ (A.card : ℝ) * (mu * (1 - xi)) :=
        mul_le_mul_of_nonneg_right hlargeReal hcoefficient.le
      _ = mu * (1 - xi) * (A.card : ℝ) := by ring
  exact sourceSpecializedMassHierarchy_of_loss_fraction hmu hcard hgap
    hloss hcap hdeltaMu

end

end Erdos186.PZ.Intersection
