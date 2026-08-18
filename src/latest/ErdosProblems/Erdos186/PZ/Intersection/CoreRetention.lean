/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SideSelection

/-!
# CFP loss and density of the two balanced pools

The alternating partition leaves at least
`(identifiedCore.card - 2) / 2` points on each side.  This file derives the
density threshold used by irreducibility directly from the CFP core-loss
estimate.  The additive constant `3` is the exact harmless slack needed to
pass through natural subtraction and division by two.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Elementary floor estimate used when splitting all but one point into
two balanced pools. -/
theorem card_le_two_mul_half_sub_two_add_three (n : ℕ) :
    n ≤ 2 * ((n - 2) / 2) + 3 := by
  omega

/-- A loss budget for the selected CFP core implies exactly the real-valued
core-retention inequality consumed by `exists_balanced_side_selections`.

The hypothesis says that after paying the selected loss, enough of the
population remains for two pools of density `delta`, with three points of
integer-rounding slack. -/
theorem coreRetention_of_loss_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hbudget :
      2 * delta * (A.card : ℝ) + 3 +
          ((selector.chosen A hA).loss : ℝ) ≤ (A.card : ℝ)) :
    delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) := by
  let S := selector.chosen A hA
  have hcoreNat : A.card ≤ S.identifiedCore.card + S.loss := by
    rw [S.card_identifiedCore]
    exact S.witness.core_large
  have hcore : (A.card : ℝ) ≤
      (S.identifiedCore.card : ℝ) + (S.loss : ℝ) := by
    exact_mod_cast hcoreNat
  have hfloorNat : S.identifiedCore.card ≤
      2 * ((S.identifiedCore.card - 2) / 2) + 3 :=
    card_le_two_mul_half_sub_two_add_three S.identifiedCore.card
  have hfloor : (S.identifiedCore.card : ℝ) ≤
      2 * ((((S.identifiedCore.card - 2) / 2 : ℕ) : ℝ)) + 3 := by
    exact_mod_cast hfloorNat
  dsimp only [S] at hcore hfloor ⊢
  nlinarith

/-- The analytic loss estimate supplied by the bounded CFP selection turns
the source's scale--logarithm hierarchy into the exact finite loss budget
used by the balanced partition.  The constant `4` consists of the one-point
slack in the CFP loss estimate and the three-point floor slack in the
alternating split. -/
theorem loss_budget_of_selectedCFP_hierarchy
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hhierarchy :
      2 * delta * (A.card : ℝ) + 4 +
          (context.lossConstant d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    2 * delta * (A.card : ℝ) + 3 +
        ((selector.chosen A hA).loss : ℝ) ≤ (A.card : ℝ) := by
  have hloss := (selector.input A hA).selectedCFP_loss_le
  change ((selector.chosen A hA).loss : ℝ) ≤
      (context.lossConstant d : ℝ) *
        ((selector.input A hA).scale : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 at hloss
  linarith

/-- Source hierarchy form of core retention, with the selected CFP loss
eliminated. -/
theorem coreRetention_of_selectedCFP_hierarchy
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hhierarchy :
      2 * delta * (A.card : ℝ) + 4 +
          (context.lossConstant d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) := by
  exact coreRetention_of_loss_budget selector
    (loss_budget_of_selectedCFP_hierarchy selector hhierarchy)

/-- The concrete CFP loss estimate reduces the population-loss budget to a
single scale/logarithm inequality.  This is the exact numerical condition
which the source obtains by taking the CFP reserve scale sublinear and the
ambient population sufficiently large. -/
theorem loss_budget_of_scale_log_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hhierarchy :
      2 * delta * (A.card : ℝ) + 4 +
          (context.lossConstant d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    2 * delta * (A.card : ℝ) + 3 +
        ((selector.chosen A hA).loss : ℝ) ≤ (A.card : ℝ) := by
  have hloss : ((selector.chosen A hA).loss : ℝ) ≤
      (context.lossConstant d : ℝ) *
        ((selector.input A hA).scale : ℝ) *
          Real.logb 2 (A.card : ℝ) + 1 := by
    simpa [Reduction.BoundedCFPSelector.chosen,
      Reduction.EligibleInput.selectedCFP] using
      (selector.input A hA).selectedCFP_loss_le
  linarith

/-- The eligibility scale upper bound converts the fixed CFP loss ratio into
the scale/logarithm hierarchy required above.  The remaining hypothesis is
purely a fixed-constant/population inequality; it no longer mentions the
chosen reserve scale. -/
theorem scale_log_budget_of_context_ratio
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hratio :
      ((2 * delta * (context.scaleDen d : ℝ) +
          (context.lossConstant d : ℝ) * (context.scaleNum d : ℝ)) *
            (A.card : ℝ)) + 4 * (context.scaleDen d : ℝ) ≤
        (context.scaleDen d : ℝ) * (A.card : ℝ)) :
    2 * delta * (A.card : ℝ) + 4 +
        (context.lossConstant d : ℝ) *
          ((selector.input A hA).scale : ℝ) *
            Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ) := by
  have hscale := (selector.input A hA).scale_upper
  have hscaleLoss :
      (context.lossConstant d : ℝ) *
          ((context.scaleDen d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ)) ≤
        (context.lossConstant d : ℝ) *
          ((context.scaleNum d : ℝ) * (A.card : ℝ)) :=
    mul_le_mul_of_nonneg_left hscale (by positivity)
  have hden : (0 : ℝ) < context.scaleDen d := by
    exact_mod_cast context.scaleDen_pos d
  nlinarith

/-- The complete core-retention estimate from the fixed CFP constants and
the large-population ratio inequality. -/
theorem coreRetention_of_context_ratio
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hratio :
      ((2 * delta * (context.scaleDen d : ℝ) +
          (context.lossConstant d : ℝ) * (context.scaleNum d : ℝ)) *
            (A.card : ℝ)) + 4 * (context.scaleDen d : ℝ) ≤
        (context.scaleDen d : ℝ) * (A.card : ℝ)) :
    delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) :=
  coreRetention_of_loss_budget selector
    (loss_budget_of_scale_log_budget selector
      (scale_log_budget_of_context_ratio selector hratio))

/-- Core retention directly from the source scale/logarithm hierarchy and
the selected CFP loss theorem. -/
theorem coreRetention_of_scale_log_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ}
    (hhierarchy :
      2 * delta * (A.card : ℝ) + 4 +
          (context.lossConstant d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) :=
  coreRetention_of_loss_budget selector
    (loss_budget_of_scale_log_budget selector hhierarchy)

/-- Side selection with its density premise discharged by the actual CFP
loss estimate and a single explicit population budget. -/
theorem exists_balanced_side_selections_of_loss_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta)
    (hbudget :
      2 * delta * (A.card : ℝ) + 3 +
          ((selector.chosen A hA).loss : ℝ) ≤ (A.card : ℝ)) :
    ∃ h₁ : selector.Eligible
        (Reduction.identifiedTranslate D.A₁ D.a),
      ∃ h₂ : selector.Eligible
        (Reduction.identifiedTranslate D.A₂ D.a),
        let T₁ := selector.chosen
          (Reduction.identifiedTranslate D.A₁ D.a) h₁
        let T₂ := selector.chosen
          (Reduction.identifiedTranslate D.A₂ D.a) h₂
        T₁.dimension = (selector.chosen A hA).dimension ∧
          T₂.dimension = (selector.chosen A hA).dimension ∧
          gamma *
              ((selector.chosen A hA).progression.volume : ℝ) ≤
            (T₁.progression.volume : ℝ) ∧
          gamma *
              ((selector.chosen A hA).progression.volume : ℝ) ≤
            (T₂.progression.volume : ℝ) := by
  exact exists_balanced_side_selections_of_coreRetention selector D hirr
    hclosed hdelta (coreRetention_of_loss_budget selector hbudget)

/-- Side selection with the density premise discharged all the way from the
actual CFP loss theorem and the source's scale/logarithm hierarchy. -/
theorem exists_balanced_side_selections_of_scale_log_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta)
    (hhierarchy :
      2 * delta * (A.card : ℝ) + 4 +
          (context.lossConstant d : ℝ) *
            ((selector.input A hA).scale : ℝ) *
              Real.logb 2 (A.card : ℝ) ≤ (A.card : ℝ)) :
    ∃ h₁ : selector.Eligible
        (Reduction.identifiedTranslate D.A₁ D.a),
      ∃ h₂ : selector.Eligible
        (Reduction.identifiedTranslate D.A₂ D.a),
        let T₁ := selector.chosen
          (Reduction.identifiedTranslate D.A₁ D.a) h₁
        let T₂ := selector.chosen
          (Reduction.identifiedTranslate D.A₂ D.a) h₂
        T₁.dimension = (selector.chosen A hA).dimension ∧
          T₂.dimension = (selector.chosen A hA).dimension ∧
          gamma *
              ((selector.chosen A hA).progression.volume : ℝ) ≤
            (T₁.progression.volume : ℝ) ∧
          gamma *
              ((selector.chosen A hA).progression.volume : ℝ) ≤
            (T₂.progression.volume : ℝ) := by
  exact exists_balanced_side_selections_of_loss_budget selector D hirr
    hclosed hdelta (loss_budget_of_scale_log_budget selector hhierarchy)

end

end Erdos186.PZ.Intersection
