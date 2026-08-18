/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ControlledSideSelection
import ErdosProblems.Erdos186.PZ.Intersection.ProgressionContainment

/-!
# Concrete Lemma 11 for the two balanced pools

This file removes the abstract bounding-set-control premise from the balanced
side selection theorem.  The actual enhanced CFP witnesses and their fixed
scale denominator supply one canonical integer control box for both sides.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- **Pham--Zakharov Lemma 11, bounded-selector form.**

The CFP loss budget makes both alternating pools dense, candidate closure
makes their translates eligible, irreducibility gives the common displayed
dimension and volume lower bounds, and progression coverage puts both side
progressions in translates of the same explicit control box. -/
theorem exists_balanced_side_selections_with_canonical_controlBox_of_loss_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {ambient : ℕ}
    {A : Finset (LatticePoint ambient)} {hA : selector.Eligible A}
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
        let S := selector.chosen A hA
        let T₁ := selector.chosen
          (Reduction.identifiedTranslate D.A₁ D.a) h₁
        let T₂ := selector.chosen
          (Reduction.identifiedTranslate D.A₂ D.a) h₂
        T₁.dimension = S.dimension ∧
          T₂.dimension = S.dimension ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₁.progression.volume : ℝ) ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₂.progression.volume : ℝ) ∧
          (∃ t, T₁.progression.carrier ⊆ PZ.translate t
            (controlIntegerBox S.progression
              (2 * context.scaleDen S.dimension)).carrier) ∧
          (∃ t, T₂.progression.carrier ⊆ PZ.translate t
            (controlIntegerBox S.progression
              (2 * context.scaleDen S.dimension)).carrier) := by
  exact exists_balanced_side_selections_with_controlledBox_of_loss_budget
    selector D
      (controlIntegerBox (selector.chosen A hA).progression
        (2 * context.scaleDen (selector.chosen A hA).dimension))
      hirr hclosed
      (boundedCoordinateBoundingSetsControlled_of_enhancedCFP
        selector delta)
      hdelta hbudget

end

end Erdos186.PZ.Intersection
