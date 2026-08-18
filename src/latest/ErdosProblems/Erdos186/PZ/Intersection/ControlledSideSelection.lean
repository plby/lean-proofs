/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.CoreRetention

/-!
# Balanced side selections with controlled bounding boxes

This is the source-faithful Lemma 11 package used by the projection-count
full-rank argument.  Candidate closure supplies the two eligible translated
inputs, bounded irreducibility supplies rank and volume, and the independent
coordinate bounding theorem supplies containment in translates of one fixed
integer box.  Density of the balanced pools is derived from the selected CFP
loss budget rather than assumed separately.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Lemma 11 simultaneously for the two balanced pools, including the
controlled-box clauses required by projection cardinality. -/
theorem exists_balanced_side_selections_with_controlledBox_of_loss_budget
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (controlledBox : CFP.IntegerBox
      (selector.chosen A hA).dimension)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcontrolled : BoundedCoordinateBoundingSetsControlled selector A hA
      delta controlledBox.carrier)
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
            (T₂.progression.volume : ℝ) ∧
          (∃ t, T₁.progression.carrier ⊆
            PZ.translate t controlledBox.carrier) ∧
          (∃ t, T₂.progression.carrier ⊆
            PZ.translate t controlledBox.carrier) := by
  have hret := coreRetention_of_loss_budget selector hbudget
  have hA₁sub : D.A₁ ⊆ (selector.chosen A hA).identifiedCore :=
    D.A₁_subset_erase.trans (Finset.erase_subset _ _)
  have hA₂sub : D.A₂ ⊆ (selector.chosen A hA).identifiedCore :=
    D.A₂_subset_erase.trans (Finset.erase_subset _ _)
  have hdense₁ : delta * (A.card : ℝ) ≤ (D.A₁.card : ℝ) := by
    exact hret.trans (by exact_mod_cast D.card_lower_A₁)
  have hdense₂ : delta * (A.card : ℝ) ≤ (D.A₂.card : ℝ) := by
    exact hret.trans (by exact_mod_cast D.card_lower_A₂)
  have hpopulation : (0 : ℝ) < A.card := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  have hA₁ne : D.A₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₁
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have hA₂ne : D.A₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₂
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have haBox : D.a ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier :=
    (selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem
  let h₁ : selector.Eligible
      (Reduction.identifiedTranslate D.A₁ D.a) :=
    hclosed D.A₁ hA₁sub hA₁ne hdense₁ D.a haBox
  let h₂ : selector.Eligible
      (Reduction.identifiedTranslate D.A₂ D.a) :=
    hclosed D.A₂ hA₂sub hA₂ne hdense₂ D.a haBox
  have hout₁ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled D.A₁ hA₁sub hA₁ne hdense₁ D.a haBox h₁
  have hout₂ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled D.A₂ hA₂sub hA₂ne hdense₂ D.a haBox h₂
  exact ⟨h₁, h₂, hout₁.1, hout₂.1, hout₁.2.1, hout₂.2.1,
    hout₁.2.2, hout₂.2.2⟩

/-- Fixed-context form of the controlled two-side selection theorem.  The
CFP loss budget is discharged from the selector's genuine loss theorem and
the fixed scale/loss constants. -/
theorem exists_balanced_side_selections_with_controlledBox_of_context_ratio
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (controlledBox : CFP.IntegerBox
      (selector.chosen A hA).dimension)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hcontrolled : BoundedCoordinateBoundingSetsControlled selector A hA
      delta controlledBox.carrier)
    (hdelta : 0 < delta)
    (hratio :
      ((2 * delta * (context.scaleDen d : ℝ) +
          (context.lossConstant d : ℝ) * (context.scaleNum d : ℝ)) *
            (A.card : ℝ)) + 4 * (context.scaleDen d : ℝ) ≤
        (context.scaleDen d : ℝ) * (A.card : ℝ)) :
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
            (T₂.progression.volume : ℝ) ∧
          (∃ t, T₁.progression.carrier ⊆
            PZ.translate t controlledBox.carrier) ∧
          (∃ t, T₂.progression.carrier ⊆
            PZ.translate t controlledBox.carrier) := by
  exact exists_balanced_side_selections_with_controlledBox_of_loss_budget
    selector D controlledBox hirr hclosed hcontrolled hdelta
      (loss_budget_of_scale_log_budget selector
        (scale_log_budget_of_context_ratio selector hratio))

end

end Erdos186.PZ.Intersection
