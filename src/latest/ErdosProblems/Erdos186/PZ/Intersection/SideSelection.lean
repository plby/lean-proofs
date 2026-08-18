/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.ConvexPools

/-!
# Selecting the two balanced CFP sides

Candidate-domain closure and bounded coordinate irreducibility apply
directly to the balanced pools produced from a capped convex combination on
the identified core.  This file packages that exact nonvacuous part of
Pham--Zakharov Lemma 11.  The only numerical inputs are the two displayed
density inequalities; deriving them from the CFP loss estimate and the
large-population hierarchy is a separate analytic step.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- The explicit core-retention inequality forces the selected coefficient
lattice to have positive dimension.  In dimension zero there is only one
lattice point, whereas the right side of the retention inequality would
have to be positive. -/
theorem selectedDimension_pos_of_coreRetention
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta : ℝ} (hdelta : 0 < delta)
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) :
    0 < (selector.chosen A hA).dimension := by
  by_contra hdim
  have hdim0 : (selector.chosen A hA).dimension = 0 :=
    Nat.eq_zero_of_not_pos hdim
  have hpopulation : (0 : ℝ) < A.card := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  have hpositive : (0 : ℝ) <
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) :=
    (mul_pos hdelta hpopulation).trans_le hcoreRetention
  have hcard : (selector.chosen A hA).identifiedCore.card ≤ 1 := by
    apply Finset.card_le_one.mpr
    intro x _hx y _hy
    funext i
    have hi := i.isLt
    omega
  have hzero :
      ((selector.chosen A hA).identifiedCore.card - 2) / 2 = 0 := by
    omega
  rw [hzero] at hpositive
  norm_num at hpositive

/-- The two balanced pools are actual eligible coordinate candidates, and
their selected CFP progressions have the original selected dimension and the
irreducibility volume lower bound. -/
theorem exists_balanced_side_selections
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
    (hdense₁ : delta * (A.card : ℝ) ≤ (D.A₁.card : ℝ))
    (hdense₂ : delta * (A.card : ℝ) ≤ (D.A₂.card : ℝ)) :
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
  have hA₁sub : D.A₁ ⊆ (selector.chosen A hA).identifiedCore :=
    D.A₁_subset_erase.trans (Finset.erase_subset _ _)
  have hA₂sub : D.A₂ ⊆ (selector.chosen A hA).identifiedCore :=
    D.A₂_subset_erase.trans (Finset.erase_subset _ _)
  have haBox : D.a ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier :=
    (selector.chosen A hA).identifiedCore_subset_coefficientBox D.a_mem
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
  obtain ⟨h₁, hT₁⟩ :=
    boundedCoordinateIrreducible_rank_volume_of_candidateClosed selector
      hirr hclosed D.A₁ hA₁sub hA₁ne hdense₁ D.a haBox
  obtain ⟨h₂, hT₂⟩ :=
    boundedCoordinateIrreducible_rank_volume_of_candidateClosed selector
      hirr hclosed D.A₂ hA₂sub hA₂ne hdense₂ D.a haBox
  exact ⟨h₁, h₂, hT₁.1, hT₂.1, hT₁.2, hT₂.2⟩

/-- Core retention turns the balanced cardinality bounds into the two density
hypotheses required by `exists_balanced_side_selections`. -/
theorem exists_balanced_side_selections_of_coreRetention
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
    (hcoreRetention : delta * (A.card : ℝ) ≤
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ)) :
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
  have hcard₁ :
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) ≤
        (D.A₁.card : ℝ) := by
    exact_mod_cast D.card_lower_A₁
  have hcard₂ :
      ((((selector.chosen A hA).identifiedCore.card - 2) / 2 : ℕ) : ℝ) ≤
        (D.A₂.card : ℝ) := by
    exact_mod_cast D.card_lower_A₂
  exact exists_balanced_side_selections selector D hirr hclosed hdelta
    (hcoreRetention.trans hcard₁) (hcoreRetention.trans hcard₂)

end

end Erdos186.PZ.Intersection
