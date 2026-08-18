/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.LargeCoefficientPool
import ErdosProblems.Erdos186.PZ.Intersection.SourceSideSelection

/-!
# Source selection on the high-coefficient alternating pools

For Lemma 14 it is not enough to run CFP on an arbitrary cardinally large
half of the core: its convex coefficients could all be tiny.  The alternating
split first retains a fixed amount of coefficient mass on each side, and the
elementary mass budget below then makes the above-threshold part of each side
`delta`-dense.  Definition 9 is applied to precisely those two parts.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- Lemma 11 on the two high-coefficient parts, with the same canonical
source control box used by the full-rank projection argument. -/
theorem exists_highCoefficient_side_selections_with_sourceControlBox
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {d : ℕ}
    {A : Finset (LatticePoint d)} {hA : selector.Eligible A}
    {delta gamma mu theta : ℝ}
    {a₀ : realImage (selector.chosen A hA).identifiedCore}
    {c : realImage (selector.chosen A hA).identifiedCore → ℝ}
    (D : ConvexPoolsData (selector.chosen A hA).identifiedCore a₀ c mu)
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (hdelta : 0 < delta) (htheta : 0 ≤ theta)
    (hcap : 0 < (mu * (selector.chosen A hA).identifiedCore.card)⁻¹)
    (hmassBudget :
      (A.card : ℝ) * theta +
          delta * (A.card : ℝ) *
            (mu * (selector.chosen A hA).identifiedCore.card)⁻¹ <
        (1 - 2 *
          (mu * (selector.chosen A hA).identifiedCore.card)⁻¹) / 2) :
    let S := selector.chosen A hA
    let H₁ := D.largeA₁ theta
    let H₂ := D.largeA₂ theta
    let m := 2 * context.scaleDen S.dimension
    let B := controlIntegerBox S.progression m
    let Q := (m + 1) ^ S.dimension * 2 ^ S.dimension
    ∃ h₁ : selector.Eligible (Reduction.identifiedTranslate H₁ D.a),
      ∃ h₂ : selector.Eligible (Reduction.identifiedTranslate H₂ D.a),
        let T₁ := selector.chosen (Reduction.identifiedTranslate H₁ D.a) h₁
        let T₂ := selector.chosen (Reduction.identifiedTranslate H₂ D.a) h₂
        T₁.dimension = S.dimension ∧
          T₂.dimension = S.dimension ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₁.progression.volume : ℝ) ∧
          gamma * (S.progression.volume : ℝ) ≤
            (T₂.progression.volume : ℝ) ∧
          (∃ t, T₁.progression.carrier ⊆ CFP.translate t B.carrier) ∧
          (∃ t, T₂.progression.carrier ⊆ CFP.translate t B.carrier) ∧
          B.carrier.card ≤ Q * S.progression.volume := by
  let S := selector.chosen A hA
  let H₁ := D.largeA₁ theta
  let H₂ := D.largeA₂ theta
  let m := 2 * context.scaleDen S.dimension
  let B := controlIntegerBox S.progression m
  let Q := (m + 1) ^ S.dimension * 2 ^ S.dimension
  have hcoreCard : S.identifiedCore.card ≤ A.card := by
    rw [Reduction.SelectedCFP.card_identifiedCore]
    exact Finset.card_le_card S.witness.core_subset
  have hdense₁ : delta * (A.card : ℝ) ≤ (H₁.card : ℝ) := by
    simpa only [H₁, S] using
      D.card_largeA₁_of_budget A.card theta delta hcoreCard htheta hcap
        (le_of_lt hdelta) hmassBudget
  have hdense₂ : delta * (A.card : ℝ) ≤ (H₂.card : ℝ) := by
    simpa only [H₂, S] using
      D.card_largeA₂_of_budget A.card theta delta hcoreCard htheta hcap
        (le_of_lt hdelta) hmassBudget
  have hH₁sub : H₁ ⊆ S.identifiedCore :=
    (D.largeA₁_subset theta).trans
      (D.A₁_subset_erase.trans (Finset.erase_subset _ _))
  have hH₂sub : H₂ ⊆ S.identifiedCore :=
    (D.largeA₂_subset theta).trans
      (D.A₂_subset_erase.trans (Finset.erase_subset _ _))
  have hpopulation : (0 : ℝ) < A.card := by
    exact_mod_cast (selector.eligible_nonempty hA).card_pos
  have hH₁ne : H₁.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₁
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have hH₂ne : H₂.Nonempty := by
    rw [Finset.nonempty_iff_ne_empty]
    intro hzero
    have hle : delta * (A.card : ℝ) ≤ 0 := by
      simpa [hzero] using hdense₂
    exact (not_le_of_gt (mul_pos hdelta hpopulation)) hle
  have haBox : D.a ∈ (gapCoefficientBox S.progression).carrier :=
    S.identifiedCore_subset_coefficientBox D.a_mem
  let h₁ : selector.Eligible (Reduction.identifiedTranslate H₁ D.a) :=
    hclosed H₁ hH₁sub hH₁ne hdense₁ D.a haBox
  let h₂ : selector.Eligible (Reduction.identifiedTranslate H₂ D.a) :=
    hclosed H₂ hH₂sub hH₂ne hdense₂ D.a haBox
  have hcontrolled : BoundedCoordinateBoundingSetsControlled selector A hA
      delta B.carrier := by
    simpa only [B, m, S] using
      boundedCoordinateBoundingSetsControlled_of_enhancedCFP selector delta
  have hout₁ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled H₁ hH₁sub hH₁ne hdense₁ D.a haBox h₁
  have hout₂ := lemma11_of_boundedCoordinateIrreducible selector hA hirr
    hcontrolled H₂ hH₂sub hH₂ne hdense₂ D.a haBox h₂
  have hcard : B.carrier.card ≤ Q * S.progression.volume := by
    simpa only [B, Q, m] using controlIntegerBox_card_le S.progression m
  refine ⟨h₁, h₂, hout₁.1, hout₂.1, hout₁.2.1, hout₂.2.1,
    ?_, ?_, hcard⟩
  · obtain ⟨t, ht⟩ := hout₁.2.2
    exact ⟨t, by simpa only [pzTranslate_eq_cfpTranslate] using ht⟩
  · obtain ⟨t, ht⟩ := hout₂.2.2
    exact ⟨t, by simpa only [pzTranslate_eq_cfpTranslate] using ht⟩

end

end Erdos186.PZ.Intersection
