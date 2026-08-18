/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Codex
-/
import ErdosProblems.Erdos186.PZ.Intersection.SlabCandidatePullback
import ErdosProblems.Erdos186.PZ.Intersection.SlabJohnBound

/-!
# Selecting a CFP witness from a dense translated slab

A slab filter on a selected side lives after translating the source core by
its distinguished point.  Definition 9, however, is stated for subsets of the
original selected core.  The theorem below performs the inverse translation,
uses candidate closure and bounded coordinate irreducibility there, and then
transports the resulting selected witness back to the literal slab filter.
-/

namespace Erdos186.PZ.Intersection

noncomputable section

set_option autoImplicit false

/-- A dense subset of a translated source-core candidate is itself an
eligible selected CFP input, with the source rank and volume lower bound.

This is the exact selection bridge needed before applying the functional-slab
John contradiction. -/
theorem exists_selectedWitness_of_dense_subset_identifiedTranslate
    {beta eta : ℝ} {context : Reduction.HigherDimensionalContext beta eta}
    (selector : Reduction.BoundedCFPSelector context) {ambient : ℕ}
    {A : Finset (LatticePoint ambient)} {hA : selector.Eligible A}
    {delta gamma : ℝ}
    (hirr : Reduction.IsBoundedCoordinateIrreducible selector A hA
      delta gamma)
    (hclosed : selector.CandidateClosedAt A hA delta)
    (X : Finset
      (LatticePoint (selector.chosen A hA).dimension))
    (hXsub : X ⊆ (selector.chosen A hA).identifiedCore)
    (a : LatticePoint (selector.chosen A hA).dimension)
    (ha : a ∈ (gapCoefficientBox
      (selector.chosen A hA).progression).carrier)
    (Z : Finset
      (LatticePoint (selector.chosen A hA).dimension))
    (hZsub : Z ⊆ Reduction.identifiedTranslate X a)
    (hZne : Z.Nonempty)
    (hdense : delta * (A.card : ℝ) ≤ (Z.card : ℝ)) :
    ∃ hZ : selector.Eligible Z,
      let T := selector.chosen Z hZ
      T.dimension = (selector.chosen A hA).dimension ∧
        gamma * ((selector.chosen A hA).progression.volume : ℝ) ≤
          (T.progression.volume : ℝ) := by
  let Y := PZ.translate a Z
  have hYsub : Y ⊆ (selector.chosen A hA).identifiedCore := by
    exact (pzTranslate_subset_of_subset_identifiedTranslate hZsub).trans hXsub
  have hYne : Y.Nonempty :=
    (pzTranslate_pullback_nonempty a Z).2 hZne
  have hdenseY : delta * (A.card : ℝ) ≤ (Y.card : ℝ) := by
    simpa only [Y, PZ.card_translate] using hdense
  let hshift : selector.Eligible (Reduction.identifiedTranslate Y a) :=
    hclosed Y hYsub hYne hdenseY a ha
  have hout := Reduction.boundedCoordinateIrreducible_rank_volume selector
    hirr Y hYsub hYne hdenseY a ha hshift
  have hidentify : Reduction.identifiedTranslate Y a = Z := by
    dsimp only [Y]
    exact identifiedTranslate_pzTranslate a Z
  rw [← hidentify]
  exact ⟨hshift, hout⟩

end

end Erdos186.PZ.Intersection
