import ErdosProblems.Erdos547.MatchingCombination
import ErdosProblems.Erdos547.AllocationTrimming

/-!
# Filling disjoint fractional pieces at two adjacent anchors
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.swap {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d) :
    AnchoredPair τ σ w d c := by
  refine ⟨h.adjacent.symm, ?_, h.fits_right, h.fits_left, ?_⟩
  · intro u
    simpa only [add_comm] using h.capacity u
  · intro u
    simpa only [add_comm, max_comm] using h.joint u

theorem PairDominated.swap {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {μ : FractionalMatching G} (h : PairDominated σ τ μ) : PairDominated τ σ μ := by
  intro u v
  simpa only [add_comm] using h u v

theorem PairDominated.mono {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {μ ν : FractionalMatching G} (h : PairDominated σ τ μ)
    (hle : ∀ u v, μ.weight u v ≤ ν.weight u v) : PairDominated σ τ ν :=
  fun u v ↦ (h u v).trans (hle u v)

theorem exists_filling_disjoint (μ₁ μ₂ μ : FractionalMatching G)
    (hμ : ∀ u v, μ₁.weight u v + μ₂.weight u v ≤ μ.weight u v)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d)
    (γ δ : ℝ) (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s)
    (hcr : r ≤ w.saturation μ₁.load c)
    (hds : s ≤ (w.truncate μ₁.load μ₁.load_nonneg).saturation μ₂.load d) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w c d ∧ PairDominated σ τ μ ∧ σ.total = r ∧ τ.total = s := by
  obtain ⟨σ, hσ, hfitσ, htotalσ⟩ := exists_skew_of_saturation_exact μ₁ w c γ hγ r hr hcr
  obtain ⟨τ, hτ, hfitτ, htotalτ⟩ := exists_skew_of_saturation_exact μ₂
    (w.truncate μ₁.load μ₁.load_nonneg) d δ hδ s hs hds
  have hdom : PairDominated σ τ μ := fun u v ↦ (add_le_add (hσ u v) (hτ u v)).trans (hμ u v)
  refine ⟨σ, τ, ⟨hcd, fun u ↦ (hdom.load_le u).trans (μ.load_le_one u), hfitσ, ?_, ?_⟩,
    hdom, htotalσ, htotalτ⟩
  · intro u
    exact (hfitτ u).trans (w.truncate_weight_le μ₁.load μ₁.load_nonneg d u)
  · intro u
    have hleft : σ.outLoad u ≤ max (w.weight c u) (w.weight d u) :=
      (hfitσ u).trans (le_max_left _ _)
    have hload : σ.outLoad u ≤ μ₁.load u := (σ.outLoad_le_load u).trans (hσ.load_le u)
    have hright : τ.outLoad u ≤ max 0
        (max (w.weight c u) (w.weight d u) - μ₁.load u) :=
      (hfitτ u).trans (max_le_max_left _ (sub_le_sub_right (le_max_right _ _) _))
    exact add_le_of_le_truncated hleft hload hright

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_filling_disjoint
