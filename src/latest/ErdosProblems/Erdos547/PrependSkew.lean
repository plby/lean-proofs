import ErdosProblems.Erdos547.AllocationOperations

/-!
# Prepending an existing skew allocation to a residual anchored pair
-/

namespace Erdos547.DPRS

open SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.prepend_right {σ : SkewMatching G γ} {τ ρ : SkewMatching G δ}
    {ν : FractionalMatching G} {w : EdgeWeights G} {d c : V}
    (h : AnchoredPair σ τ (w.truncate ρ.load ρ.load_nonneg) d c)
    (hdom : PairDominated σ τ ν) (hcap : ∀ u, ρ.load u + ν.load u ≤ 1)
    (hfit : ρ.Fits w c) :
    ∃ ht : ∀ u, ρ.load u + τ.load u ≤ 1, AnchoredPair σ (ρ.add τ ht) w d c := by
  have ht (u : V) : ρ.load u + τ.load u ≤ 1 :=
    (add_le_add le_rfl (hdom.right.load_le u)).trans (hcap u)
  refine ⟨ht, h.adjacent, ?_, ?_, ?_, ?_⟩
  · intro u
    rw [SkewMatching.add_load]
    linarith [hdom.load_le u, hcap u]
  · intro u
    exact (h.fits_left u).trans (w.truncate_weight_le ρ.load ρ.load_nonneg d u)
  · intro u
    rw [SkewMatching.add_outLoad]
    exact add_le_of_le_truncated (hfit u) (ρ.outLoad_le_load u) (h.fits_right u)
  · intro u
    rw [SkewMatching.add_outLoad]
    have htr := h.joint u
    change σ.outLoad u + τ.outLoad u ≤
      max (max 0 (w.weight d u - ρ.load u)) (max 0 (w.weight c u - ρ.load u)) at htr
    rw [max_truncated] at htr
    have hh := add_le_of_le_truncated ((hfit u).trans (le_max_right _ _))
      (ρ.outLoad_le_load u) htr
    linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.prepend_right
