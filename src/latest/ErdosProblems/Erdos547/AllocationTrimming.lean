import ErdosProblems.Erdos547.AllocationOperations

/-!
# Trimming allocations to exact totals
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ ε ζ : ℝ}

namespace SkewMatching

theorem IsSuballocation.outLoad_le {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    (h : τ.IsSuballocation σ) (u : V) : τ.outLoad u ≤ σ.outLoad u := by
  simp only [outLoad, Finset.sum_div]
  exact Finset.sum_le_sum fun v _ ↦ (h u v).1

theorem scale_isSuballocation (σ : SkewMatching G γ) (t : ℝ) (ht : 0 ≤ t) (ht1 : t ≤ 1) :
    (σ.scale t ht ht1).IsSuballocation σ := by
  intro u v
  have hw := mul_le_mul_of_nonneg_right ht1 (σ.nonnegative u v)
  simp only [one_mul] at hw
  exact ⟨div_le_div_of_nonneg_right hw σ.denominator_pos.le,
    div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hw σ.skew_nonneg) σ.denominator_pos.le⟩

theorem exists_suballocation_total (σ : SkewMatching G γ) (r : ℝ) (hr : 0 ≤ r)
    (hbound : r ≤ σ.total) :
    ∃ τ : SkewMatching G γ, τ.IsSuballocation σ ∧ τ.total = r := by
  by_cases hz : σ.total = 0
  · have hr0 : r = 0 := by linarith
    exact ⟨σ, fun _ _ ↦ ⟨le_rfl, le_rfl⟩, hz.trans hr0.symm⟩
  have hp : 0 < σ.total := lt_of_le_of_ne (hr.trans hbound) (Ne.symm hz)
  have ht : 0 ≤ r / σ.total := div_nonneg hr hp.le
  have ht1 : r / σ.total ≤ 1 := (div_le_one hp).mpr hbound
  refine ⟨σ.scale (r / σ.total) ht ht1, σ.scale_isSuballocation _ ht ht1, ?_⟩
  rw [scale_total, div_mul_cancel₀ _ hz]

end SkewMatching

theorem AnchoredPair.of_suballocations {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {σ' : SkewMatching G ε} {τ' : SkewMatching G ζ} {w : EdgeWeights G} {c d : V}
    (h : AnchoredPair σ τ w c d) (hs : σ'.IsSuballocation σ) (ht : τ'.IsSuballocation τ) :
    AnchoredPair σ' τ' w c d := by
  refine ⟨h.adjacent, ?_, ?_, ?_, ?_⟩
  · intro u
    exact (add_le_add (hs.load_le u) (ht.load_le u)).trans (h.capacity u)
  · intro u
    exact (hs.outLoad_le u).trans (h.fits_left u)
  · intro u
    exact (ht.outLoad_le u).trans (h.fits_right u)
  · intro u
    exact (add_le_add (hs.outLoad_le u) (ht.outLoad_le u)).trans (h.joint u)

theorem PairDominated.of_suballocations {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {σ' : SkewMatching G ε} {τ' : SkewMatching G ζ} {μ : FractionalMatching G}
    (h : PairDominated σ τ μ) (hs : σ'.IsSuballocation σ) (ht : τ'.IsSuballocation τ) :
    PairDominated σ' τ' μ :=
  fun u v ↦ (add_le_add (hs.endpoint_le u v) (ht.endpoint_le u v)).trans (h u v)

theorem AnchoredPair.trim {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {w : EdgeWeights G} {c d : V} {μ : FractionalMatching G}
    (h : AnchoredPair σ τ w c d) (hμ : PairDominated σ τ μ)
    (r s : ℝ) (hr : 0 ≤ r) (hs : 0 ≤ s) (hrσ : r ≤ σ.total) (hsτ : s ≤ τ.total) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w c d ∧ PairDominated σ' τ' μ ∧ σ'.total = r ∧ τ'.total = s := by
  obtain ⟨σ', hσ', htotalσ⟩ := σ.exists_suballocation_total r hr hrσ
  obtain ⟨τ', hτ', htotalτ⟩ := τ.exists_suballocation_total s hs hsτ
  exact ⟨σ', τ', h.of_suballocations hσ' hτ', hμ.of_suballocations hσ' hτ', htotalσ, htotalτ⟩

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.trim
