import ErdosProblems.Erdos547.DisjointFilling

/-!
# Combining anchored pairs carried by disjoint fractional pieces
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.combine_pieces
    {σ₁ σ₂ : SkewMatching G γ} {τ₁ τ₂ : SkewMatching G δ}
    {μ₁ μ₂ μ : FractionalMatching G} {w : EdgeWeights G} {c d : V}
    (h₁ : AnchoredPair σ₁ τ₁ w c d)
    (h₂ : AnchoredPair σ₂ τ₂ (w.truncate μ₁.load μ₁.load_nonneg) c d)
    (hdom₁ : PairDominated σ₁ τ₁ μ₁) (hdom₂ : PairDominated σ₂ τ₂ μ₂)
    (hμ : ∀ u v, μ₁.weight u v + μ₂.weight u v ≤ μ.weight u v) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ,
      AnchoredPair σ τ w c d ∧ PairDominated σ τ μ ∧
      σ.total = σ₁.total + σ₂.total ∧ τ.total = τ₁.total + τ₂.total := by
  have hc (u : V) : μ₁.load u + μ₂.load u ≤ 1 := by
    have hh : μ₁.load u + μ₂.load u ≤ μ.load u := by
      rw [FractionalMatching.load, FractionalMatching.load, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ ↦ hμ u v
    exact hh.trans (μ.load_le_one u)
  obtain ⟨hs, ht, hpair, hdom⟩ := h₁.add_truncated h₂ hdom₁ hdom₂ hc
  exact ⟨σ₁.add σ₂ hs, τ₁.add τ₂ ht, hpair, hdom.mono hμ,
    SkewMatching.add_total _ _ _, SkewMatching.add_total _ _ _⟩

theorem AnchoredPair.single_left (σ : SkewMatching G γ) (δ : ℝ) (hδ : 0 ≤ δ)
    (w : EdgeWeights G) {c d : V} (hcd : G.Adj c d) (hfit : σ.Fits w c) :
    AnchoredPair σ (SkewMatching.zero G δ hδ) w c d := by
  have hz (u : V) : (SkewMatching.zero G δ hδ).outLoad u = 0 := by
    simp only [SkewMatching.outLoad, SkewMatching.zero, Finset.sum_const_zero, zero_div]
  have hl (u : V) : (SkewMatching.zero G δ hδ).load u = 0 := by
    simp only [SkewMatching.load, SkewMatching.inLoad, SkewMatching.outLoad, SkewMatching.zero,
      Finset.sum_const_zero, mul_zero, zero_div, add_zero]
  refine ⟨hcd, ?_, hfit, ?_, ?_⟩
  · intro u
    rw [hl, add_zero]
    exact σ.load_le_one u
  · intro u
    rw [hz]
    exact w.nonnegative d u
  · intro u
    rw [hz, add_zero]
    exact (hfit u).trans (le_max_left _ _)

theorem PairDominated.single_left (σ : SkewMatching G γ) (δ : ℝ) (hδ : 0 ≤ δ)
    {μ : FractionalMatching G} (h : σ.DominatedByFractional μ) :
    PairDominated σ (SkewMatching.zero G δ hδ) μ := by
  intro u v
  simpa only [SkewMatching.endpointWeight, SkewMatching.zero, mul_zero, add_zero, zero_div]
    using h u v

theorem AnchoredPair.extend_left_piece
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {H P μ : FractionalMatching G}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d) (hdom : PairDominated σ τ H)
    (hpieces : ∀ u v, H.weight u v + P.weight u v ≤ μ.weight u v)
    (r : ℝ) (hr : 0 ≤ r)
    (hsat : r ≤ (w.truncate H.load H.load_nonneg).saturation P.load c) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w c d ∧ PairDominated σ' τ' μ ∧
      σ'.total = σ.total + r ∧ τ'.total = τ.total := by
  obtain ⟨ρ, hρ, hfit, htotal⟩ := exists_skew_of_saturation_exact P
    (w.truncate H.load H.load_nonneg) c γ σ.skew_nonneg r hr hsat
  have hpair := AnchoredPair.single_left ρ δ τ.skew_nonneg _ h.adjacent hfit
  have hdom' := PairDominated.single_left ρ δ τ.skew_nonneg hρ
  obtain ⟨σ', τ', hp, hd, hs, ht⟩ := h.combine_pieces hpair hdom hdom' hpieces
  refine ⟨σ', τ', hp, hd, ?_, ?_⟩
  · rwa [htotal] at hs
  · simpa only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, add_zero] using ht

theorem AnchoredPair.extend_right_piece
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {H P μ : FractionalMatching G}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d) (hdom : PairDominated σ τ H)
    (hpieces : ∀ u v, H.weight u v + P.weight u v ≤ μ.weight u v)
    (r : ℝ) (hr : 0 ≤ r)
    (hsat : r ≤ (w.truncate H.load H.load_nonneg).saturation P.load d) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w c d ∧ PairDominated σ' τ' μ ∧
      σ'.total = σ.total ∧ τ'.total = τ.total + r := by
  obtain ⟨τ', σ', hp, hd, ht, hs⟩ := h.swap.extend_left_piece hdom.swap hpieces r hr hsat
  exact ⟨σ', τ', hp.swap, hd.swap, hs, ht⟩

theorem anchoredPair_of_one_side {σ : SkewMatching G γ} {τ : SkewMatching G δ}
    {J : FractionalMatching G} {w : EdgeWeights G} {c d : V} (hcd : G.Adj c d)
    (hdom : PairDominated σ τ J) (U : Finset V) (hσ : ∀ u ∉ U, σ.outLoad u = 0)
    (hfit : τ.Fits w d) (hU : ∀ u ∈ U, J.load u ≤ w.weight c u) :
    AnchoredPair σ τ w c d := by
  refine ⟨hcd, fun u ↦ (hdom.load_le u).trans (J.load_le_one u), ?_, hfit, ?_⟩
  · intro u
    by_cases hu : u ∈ U
    · exact ((σ.outLoad_le_load u).trans (hdom.left.load_le u)).trans (hU u hu)
    · rw [hσ u hu]
      exact w.nonnegative c u
  · intro u
    by_cases hu : u ∈ U
    · exact ((add_le_add (σ.outLoad_le_load u) (τ.outLoad_le_load u)).trans
        (hdom.load_le u)).trans ((hU u hu).trans (le_max_left _ _))
    · rw [hσ u hu, zero_add]
      exact (hfit u).trans (le_max_right _ _)

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.combine_pieces
