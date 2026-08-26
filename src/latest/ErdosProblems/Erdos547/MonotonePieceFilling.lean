import ErdosProblems.Erdos547.PieceCombination
import ErdosProblems.Erdos547.FractionalSaturation

/-!
# Filling a residual fractional piece without decreasing any vertex load
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ δ : ℝ}

theorem AnchoredPair.extend_left_piece_monotone
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {H P μ : FractionalMatching G}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d) (hdom : PairDominated σ τ H)
    (hpieces : ∀ u v, H.weight u v + P.weight u v ≤ μ.weight u v)
    (r : ℝ) (hr : 0 ≤ r)
    (hsat : r ≤ (w.truncate H.load H.load_nonneg).saturation P.load c) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w c d ∧ PairDominated σ' τ' μ ∧
      σ'.total = σ.total + r ∧ τ'.total = τ.total ∧
      ∀ u, σ.load u + τ.load u ≤ σ'.load u + τ'.load u := by
  obtain ⟨ρ, hρ, hfit, htotal⟩ := exists_skew_of_saturation_exact P
    (w.truncate H.load H.load_nonneg) c γ σ.skew_nonneg r hr hsat
  have hpair := AnchoredPair.single_left ρ δ τ.skew_nonneg _ h.adjacent hfit
  have hdom' := PairDominated.single_left ρ δ τ.skew_nonneg hρ
  have hcap (u : V) : H.load u + P.load u ≤ 1 := by
    have hh : H.load u + P.load u ≤ μ.load u := by
      rw [FractionalMatching.load, FractionalMatching.load, ← Finset.sum_add_distrib]
      exact Finset.sum_le_sum fun v _ ↦ hpieces u v
    exact hh.trans (μ.load_le_one u)
  obtain ⟨hs, ht, hp, hd⟩ := h.add_truncated hpair hdom hdom' hcap
  refine ⟨σ.add ρ hs, τ.add (SkewMatching.zero G δ τ.skew_nonneg) ht,
    hp, hd.mono hpieces, ?_, ?_, ?_⟩
  · rw [SkewMatching.add_total, htotal]
  · rw [SkewMatching.add_total]
    simp only [SkewMatching.total, SkewMatching.zero, Finset.sum_const_zero, add_zero]
  · intro u
    rw [SkewMatching.add_load, SkewMatching.add_load]
    linarith [ρ.load_nonneg u, (SkewMatching.zero G δ τ.skew_nonneg).load_nonneg u]

theorem AnchoredPair.fill_fractional_remainder
    {σ : SkewMatching G γ} {τ : SkewMatching G δ} {H μ : FractionalMatching G}
    {w : EdgeWeights G} {c d : V} (h : AnchoredPair σ τ w c d) (hdom : PairDominated σ τ H)
    (hH : ∀ u v, H.weight u v ≤ μ.weight u v)
    (hlower : w.saturation H.load c ≤ σ.total + τ.total) :
    ∃ σ' : SkewMatching G γ, ∃ τ' : SkewMatching G δ,
      AnchoredPair σ' τ' w c d ∧ PairDominated σ' τ' μ ∧
      w.saturation μ.load c ≤ σ'.total + τ'.total ∧ τ'.total = τ.total ∧
      ∀ u, σ.load u + τ.load u ≤ σ'.load u + τ'.load u := by
  let P := μ.sub H hH
  let r := (w.truncate H.load H.load_nonneg).saturation P.load c
  have hr : 0 ≤ r := (w.truncate H.load H.load_nonneg).saturation_nonneg P.load P.load_nonneg c
  have hpieces (u v : V) : H.weight u v + P.weight u v ≤ μ.weight u v := by
    change H.weight u v + (μ.weight u v - H.weight u v) ≤ _
    linarith
  obtain ⟨σ', τ', hp, hd, htσ, htτ, hload⟩ :=
    h.extend_left_piece_monotone hdom hpieces r hr le_rfl
  refine ⟨σ', τ', hp, hd, ?_, htτ, hload⟩
  have he := μ.saturation_sub H hH w c
  change w.saturation H.load c + r = w.saturation μ.load c at he
  linarith

end Erdos547.DPRS

#print axioms Erdos547.DPRS.AnchoredPair.fill_fractional_remainder
