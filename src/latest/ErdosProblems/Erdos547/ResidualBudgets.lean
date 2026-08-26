import ErdosProblems.Erdos547.MatchingCompletion

/-!
# Positive totals split into parts of a prescribed skew
-/

namespace Erdos547.DPRS

theorem positive_skew_parts (r γ : ℝ) (hr : 0 < r) (hγ : 0 ≤ γ) :
    0 < r / (1 + γ) ∧ 0 ≤ γ * (r / (1 + γ)) ∧
      r / (1 + γ) + γ * (r / (1 + γ)) = r ∧
      (γ * (r / (1 + γ))) / (r / (1 + γ)) = γ := by
  have hden : 0 < 1 + γ := by linarith
  have hp : 0 < r / (1 + γ) := div_pos hr hden
  refine ⟨hp, mul_nonneg hγ hp.le, ?_, mul_div_cancel_right₀ γ (ne_of_gt hp)⟩
  field_simp [ne_of_gt hden]

noncomputable section

open Finset SimpleGraph
open scoped BigOperators

variable {V : Type*} [Fintype V] {G : SimpleGraph V}

theorem exists_completion_of_totals (μ : FractionalMatching G) (U W : Finset V)
    (hdis : Disjoint U W) (hruns : μ.RunsBetween U W) (w : EdgeWeights G) (c : V)
    (hW : ∀ u ∈ W, μ.load u ≤ w.weight c u) (γ δ r s : ℝ)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ) (hr : 0 < r) (hs : 0 < s)
    (hlo : max (r / (1 + γ)) (γ * (r / (1 + γ))) +
      min (s / (1 + δ)) (δ * (s / (1 + δ))) ≤ μ.total)
    (hhi : μ.total ≤ min (r / (1 + γ)) (γ * (r / (1 + γ))) +
      max (s / (1 + δ)) (δ * (s / (1 + δ)))) :
    ∃ σ : SkewMatching G γ, ∃ τ : SkewMatching G δ, PairDominated σ τ μ ∧
      σ.total = r ∧ max 0 (w.saturation μ.load c - σ.total) ≤ τ.total ∧
      (∀ u ∉ U, σ.outLoad u = 0) ∧ τ.Fits w c := by
  obtain ⟨ha₁, ha₂, hsumA, hratioA⟩ := positive_skew_parts r γ hr hγ
  obtain ⟨hb₁, hb₂, hsumB, hratioB⟩ := positive_skew_parts s δ hs hδ
  have hex := exists_matching_completion μ U W hdis hruns w c hW
    (r / (1 + γ)) (γ * (r / (1 + γ))) (s / (1 + δ)) (δ * (s / (1 + δ)))
    ha₁ ha₂ hb₁ hb₂ hlo hhi
  rw [hratioA, hratioB] at hex
  obtain ⟨σ, τ, hdom, htotal, hlower, hout, hfit, _⟩ := hex
  exact ⟨σ, τ, hdom, htotal.trans hsumA, hlower, hout, hfit⟩

end

end Erdos547.DPRS

#print axioms Erdos547.DPRS.exists_completion_of_totals
