import ErdosProblems.Erdos547.AllocationTrimming

/-!
# Splitting a skew matching into two compatible scalar pieces
-/

noncomputable section

namespace Erdos547.DPRS

open Finset SimpleGraph

variable {V : Type*} [Fintype V] {G : SimpleGraph V} {γ : ℝ}

namespace SkewMatching

theorem exists_split_total (σ : SkewMatching G γ) (r : ℝ) (hr : 0 ≤ r) (hrσ : r ≤ σ.total) :
    ∃ τ ρ : SkewMatching G γ, τ.IsSuballocation σ ∧ ρ.IsSuballocation σ ∧ τ.total = r ∧
      (∀ u v, τ.weight u v + ρ.weight u v = σ.weight u v) ∧
      (∀ u, τ.load u + ρ.load u = σ.load u) ∧
      (∀ u, τ.outLoad u + ρ.outLoad u = σ.outLoad u) := by
  by_cases hz : σ.total = 0
  · have hr0 : r = 0 := by linarith
    let ρ := σ.scale 0 le_rfl zero_le_one
    refine ⟨σ, ρ, fun _ _ ↦ ⟨le_rfl, le_rfl⟩,
      σ.scale_isSuballocation 0 le_rfl zero_le_one, hz.trans hr0.symm, ?_, ?_, ?_⟩
    · intro u v
      change σ.weight u v + 0 * σ.weight u v = _
      ring
    · intro u
      rw [show ρ.load u = 0 * σ.load u from σ.scale_load 0 le_rfl zero_le_one u]
      ring
    · intro u
      change σ.outLoad u + (∑ v, 0 * σ.weight u v) / (1 + γ) = _
      simp only [zero_mul, Finset.sum_const_zero, zero_div, add_zero]
  have hp : 0 < σ.total := lt_of_le_of_ne (hr.trans hrσ) (Ne.symm hz)
  let t := r / σ.total
  have ht : 0 ≤ t := div_nonneg hr hp.le
  have ht1 : t ≤ 1 := (div_le_one hp).mpr hrσ
  let τ := σ.scale t ht ht1
  let ρ := σ.scale (1 - t) (by linarith) (by linarith)
  refine ⟨τ, ρ, σ.scale_isSuballocation t ht ht1,
    σ.scale_isSuballocation (1 - t) (by linarith) (by linarith), ?_, ?_, ?_, ?_⟩
  · rw [show τ.total = t * σ.total from σ.scale_total t ht ht1, div_mul_cancel₀ _ hz]
  · intro u v
    change t * σ.weight u v + (1 - t) * σ.weight u v = _
    ring
  · intro u
    rw [show τ.load u = t * σ.load u from σ.scale_load t ht ht1 u,
      show ρ.load u = (1 - t) * σ.load u from σ.scale_load (1 - t) _ _ u]
    ring
  · intro u
    change (∑ v, t * σ.weight u v) / (1 + γ) +
      (∑ v, (1 - t) * σ.weight u v) / (1 + γ) = _
    rw [← Finset.mul_sum, ← Finset.mul_sum]
    change t * (∑ v, σ.weight u v) / (1 + γ) +
      (1 - t) * (∑ v, σ.weight u v) / (1 + γ) = (∑ v, σ.weight u v) / (1 + γ)
    ring

end SkewMatching

end Erdos547.DPRS

#print axioms Erdos547.DPRS.SkewMatching.exists_split_total
