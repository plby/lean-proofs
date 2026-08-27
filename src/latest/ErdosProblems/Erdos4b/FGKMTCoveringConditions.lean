/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCoveringHistory

/-! # Source hypotheses for a finite sequence of covering stages -/

namespace Erdos4b.FGKMT

noncomputable section

universe u v w

variable {I : ℕ → Type u} {Ω : ℕ → Type v} {α : Type w}
  [∀ j, Fintype (I j)] [∀ j, Fintype (Ω j)] [DecidableEq α]

structure CoveringConditions (F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α)
    (V : Finset α) (r A m : ℕ) (κ δ D : ℝ) : Prop where
  size_pos : 1 ≤ A
  degree_ge_one : 1 ≤ D
  survival_pos : 0 < κ
  survival_le_one : κ ≤ 1
  error_pos : 0 < δ
  smallness : δ ≤ (1 / coveringScale A D κ) ^ (10 ^ (m + 2))
  vertices_eq : ∀ j < m, (F j).vertices = V
  rank_le : ∀ j < m, (F j).rank ≤ r
  labels_pos : ∀ j < m, 0 < Fintype.card (I j)
  survival_lower : ∀ j ≤ m, ∀ a ∈ V, κ ≤ coveringSurvival F j a
  degree_bound : ∀ j < m, ∀ a ∈ V, (F j).degree a ≤ D * coveringSurvival F j a
  codegree_bound : ∀ j < m, ∀ a ∈ V, ∀ b ∈ V, b ≠ a → (F j).codegree a b ≤ δ
  vertex_bound : ∀ j < m, ∀ i, ∀ a ∈ V,
    (F j).vertexMass i a ≤ δ / Real.sqrt (Fintype.card (I j))

namespace CoveringConditions

variable {F : (j : ℕ) → FiniteEdgeFamily (I j) (Ω j) α}
  {V : Finset α} {r A m : ℕ} {κ δ D : ℝ} (H : CoveringConditions F V r A m κ δ D)

include H

theorem scale_ge : 256 ≤ coveringScale A D κ :=
  (coveringScale_bounds A (zero_le_one.trans H.degree_ge_one)
    H.survival_pos H.survival_le_one).1

theorem stage_smallness {j : ℕ} (hj : j ≤ m) :
    δ ≤ (1 / coveringScale A D κ) ^ (10 ^ (j + 2)) :=
  covering_smallness_mono ((by norm_num : (1 : ℝ) ≤ 256).trans H.scale_ge) hj H.smallness

theorem threshold_lt_one (j : ℕ) (hj : j < m) : coveringThreshold δ (j + 1) < 1 := by
  have hhalf := coveringThreshold_le_half H.error_pos H.scale_ge (Nat.succ_pos j)
    (H.stage_smallness (Nat.succ_le_of_lt hj))
  exact hhalf.trans_lt (by norm_num)

end CoveringConditions

end

end Erdos4b.FGKMT
