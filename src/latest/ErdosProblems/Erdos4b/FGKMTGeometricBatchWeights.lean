/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTBatchPartition

/-! # The normalized geometric batch weights and their degree targets -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def geometricBatchTarget (j : ℕ) : ℝ := (1 / 5 : ℝ) ^ j * Real.log 5

def geometricBatchProbability (C : ℝ) (j : ℕ) : ℝ := geometricBatchTarget j / C

theorem geometricBatchTarget_pos (j : ℕ) : 0 < geometricBatchTarget j :=
  mul_pos (pow_pos (by norm_num) j) (Real.log_pos (by norm_num))

theorem geometricBatchTarget_succ (j : ℕ) :
    geometricBatchTarget (j + 1) = geometricBatchTarget j / 5 := by
  simp only [geometricBatchTarget, pow_succ]
  ring

theorem geometricBatchTarget_sum (m : ℕ) :
    (∑ j : Fin m, geometricBatchTarget j) =
      (5 / 4 : ℝ) * (1 - (1 / 5 : ℝ) ^ m) * Real.log 5 := by
  simp only [geometricBatchTarget, ← Finset.sum_mul]
  rw [Fin.sum_univ_eq_sum_range, geom_sum_eq (by norm_num : (1 / 5 : ℝ) ≠ 1)]
  ring

theorem geometricBatchTarget_sum_le (m : ℕ) :
    (∑ j : Fin m, geometricBatchTarget j) ≤ (5 / 4 : ℝ) * Real.log 5 := by
  rw [geometricBatchTarget_sum]
  have hp : 0 ≤ (1 / 5 : ℝ) ^ m := pow_nonneg (by norm_num) m
  have hl : 0 < Real.log 5 := Real.log_pos (by norm_num)
  nlinarith [mul_nonneg hp hl.le]

theorem geometricBatchProbability_pos {C : ℝ} (hC : 0 < C) (j : ℕ) :
    0 < geometricBatchProbability C j := div_pos (geometricBatchTarget_pos j) hC

theorem geometricBatchProbability_mul {C : ℝ} (hC : C ≠ 0) (j : ℕ) :
    geometricBatchProbability C j * C = geometricBatchTarget j :=
  div_mul_cancel₀ _ hC

theorem geometricBatchProbability_sum_le_one {C : ℝ} (hC : 0 < C)
    (hbudget : (5 / 4 : ℝ) * Real.log 5 ≤ C) (m : ℕ) :
    (∑ j : Fin m, geometricBatchProbability C j) ≤ 1 := by
  simp only [geometricBatchProbability, ← Finset.sum_div]
  exact (div_le_one hC).mpr ((geometricBatchTarget_sum_le m).trans hbudget)

theorem geometricBatchProbability_le_one {C : ℝ} (hC : 0 < C)
    (hbudget : (5 / 4 : ℝ) * Real.log 5 ≤ C) (j : ℕ) :
    geometricBatchProbability C j ≤ 1 := by
  exact categorical_probability_le_one (fun k : Fin (j + 1) => geometricBatchProbability C k)
    (fun k => (geometricBatchProbability_pos hC k).le)
    (geometricBatchProbability_sum_le_one hC hbudget (j + 1)) ⟨j, Nat.lt_succ_self j⟩

namespace FiniteEdgeFamily

variable {I Ω α : Type*} [Fintype I] [Fintype Ω] [DecidableEq α]

theorem exists_geometric_label_partition (F : FiniteEdgeFamily I Ω α) (m : ℕ)
    {C b t : ℝ} (hC : 0 < C) (hbudget : (5 / 4 : ℝ) * Real.log 5 ≤ C)
    (hb : 0 ≤ b) (hcap : ∀ i, ∀ v ∈ F.vertices, F.vertexMass i v ≤ b) (ht : 0 ≤ t)
    (hdegree : ∀ v ∈ F.vertices, |F.degree v - C| ≤ t)
    (hsmall : 2 * (F.vertices.card : ℝ) * m *
      Real.exp (-2 * t ^ 2 / ((Fintype.card I : ℝ) * b ^ 2)) < 1) :
    ∃ a : I → Option (Fin m), ∀ v ∈ F.vertices, ∀ j : Fin m,
      |(F.restrictLabels (batchLabels a j)).degree v - geometricBatchTarget j| < 2 * t := by
  obtain ⟨a, ha⟩ := F.exists_label_partition_target
    (fun j : Fin m => geometricBatchProbability C j)
    (fun j => (geometricBatchProbability_pos hC j).le)
    (geometricBatchProbability_sum_le_one hC hbudget m) hb hcap ht hdegree
    (by simpa only [Fintype.card_fin] using hsmall)
  refine ⟨a, fun v hv j => ?_⟩
  simpa only [geometricBatchProbability_mul hC.ne'] using ha v hv j

end FiniteEdgeFamily

end

end Erdos4b.FGKMT
