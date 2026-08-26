/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Measurable sign counts associated with a finite coefficient window.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowSums
import ErdosProblems.Erdos521.SignGridExpectation

namespace Erdos521

open MeasureTheory
open scoped BigOperators

noncomputable def windowGridSignChanges (ε : ℕ → ℝ) (W : Finset ℕ) (g : ℕ → ℝ) (N : ℕ) : ℕ :=
  ∑ i ∈ Finset.range N, signChange (windowPowerSum ε W (g i)) (windowPowerSum ε W (g (i + 1)))

theorem measurable_signChange : Measurable (fun p : ℝ × ℝ ↦ signChange p.1 p.2) := by
  exact Measurable.ite (measurableSet_lt (measurable_fst.mul measurable_snd) measurable_const)
    measurable_const measurable_const

theorem measurable_windowGridSignChanges (W : Finset ℕ) (g : ℕ → ℝ) (N : ℕ) :
    Measurable (fun ε ↦ windowGridSignChanges ε W g N) := by
  unfold windowGridSignChanges
  apply Finset.measurable_sum
  intro i _
  exact measurable_signChange.comp ((measurable_windowPowerSum W (g i)).prodMk
    (measurable_windowPowerSum W (g (i + 1))))

theorem windowGridSignChanges_le (ε : ℕ → ℝ) (W : Finset ℕ) (g : ℕ → ℝ) (N : ℕ) :
    windowGridSignChanges ε W g N ≤ N := by
  unfold windowGridSignChanges
  calc
    _ ≤ ∑ _i ∈ Finset.range N, 1 := Finset.sum_le_sum (fun _ _ ↦ signChange_le_one _ _)
    _ = N := by simp

theorem signChange_pos_mul {c d : ℝ} (hc : 0 < c) (hd : 0 < d) (u v : ℝ) :
    signChange (c * u) (d * v) = signChange u v := by
  unfold signChange
  rw [mul_mul_mul_comm]
  have heq : c * d * (u * v) < 0 ↔ u * v < 0 := by
    constructor
    · intro h
      rcases mul_neg_iff.mp h with ⟨_, hneg⟩ | ⟨hneg, _⟩
      · exact hneg
      · exact False.elim ((not_lt_of_ge (mul_pos hc hd).le) hneg)
    · exact mul_neg_of_pos_of_neg (mul_pos hc hd)
  simp only [heq]

theorem windowGridSignChanges_Ico (ε : ℕ → ℝ) {L U : ℕ} (hLU : L < U)
    (g : ℕ → ℝ) (hg : ∀ i, 0 < g i) (N : ℕ) :
    windowGridSignChanges ε (Finset.Ico L U) g N =
      gridSignChanges (fun k ↦ ε (L + k)) (U - L - 1) g N := by
  unfold windowGridSignChanges gridSignChanges
  apply Finset.sum_congr rfl
  intro i _
  simp only [windowPowerSum_Ico, polynomial_eval]
  rw [signChange_pos_mul (pow_pos (hg i) L) (pow_pos (hg (i + 1)) L)]
  congr 2 <;> omega

end Erdos521
