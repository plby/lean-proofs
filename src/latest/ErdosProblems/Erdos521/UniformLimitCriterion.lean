/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Uniform bounds from convergence along every admissible sequence.
Formal proof: Codex.
-/
import Mathlib.Analysis.SpecialFunctions.Log.Basic

namespace Erdos521

open Filter
open scoped Topology

theorem uniform_limit_of_admissible_sequences (F : ℕ → ℝ → ℝ) (P : ℕ → ℝ → Prop) (c : ℝ)
    (hseq : ∀ (n : ℕ → ℕ) (s : ℕ → ℝ), Tendsto n atTop atTop → Tendsto s atTop atTop →
      (∀ j, P (n j) (s j)) → Tendsto (fun j ↦ F (n j) (s j)) atTop (𝓝 c)) :
    ∀ η : ℝ, 0 < η → ∃ M : ℕ, 2 ≤ M ∧ ∀ n : ℕ, M ≤ n → ∀ s : ℝ, (M : ℝ) ≤ s →
      P n s → |F n s - c| < η := by
  classical
  intro η hη
  by_contra h
  push Not at h
  have hbad (j : ℕ) : ∃ n : ℕ, j + 2 ≤ n ∧ ∃ s : ℝ, ((j + 2 : ℕ) : ℝ) ≤ s ∧
      P n s ∧ η ≤ |F n s - c| := h (j + 2) (by omega)
  choose n hn s hs hP herror using hbad
  have hnlim : Tendsto n atTop atTop := tendsto_atTop_mono hn (tendsto_add_atTop_nat 2)
  have hslim : Tendsto s atTop atTop := tendsto_atTop_mono hs
    ((tendsto_natCast_atTop_atTop (R := ℝ)).comp (tendsto_add_atTop_nat 2))
  have hlim := ((hseq n s hnlim hslim hP).sub_const c).abs
  simp only [sub_self, abs_zero] at hlim
  obtain ⟨j, hj⟩ := (hlim.eventually (gt_mem_nhds hη)).exists
  exact (not_lt_of_ge (herror j)) hj

end Erdos521
