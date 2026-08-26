/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A quantitative maximal root-count estimate on a real interval.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.LocalRootBounds
import ErdosProblems.Erdos521.CenterChanges
import ErdosProblems.Erdos521.SmallBall

namespace Erdos521

open MeasureTheory

theorem localRootCount_maximal_probability_split (n N k : ℕ) (x : ℝ) {r δ : ℝ}
    (hr : 0 < r) (hδ : 0 < δ) :
    sequenceLaw.real {ε | ∃ m, n ≤ m ∧ m ≤ N ∧ k ≤ localRootCount ε m x r} ≤
      sequenceLaw.real {ε | |powerSum ε (n + 1) x| ≤ 2 * δ} +
      x ^ (2 * (n + 1)) * geometricVariance x (N - n) / δ ^ 2 +
      2 * (geometricVariance (‖(x : ℂ)‖ + |4 * r|) (N + 1) *
        (1 + Real.log (N + 1))) / (δ ^ 2 * (4 : ℝ) ^ k) := by
  let E₁ := {ε : ℕ → ℝ | |powerSum ε (n + 1) x| ≤ 2 * δ}
  let E₂ := {ε : ℕ → ℝ | ∃ m, n ≤ m ∧ m ≤ N ∧
    δ ≤ |powerSum ε (m + 1) x - powerSum ε (n + 1) x|}
  let E₃ := {ε : ℕ → ℝ | ∃ m ≤ N, δ ≤ |powerSum ε (m + 1) x| ∧
    k ≤ localRootCount ε m x r}
  have hsub : {ε | ∃ m, n ≤ m ∧ m ≤ N ∧ k ≤ localRootCount ε m x r} ⊆
      (E₁ ∪ E₂) ∪ E₃ := by
    intro ε hε
    obtain ⟨m, hnm, hmN, hroot⟩ := hε
    by_cases hbase : |powerSum ε (n + 1) x| ≤ 2 * δ
    · exact Or.inl (Or.inl hbase)
    by_cases hdiff : δ ≤ |powerSum ε (m + 1) x - powerSum ε (n + 1) x|
    · exact Or.inl (Or.inr ⟨m, hnm, hmN, hdiff⟩)
    apply Or.inr
    refine ⟨m, hmN, ?_, hroot⟩
    have htriangle := abs_sub_abs_le_abs_sub (powerSum ε (n + 1) x) (powerSum ε (m + 1) x)
    rw [abs_sub_comm] at htriangle
    push Not at hbase hdiff
    linarith
  have hprob := (measureReal_mono (μ := sequenceLaw) hsub).trans
    (measureReal_union_le (μ := sequenceLaw) (E₁ ∪ E₂) E₃)
  have hsum := add_le_add (measureReal_union_le (μ := sequenceLaw) E₁ E₂)
    (le_refl (sequenceLaw.real E₃))
  apply (hprob.trans hsum).trans
  exact add_le_add
    (add_le_add (le_refl (sequenceLaw.real E₁)) (powerSum_changes_probability n N x hδ))
    (localRootCount_large_center_probability N k x hr hδ)

/-- All terms are explicit. No concentration or root-asymptotic theorem is
assumed in this local estimate. -/
theorem localRootCount_maximal_probability (n N k L : ℕ) (hL : 2 * L ≤ n + 1)
    {x r δ : ℝ} (hx₀ : 1 / 2 ≤ x) (hx₁ : x ≤ 1) (hr : 0 < r) (hδ : 0 < δ) :
    let c : ℝ := 1 / (4 * Real.pi ^ 2)
    sequenceLaw.real {ε | ∃ m, n ≤ m ∧ m ≤ N ∧ k ≤ localRootCount ε m x r} ≤
      Real.exp (1 / 2) *
        (Real.sqrt (Real.pi / (c * geometricVariance x (n + 1) / (2 * δ) ^ 2)) +
          Real.exp (-c * geometricVariance x (n + 1)) +
          2 * Real.exp (-((2 * δ) * (x ^ L)⁻¹) ^ 2 / 2)) +
      x ^ (2 * (n + 1)) * geometricVariance x (N - n) / δ ^ 2 +
      2 * (geometricVariance (x + 4 * r) (N + 1) *
        (1 + Real.log (N + 1))) / (δ ^ 2 * (4 : ℝ) ^ k) := by
  dsimp only
  have h := localRootCount_maximal_probability_split n N k x hr hδ
  have hx : 0 ≤ x := by linarith
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hx,
    abs_of_pos (by positivity : 0 < 4 * r)] at h
  apply h.trans
  exact add_le_add
    (add_le_add (powerSum_smallBall n L hL hx₀ hx₁ (by positivity : 0 < 2 * δ)) le_rfl) le_rfl

end Erdos521
