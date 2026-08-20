import Mathlib.Tactic
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: PlanarRot90ClockwiseWedgeTauTrig]
lemma PlanarRot90ClockwiseWedgeTauTrig (β ν α : ℝ)
    (hαν : α ≠ β) (hνβ : ν ≠ β) :
    let τ : ℝ → ℝ :=
      fun x => if x = β then 2 * Real.pi
        else if x < β then β - x
        else β - x + 2 * Real.pi
    Real.sin (α - β) = -Real.sin (τ α) ∧
      Real.cos (α - β) = Real.cos (τ α) ∧
      Real.sin (α - ν) = Real.sin (τ ν - τ α) := by
-- BODY
  dsimp only
  let τ : ℝ → ℝ :=
    fun x => if x = β then 2 * Real.pi
      else if x < β then β - x
      else β - x + 2 * Real.pi
  have hsin : Real.sin (α - β) = -Real.sin (τ α) := by
    dsimp [τ]
    rw [if_neg hαν]
    by_cases hlt : α < β
    · simp [hlt]
      have h : α - β = -(β - α) := by ring
      rw [h, Real.sin_neg]
    · simp [hlt]
      have h : α - β = -(β - α) := by ring
      rw [h, Real.sin_neg]
  have hcos : Real.cos (α - β) = Real.cos (τ α) := by
    dsimp [τ]
    rw [if_neg hαν]
    by_cases hlt : α < β
    · simp [hlt]
      have h : α - β = -(β - α) := by ring
      rw [h, Real.cos_neg]
    · simp [hlt]
      have h : α - β = -(β - α) := by ring
      rw [h, Real.cos_neg]
  have hsin_sub : Real.sin (α - ν) = Real.sin (τ ν - τ α) := by
    dsimp [τ]
    rw [if_neg hνβ, if_neg hαν]
    by_cases hnlt : ν < β
    · by_cases halt : α < β
      · simp [hnlt, halt]
      · simp [hnlt, halt]
        have h :
            β - ν - (β - α + 2 * Real.pi) = α - ν - 2 * Real.pi := by ring
        rw [h, Real.sin_sub_two_pi]
    · by_cases halt : α < β
      · simp [hnlt, halt]
        have h :
            β - ν + 2 * Real.pi - (β - α) = α - ν + 2 * Real.pi := by ring
        rw [h, Real.sin_add_two_pi]
      · simp [hnlt, halt]
  exact ⟨hsin, hcos, hsin_sub⟩
