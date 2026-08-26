import ErdosProblems.Erdos421.MeanSquare
import Mathlib.Analysis.InnerProductSpace.Basic

/-! # The Hilbert-space inequality behind the Halász method -/

namespace Erdos421

open Complex
open scoped ComplexConjugate

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

theorem gram_row_weighted_norm_bound (S : Finset ℕ) (v : ℕ → E) (c : ℕ → ℂ)
    {R : ℝ} (hrow : ∀ i ∈ S, (∑ j ∈ S, ‖inner ℂ (v i) (v j)‖) ≤ R) :
    ‖∑ i ∈ S, c i • v i‖ ^ 2 ≤ R * (∑ i ∈ S, ‖c i‖ ^ 2) := by
  let w := ∑ i ∈ S, c i • v i
  have hinner : inner ℂ w w =
      ∑ i ∈ S, ∑ j ∈ S, conj (c i) * (c j * inner ℂ (v i) (v j)) := by
    dsimp only [w]
    rw [sum_inner]
    apply Finset.sum_congr rfl
    intro i _
    rw [inner_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [inner_smul_left, inner_smul_right]
  have hnorm : ‖w‖ ^ 2 ≤
      ∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * ‖inner ℂ (v i) (v j)‖ := by
    calc
      ‖w‖ ^ 2 = (inner ℂ w w).re := (inner_self_eq_norm_sq (𝕜 := ℂ) w).symm
      _ ≤ ‖inner ℂ w w‖ := Complex.re_le_norm _
      _ ≤ ∑ i ∈ S, ∑ j ∈ S, ‖conj (c i) * (c j * inner ℂ (v i) (v j))‖ := by
        rw [hinner]
        exact (norm_sum_le _ _).trans (Finset.sum_le_sum (fun i _ ↦ norm_sum_le _ _))
      _ = _ := by simp only [norm_mul, Complex.norm_conj, mul_assoc]
  have hs : ∀ i j, ‖inner ℂ (v i) (v j)‖ = ‖inner ℂ (v j) (v i)‖ := by
    intro i j
    rw [← inner_conj_symm]
    exact Complex.norm_conj _
  have hschur := symmetric_weighted_sum_le S (fun i ↦ ‖c i‖)
    (fun i j ↦ ‖inner ℂ (v i) (v j)‖) (fun _ _ ↦ norm_nonneg _) hs hrow
  have htwice : (∑ i ∈ S, ∑ j ∈ S, 2 * ‖c i‖ * ‖c j‖ * ‖inner ℂ (v i) (v j)‖) =
      2 * (∑ i ∈ S, ∑ j ∈ S, ‖c i‖ * ‖c j‖ * ‖inner ℂ (v i) (v j)‖) := by
    simp only [Finset.mul_sum, mul_assoc]
  rw [htwice] at hschur
  change ‖w‖ ^ 2 ≤ _
  linarith

/-- The finite Hilbert-space large-value inequality, with an explicit Gram-row bound. -/
theorem hilbert_large_values_bound (S : Finset ℕ) (v : ℕ → E) (u : E)
    {R : ℝ} (hR : 0 ≤ R)
    (hrow : ∀ i ∈ S, (∑ j ∈ S, ‖inner ℂ (v i) (v j)‖) ≤ R) :
    (∑ i ∈ S, ‖inner ℂ (v i) u‖ ^ 2) ≤ R * ‖u‖ ^ 2 := by
  let c : ℕ → ℂ := fun i ↦ inner ℂ (v i) u
  let Q : ℝ := ∑ i ∈ S, ‖c i‖ ^ 2
  let w := ∑ i ∈ S, c i • v i
  have hQ : 0 ≤ Q := Finset.sum_nonneg (fun i _ ↦ sq_nonneg _)
  have hwu : inner ℂ w u = (Q : ℂ) := by
    simp only [w, Q, sum_inner, inner_smul_left]
    rw [Complex.ofReal_sum]
    apply Finset.sum_congr rfl
    intro i _
    change conj (c i) * c i = ((‖c i‖ ^ 2 : ℝ) : ℂ)
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcs : Q ≤ ‖w‖ * ‖u‖ := by
    have h := norm_inner_le_norm (𝕜 := ℂ) w u
    rwa [hwu, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hQ] at h
  have hgram : ‖w‖ ^ 2 ≤ R * Q := gram_row_weighted_norm_bound S v c hrow
  have hcs2 : Q ^ 2 ≤ ‖w‖ ^ 2 * ‖u‖ ^ 2 := by
    nlinarith [norm_nonneg w, norm_nonneg u]
  have hmul := mul_le_mul_of_nonneg_right hgram (sq_nonneg ‖u‖)
  change Q ≤ _
  by_cases hzero : Q = 0
  · rw [hzero]
    exact mul_nonneg hR (sq_nonneg _)
  · have hpos : 0 < Q := lt_of_le_of_ne hQ (Ne.symm hzero)
    nlinarith

end Erdos421
