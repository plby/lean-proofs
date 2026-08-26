import ErdosProblems.Erdos76.LPDuality

/-!
# Finite packing duality with a cap on each packing variable

This general LP lemma is useful when smoothing arbitrary fractional graph
packings for the standalone Haxell–Rödl theorem.
-/

open Finset
open scoped BigOperators Matrix

namespace Erdos76.CappedLP

variable {I J : Type*} [Fintype I] [Fintype J] [DecidableEq I] [DecidableEq J]

theorem exists_capped_primal_dual (A : Matrix I J ℝ) (hA : ∀ i j, 0 ≤ A i j)
    (μ : ℝ) (hμ : 0 < μ) :
    ∃ w : J → ℝ, ∃ z : I → ℝ, ∃ r : J → ℝ,
      (∀ j, 0 ≤ w j ∧ w j ≤ μ) ∧ (∀ i, (A *ᵥ w) i ≤ 1) ∧
      (∀ i, 0 ≤ z i) ∧ (∀ j, 0 ≤ r j) ∧
      (∀ j, 1 ≤ (z ᵥ* A) j + r j) ∧
      (∑ j, w j) = (∑ i, z i) + μ * ∑ j, r j := by
  classical
  cases isEmpty_or_nonempty J with
  | inl h =>
    refine ⟨fun _ ↦ 0, fun _ ↦ 0, fun _ ↦ 0, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · exact fun j ↦ isEmptyElim j
    · simp [Matrix.mulVec, dotProduct]
    · simp
    · simp
    · exact fun j ↦ isEmptyElim j
    · simp
  | inr h =>
    let C : Matrix (I ⊕ J) J ℝ := fun e j ↦ match e with
      | Sum.inl i => μ * A i j
      | Sum.inr k => if k = j then 1 else 0
    obtain ⟨x, y, hx, hload, hy, hcover, hxy⟩ :=
      LPDuality.matrix_fractional_matching_cover_of_column_pos C
        (by
          intro e j
          cases e with
          | inl i => exact mul_nonneg hμ.le (hA i j)
          | inr k => simp only [C]; split_ifs <;> norm_num)
        (fun j ↦ ⟨Sum.inr j, by simp [C]⟩)
    let w : J → ℝ := fun j ↦ μ * x j
    let z : I → ℝ := fun i ↦ μ * y (Sum.inl i)
    let r : J → ℝ := fun j ↦ y (Sum.inr j)
    have hcap : ∀ j, x j ≤ 1 := by
      intro j
      simpa [C, Matrix.mulVec, dotProduct, ite_mul] using hload (Sum.inr j)
    have hedge : ∀ i, (A *ᵥ w) i = (C *ᵥ x) (Sum.inl i) := by
      intro i
      simp only [Matrix.mulVec, dotProduct, C, w]
      apply sum_congr rfl
      intro j _
      ring
    have hcov : ∀ j, (y ᵥ* C) j = (z ᵥ* A) j + r j := by
      intro j
      simp only [Matrix.vecMul, dotProduct, Fintype.sum_sum_type, C, z, r]
      simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, if_true]
      congr 1
      apply sum_congr rfl
      intro i _
      ring
    refine ⟨w, z, r, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · intro j
      exact ⟨mul_nonneg hμ.le (hx j), by simpa [w] using mul_le_mul_of_nonneg_left (hcap j) hμ.le⟩
    · intro i
      exact (hedge i).trans_le (hload (Sum.inl i))
    · intro i; exact mul_nonneg hμ.le (hy (Sum.inl i))
    · intro j; exact hy (Sum.inr j)
    · intro j; exact (hcover j).trans_eq (hcov j)
    · simp only [w, z, r, ← mul_sum]
      rw [hxy, Fintype.sum_sum_type, mul_add]

end Erdos76.CappedLP
