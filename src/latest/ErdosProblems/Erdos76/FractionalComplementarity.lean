import ErdosProblems.Erdos76.LPDuality

/-!
# Complementary slackness and forced edges

This file proves the finite optimality facts used by the new fractional
triangle-packing argument. All equalities follow from weak duality.
-/

open Finset
open scoped BigOperators Matrix

namespace Erdos76.FractionalComplementarity

variable {I J : Type*} [Fintype I] [Fintype J]

lemma matrix_gap_identity (A : Matrix I J ℝ) (x : J → ℝ) (y : I → ℝ) :
    (∑ i, y i) - ∑ j, x j =
      (∑ i, y i * (1 - (A *ᵥ x) i)) +
      ∑ j, x j * ((y ᵥ* A) j - 1) := by
  classical
  have hswap : (∑ i, y i * (A *ᵥ x) i) = ∑ j, x j * (y ᵥ* A) j := by
    simp only [Matrix.mulVec, Matrix.vecMul, dotProduct, mul_sum]
    rw [sum_comm]
    apply sum_congr rfl
    intro j _
    apply sum_congr rfl
    intro i _
    ring
  simp only [mul_sub, mul_one, sum_sub_distrib, hswap]
  ring

theorem matrix_complementary_slackness (A : Matrix I J ℝ) (x : J → ℝ) (y : I → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hload : ∀ i, (A *ᵥ x) i ≤ 1)
    (hy : ∀ i, 0 ≤ y i) (hcover : ∀ j, 1 ≤ (y ᵥ* A) j)
    (heq : ∑ j, x j = ∑ i, y i) :
    (∀ i, 0 < y i → (A *ᵥ x) i = 1) ∧
      ∀ j, 0 < x j → (y ᵥ* A) j = 1 := by
  classical
  have hp : ∀ i, 0 ≤ y i * (1 - (A *ᵥ x) i) :=
    fun i ↦ mul_nonneg (hy i) (sub_nonneg.mpr (hload i))
  have hq : ∀ j, 0 ≤ x j * ((y ᵥ* A) j - 1) :=
    fun j ↦ mul_nonneg (hx j) (sub_nonneg.mpr (hcover j))
  have hgap := matrix_gap_identity A x y
  rw [heq, sub_self] at hgap
  have hps : (∑ i, y i * (1 - (A *ᵥ x) i)) = 0 := by
    have := sum_nonneg (fun i (_ : i ∈ (univ : Finset I)) ↦ hp i)
    have := sum_nonneg (fun j (_ : j ∈ (univ : Finset J)) ↦ hq j)
    linarith
  have hqs : (∑ j, x j * ((y ᵥ* A) j - 1)) = 0 := by linarith
  constructor
  · intro i hi
    have hz := (sum_eq_zero_iff_of_nonneg (fun i _ ↦ hp i)).mp hps i (mem_univ _)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hi.ne') |>.symm
  · intro j hj
    have hz := (sum_eq_zero_iff_of_nonneg (fun j _ ↦ hq j)).mp hqs j (mem_univ _)
    exact sub_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hj.ne')

variable [DecidableEq I]

attribute [local instance] Classical.propDecidable

lemma positive_forced_sum_le_three (S : Finset I) (hS : S.card = 3) (z : I → ℝ)
    (hz : ∀ i ∈ S, 0 ≤ z i) (htight : ∑ i ∈ S, z i = 1)
    (F : I → Prop) (hF : ∀ i ∈ S, F i → 1 ≤ z i) :
    (∑ i ∈ S, ((if 0 < z i then (1 : ℝ) else 0) + 2 * (if F i then 1 else 0))) ≤ 3 := by
  by_cases hex : ∃ i ∈ S, F i
  · obtain ⟨i, hi, hFi⟩ := hex
    have hzi := hF i hi hFi
    have hother : ∀ j ∈ S, j ≠ i → z j = 0 := by
      intro j hj hji
      have hpair : z i + z j ≤ ∑ k ∈ S, z k := by
        have hsub : ({i, j} : Finset I) ⊆ S := by
          intro k hk
          rcases mem_insert.mp hk with rfl | hk
          · exact hi
          · exact mem_singleton.mp hk ▸ hj
        have := sum_le_sum_of_subset_of_nonneg hsub (fun k hk _ ↦ hz k hk)
        simpa [Ne.symm hji] using this
      rw [htight] at hpair
      have := hz j hj
      linarith
    rw [sum_eq_single i]
    · have hpos : 0 < z i := by linarith
      norm_num [hpos, hFi]
    · intro j hj hji
      have hzj := hother j hj hji
      have hnF : ¬ F j := by intro hjF; have := hF j hj hjF; linarith
      simp [hzj, hnF]
    · exact fun h ↦ (h hi).elim
  · have hnF : ∀ i ∈ S, ¬F i := by simpa using hex
    calc
      _ ≤ ∑ i ∈ S, (1 : ℝ) := by
        apply sum_le_sum
        intro i hi
        simp only [hnF i hi, if_false, mul_zero, add_zero]
        split_ifs <;> norm_num
      _ = 3 := by simp [hS]

/-- For an optimal packing/cover pair, the number of positive cover entries
plus twice the number of prescribed entries at least one is bounded by three
times the packing weight. -/
theorem support_forced_bound (s : J → Finset I) (hs : ∀ j, (s j).card = 3)
    (x : J → ℝ) (y : I → ℝ)
    (hx : ∀ j, 0 ≤ x j) (hy : ∀ i, 0 ≤ y i)
    (hload : ∀ i, (∑ j, if i ∈ s j then x j else 0) ≤ 1)
    (hcover : ∀ j, 1 ≤ ∑ i ∈ s j, y i)
    (heq : ∑ j, x j = ∑ i, y i)
    (F : I → Prop) (hF : ∀ i, F i → 1 ≤ y i) :
    (∑ i, ((if 0 < y i then (1 : ℝ) else 0) + 2 * (if F i then 1 else 0))) ≤
      3 * ∑ j, x j := by
  let A : Matrix I J ℝ := fun i j ↦ if i ∈ s j then 1 else 0
  have hAload : ∀ i, (A *ᵥ x) i = ∑ j, if i ∈ s j then x j else 0 := by
    intro i
    simp [A, Matrix.mulVec, dotProduct, ite_mul]
  have hAcover : ∀ j, (y ᵥ* A) j = ∑ i ∈ s j, y i := by
    intro j
    simp [A, Matrix.vecMul, dotProduct, mul_ite]
  obtain ⟨hsaturate, htight⟩ := matrix_complementary_slackness A x y hx
    (fun i ↦ (hAload i).trans_le (hload i)) hy
    (fun j ↦ (hcover j).trans_eq (hAcover j).symm) heq
  let a : I → ℝ := fun i ↦ (if 0 < y i then 1 else 0) + 2 * (if F i then 1 else 0)
  have haload : ∀ i, a i * (∑ j, if i ∈ s j then x j else 0) = a i := by
    intro i
    by_cases hi : 0 < y i
    · rw [← hAload, hsaturate i hi, mul_one]
    · have hnF : ¬ F i := fun h ↦ hi (lt_of_lt_of_le (by norm_num) (hF i h))
      simp [a, hi, hnF]
  have hcolumn : ∀ j, x j * (∑ i ∈ s j, a i) ≤ 3 * x j := by
    intro j
    by_cases hj : x j = 0
    · simp [hj]
    · have ht : ∑ i ∈ s j, y i = 1 :=
        (hAcover j).symm.trans (htight j (lt_of_le_of_ne (hx j) (Ne.symm hj)))
      have hb := positive_forced_sum_le_three (s j) (hs j) y
        (fun i _ ↦ hy i) ht F (fun i _ h ↦ hF i h)
      exact (mul_le_mul_of_nonneg_left hb (hx j)).trans_eq (mul_comm _ _)
  calc
    (∑ i, a i) = ∑ i, a i * (∑ j, if i ∈ s j then x j else 0) :=
      sum_congr rfl (fun i _ ↦ (haload i).symm)
    _ = ∑ j, x j * (∑ i ∈ s j, a i) := by
      simp only [mul_sum, mul_ite, mul_zero]
      rw [sum_comm]
      apply sum_congr rfl
      intro j _
      simp only [mul_comm (a _) (x j)]
      simp
    _ ≤ ∑ j, 3 * x j := sum_le_sum (fun j _ ↦ hcolumn j)
    _ = 3 * ∑ j, x j := (mul_sum _ _ _).symm

end Erdos76.FractionalComplementarity
