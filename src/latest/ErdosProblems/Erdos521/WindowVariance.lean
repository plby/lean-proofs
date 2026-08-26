/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Variance bounds for the low and high coefficients omitted by a window.
Formal proof: Codex.
-/
import ErdosProblems.Erdos521.WindowSums
import ErdosProblems.Erdos521.LocalVariance

namespace Erdos521

open scoped BigOperators

theorem range_sdiff_Ico {L U N : ℕ} (hLU : L ≤ U) (hUN : U ≤ N) :
    Finset.range N \ Finset.Ico L U = Finset.range L ∪ Finset.Ico U N := by
  ext k
  simp only [Finset.mem_sdiff, Finset.mem_range, Finset.mem_Ico, Finset.mem_union]
  omega

theorem omitted_geometricVariance (x : ℝ) {L U N : ℕ} (hLU : L ≤ U) (hUN : U ≤ N) :
    (∑ k ∈ Finset.range N \ Finset.Ico L U, x ^ (2 * k)) =
      geometricVariance x L + x ^ (2 * U) * geometricVariance x (N - U) := by
  have hdis : Disjoint (Finset.range L) (Finset.Ico U N) := by
    apply Finset.disjoint_left.mpr
    intro k hk hk'
    simp only [Finset.mem_range, Finset.mem_Ico] at hk hk'
    omega
  rw [range_sdiff_Ico hLU hUN, Finset.sum_union hdis]
  congr 1
  have h := sum_tail_square x 1 U N
  simpa only [one_mul, ← pow_mul, Nat.mul_comm] using h

theorem omitted_geometricVariance_le {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1)
    {L U N : ℕ} (hLU : L ≤ U) (hUN : U ≤ N) :
    (∑ k ∈ Finset.range N \ Finset.Ico L U, x ^ (2 * k)) ≤
      (L : ℝ) + x ^ (2 * U) / (1 - x) := by
  rw [omitted_geometricVariance x hLU hUN]
  apply add_le_add (geometricVariance_le_count hx hx₁.le L)
  simpa only [mul_one_div] using mul_le_mul_of_nonneg_left
    (geometricVariance_le_one_div hx hx₁ (N - U)) (pow_nonneg hx _)

theorem omitted_geometricVariance_normalized {x : ℝ} (hx : 0 ≤ x) (hx₁ : x < 1)
    {L U N : ℕ} (hLU : L ≤ U) (hUN : U ≤ N) (htail : x ^ (2 * N) ≤ 1 / 2) :
    (∑ k ∈ Finset.range N \ Finset.Ico L U, x ^ (2 * k)) ≤
      4 * ((L : ℝ) * (1 - x) + x ^ (2 * U)) * geometricVariance x N := by
  have hd : 0 < 1 - x := sub_pos.mpr hx₁
  have hV := geometricVariance_lower hx₁ N htail
  have hV' : 1 / (1 - x) ≤ 4 * geometricVariance x N := by
    rw [inv_eq_one_div, div_le_iff₀ (by positivity : 0 < 4 * (1 - x))] at hV
    apply (div_le_iff₀ hd).mpr
    nlinarith
  have hnonneg : 0 ≤ (L : ℝ) * (1 - x) + x ^ (2 * U) := by positivity
  calc
    _ ≤ (L : ℝ) + x ^ (2 * U) / (1 - x) := omitted_geometricVariance_le hx hx₁ hLU hUN
    _ = ((L : ℝ) * (1 - x) + x ^ (2 * U)) * (1 / (1 - x)) := by field_simp
    _ ≤ ((L : ℝ) * (1 - x) + x ^ (2 * U)) * (4 * geometricVariance x N) :=
      mul_le_mul_of_nonneg_left hV' hnonneg
    _ = _ := by ring

end Erdos521
