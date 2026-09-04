import Util.Bernays.GenusSeriesNonzero
import Util.Bernays.GoodLocalCounting
import Util.Bernays.LogCountBound

/-!
# Counting bounds for all genus twists
-/

open Filter Topology
open scoped Classical

namespace Bernays

theorem goodLocalValues_card_le {d b : ℤ} (hD : b ^ 2 + 4 * d ≠ 0) (N : ℕ) :
    (goodLocalValues d b hD N).card ≤ N := by
  have hsub : goodLocalValues d b hD N ⊆ Finset.Icc 1 N :=
    (Finset.filter_subset _ _).trans (Finset.filter_subset _ _)
  simpa using Finset.card_le_card hsub

theorem genusLocalAF_norm_le_one {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ n : ℕ, ‖genusLocalAF hD ψ n‖ ≤ 1 := by
  let := quadraticOrderIsDomain hD
  intro ψ n
  rw [genusLocalAF_norm]
  split_ifs <;> norm_num

theorem genusLocalAF_sum {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, genusLocalAF hD ψ n) =
      ∑ n ∈ goodLocalValues d b hD.ne N, ψ (Additive.ofMul (genusValue hD n)) := by
  let := quadraticOrderIsDomain hD
  intro ψ N
  rw [goodLocalValues, localValues, Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  simp only [genusLocalAF_apply, hn₀, true_and]

theorem genusLocalAF_sum_norm {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, (∑ n ∈ Finset.Icc 1 N, ‖genusLocalAF hD ψ n‖) =
      ((goodLocalValues d b hD.ne N).card : ℝ) := by
  let := quadraticOrderIsDomain hD
  intro ψ N
  have hcard : ((goodLocalValues d b hD.ne N).card : ℝ) =
      ∑ _n ∈ goodLocalValues d b hD.ne N, (1 : ℝ) := by simp
  rw [hcard]
  rw [goodLocalValues, localValues, Finset.filter_filter, Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  have hn₀ : 0 < n := (Finset.mem_Icc.mp hn).1
  simp only [genusLocalAF_norm, hn₀, true_and]

theorem cumsum_le_sum_Icc {a : ℕ → ℝ} (ha₀ : a 0 = 0) (ha : ∀ n : ℕ, 0 ≤ a n) (N : ℕ) :
    cumsum a N ≤ ∑ n ∈ Finset.Icc 1 N, a n := by
  have hsub : Finset.range N ⊆ insert 0 (Finset.Icc 1 N) := by
    intro n hn
    by_cases hz : n = 0
    · simp only [hz, Finset.mem_insert, true_or]
    · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_Icc.mpr
        ⟨Nat.one_le_iff_ne_zero.mpr hz, (Finset.mem_range.mp hn).le⟩))
  have h := Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => ha n)
  simpa only [cumsum, Finset.sum_insert (by simp : 0 ∉ Finset.Icc 1 N), ha₀, zero_add] using h

theorem genusLocalAF_cheby {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
      cheby (genusLocalAF hD ψ) := by
  let := quadraticOrderIsDomain hD
  intro ψ
  refine ⟨1, fun N => ?_⟩
  have h := Finset.sum_le_sum (s := Finset.range N) (fun n _ => genusLocalAF_norm_le_one hD ψ n)
  simpa only [cumsum, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, one_mul] using h

theorem genusLocalAF_logCountBound {d b : ℤ} (hD : b ^ 2 + 4 * d < 0) :
    letI := quadraticOrderIsDomain hD
    ∃ C : ℝ, 0 < C ∧ ∀ ψ : AddChar (Additive (GenusGroup (QuadraticAlgebra ℤ d b))) ℂ,
    ∀ N : ℕ, cumsum (fun n => ‖genusLocalAF hD ψ n‖) N ≤
      C * N / (1 + Real.sqrt (Real.log (N : ℝ))) := by
  let := quadraticOrderIsDomain hD
  obtain ⟨C, hC, hbound⟩ := exists_logCountBound_of_limit
    (fun N => Nat.cast_nonneg (goodLocalValues d b hD.ne N).card)
    (fun N => by exact_mod_cast goodLocalValues_card_le hD.ne N)
    (goodLocalConstant_pos hD).le (goodLocalValues_card_limit hD)
  refine ⟨C, hC, fun ψ N => ?_⟩
  have hsum := cumsum_le_sum_Icc (show ‖genusLocalAF hD ψ 0‖ = 0 by simp)
    (fun n => norm_nonneg (genusLocalAF hD ψ n)) N
  rw [genusLocalAF_sum_norm hD ψ N] at hsum
  exact hsum.trans (hbound N)

end Bernays
