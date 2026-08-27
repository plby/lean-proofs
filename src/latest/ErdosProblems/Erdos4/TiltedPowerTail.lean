import ErdosProblems.Erdos4.FGKMTQuantitativeTail
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

/-! Uniform finite power tails, with constants independent of the upper endpoint. -/

open scoped BigOperators

namespace Erdos4.Tilted

theorem finite_three_halves_tail {W : ℕ} (hW : 0 < W) (S : Finset ℕ)
    (hS : ∀ n ∈ S, W < n) :
    (∑ n ∈ S, (n : ℝ) ^ (-(3 / 2 : ℝ))) ≤ 2 * (W : ℝ) ^ (-(1 / 2 : ℝ)) := by
  let N := max W (S.sup id)
  have hWN : W ≤ N := le_max_left _ _
  have hWpos : (0 : ℝ) < W := Nat.cast_pos.mpr hW
  have hsub : S ⊆ Finset.Ioc W N := by
    intro n hn
    exact Finset.mem_Ioc.mpr ⟨hS n hn, (Finset.le_sup (f := id) hn).trans (le_max_right _ _)⟩
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-(3 / 2 : ℝ))) (Set.Icc (W : ℝ) N) := by
    intro a ha b hb hab
    exact Real.rpow_le_rpow_of_nonpos (hWpos.trans_le ha.1) hab (by norm_num)
  have hsum : (∑ n ∈ Finset.Ioc W N, (n : ℝ) ^ (-(3 / 2 : ℝ))) =
      ∑ n ∈ Finset.Ico W N, ((n + 1 : ℕ) : ℝ) ^ (-(3 / 2 : ℝ)) := by
    rw [Finset.sum_Ico_add' (fun n : ℕ => (n : ℝ) ^ (-(3 / 2 : ℝ))) W N 1]
    congr 1
    ext n
    simp only [Finset.mem_Ico, Finset.mem_Ioc]
    omega
  have hzero : (0 : ℝ) ∉ Set.uIcc (W : ℝ) N := by
    rw [Set.uIcc_of_le (Nat.cast_le.mpr hWN)]
    intro h
    linarith [h.1]
  calc
    _ ≤ ∑ n ∈ Finset.Ioc W N, (n : ℝ) ^ (-(3 / 2 : ℝ)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsub (fun n _ _ => Real.rpow_nonneg (Nat.cast_nonneg n) _)
    _ ≤ ∫ x in (W : ℝ)..(N : ℝ), x ^ (-(3 / 2 : ℝ)) := by
      rw [hsum]
      exact hanti.sum_le_integral_Ico hWN
    _ = 2 * ((W : ℝ) ^ (-(1 / 2 : ℝ)) - (N : ℝ) ^ (-(1 / 2 : ℝ))) := by
      rw [integral_rpow (Or.inr ⟨by norm_num, hzero⟩)]
      norm_num
      ring
    _ ≤ _ := by linarith [Real.rpow_nonneg (Nat.cast_nonneg N) (-(1 / 2 : ℝ))]

end Erdos4.Tilted
