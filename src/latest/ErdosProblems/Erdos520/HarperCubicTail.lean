import ErdosProblems.Erdos520.HarperBlockSchedule
import Mathlib.Analysis.SumIntegralComparisons
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic

set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true

open Finset MeasureTheory Set
open scoped BigOperators

namespace Erdos
namespace Problem520

/-!
# Explicit tail control for the cubic prime errors

The logarithmic Taylor remainder at `p` is on the scale `p^(-3/2)`.
The lemmas here compare its finite tail with the elementary integral of
`x^(-3/2)`, giving a bound of order `A^(-1/2)` uniformly in the upper
endpoint.  This is deliberately proved over all integers, so no prime
number theorem is involved.
-/

theorem harperCubicScale_eq_rpow (n : ℕ) :
    (Real.sqrt (n : ℝ))⁻¹ ^ 3 = (n : ℝ) ^ (-(3 : ℝ) / 2) := by
  rw [← Real.rpow_neg_one, ← Real.rpow_natCast,
    ← Real.rpow_mul (Real.sqrt_nonneg (n : ℝ)), Real.sqrt_eq_rpow,
    ← Real.rpow_mul (Nat.cast_nonneg n)]
  norm_num

/-- Integral-test bound for a finite `n^(-3/2)` tail. -/
theorem sum_Ioc_harperCubicScale_le
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3) ≤
      2 * (A : ℝ) ^ (-(1 : ℝ) / 2) := by
  have hApos : (0 : ℝ) < A := by exact_mod_cast (Nat.zero_lt_of_lt hA)
  have hanti : AntitoneOn (fun x : ℝ ↦ x ^ (-(3 : ℝ) / 2))
      (Set.Icc (A : ℝ) (B : ℝ)) := by
    apply (Real.antitoneOn_rpow_Ioi_of_exponent_nonpos
      (by norm_num : (-(3 : ℝ) / 2) ≤ 0)).mono
    intro x hx
    exact hApos.trans_le hx.1
  have hsum := hanti.sum_le_integral_Ico hAB
  have hshift :
      (∑ n ∈ Finset.Ioc A B, (n : ℝ) ^ (-(3 : ℝ) / 2)) =
        ∑ n ∈ Finset.Ico A B,
          ((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) := by
    rw [← Finset.Ico_add_one_add_one_eq_Ioc]
    simpa only [Nat.cast_add, Nat.cast_one, add_comm] using!
      (Finset.sum_Ico_add
        (fun n : ℕ ↦ (n : ℝ) ^ (-(3 : ℝ) / 2)) A B 1).symm
  have hzero : (0 : ℝ) ∉ Set.uIcc (A : ℝ) (B : ℝ) := by
    rw [Set.uIcc_of_le (by exact_mod_cast hAB)]
    intro h
    have hle := (Set.mem_Icc.mp h).1
    linarith
  have hint :
      (∫ x in (A : ℝ)..(B : ℝ), x ^ (-(3 : ℝ) / 2)) =
        (((B : ℝ) ^ (-(1 : ℝ) / 2) -
            (A : ℝ) ^ (-(1 : ℝ) / 2)) /
          (-(1 : ℝ) / 2)) := by
    have hexp : -(3 : ℝ) / 2 + 1 = -(1 : ℝ) / 2 := by norm_num
    simpa only [hexp] using!
      (integral_rpow
        (a := (A : ℝ)) (b := (B : ℝ))
        (r := (-(3 : ℝ) / 2)) (Or.inr ⟨by norm_num, hzero⟩))
  calc
    (∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3) =
        ∑ n ∈ Finset.Ioc A B, (n : ℝ) ^ (-(3 : ℝ) / 2) := by
      apply Finset.sum_congr rfl
      intro n hn
      exact harperCubicScale_eq_rpow n
    _ = ∑ n ∈ Finset.Ico A B,
          ((n + 1 : ℕ) : ℝ) ^ (-(3 : ℝ) / 2) := hshift
    _ ≤ ∫ x in (A : ℝ)..(B : ℝ), x ^ (-(3 : ℝ) / 2) := hsum
    _ = 2 * ((A : ℝ) ^ (-(1 : ℝ) / 2) -
          (B : ℝ) ^ (-(1 : ℝ) / 2)) := by rw [hint]; ring
    _ ≤ 2 * (A : ℝ) ^ (-(1 : ℝ) / 2) := by
      have hBnonneg : 0 ≤ (B : ℝ) ^ (-(1 : ℝ) / 2) :=
        Real.rpow_nonneg (Nat.cast_nonneg B) _
      linarith

/-- Square-root form of the same tail bound. -/
theorem sum_Ioc_harperCubicScale_le_inv_sqrt
    {A B : ℕ} (hA : 1 ≤ A) (hAB : A ≤ B) :
    (∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3) ≤
      2 * (Real.sqrt (A : ℝ))⁻¹ := by
  calc
    (∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3) ≤
        2 * (A : ℝ) ^ (-(1 : ℝ) / 2) :=
      sum_Ioc_harperCubicScale_le hA hAB
    _ = 2 * (Real.sqrt (A : ℝ))⁻¹ := by
      congr 1
      rw [Real.sqrt_eq_rpow, ← Real.rpow_neg (Nat.cast_nonneg A)]
      congr 1
      ring

/-- The full cubic Taylor budget of one scheduled prime block decays
doubly exponentially with the block index. -/
theorem harperBlockCubicRemainder_scheduled_le (y j : ℕ) :
    harperBlockCubicRemainder y (harperScheduledPrimeBlock y j) ≤
      (4 / 3 : ℝ) * (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ := by
  let S := harperScheduledPrimeBlock y j
  let e : HarperPrimeIndex y ↪ ℕ := Function.Embedding.subtype _
  let A := harperBlockEndpoint j
  let B := harperBlockEndpoint (j + 1)
  have hsubset : S.map e ⊆ Finset.Ioc A B := by
    intro n hn
    rw [Finset.mem_map] at hn
    obtain ⟨p, hp, rfl⟩ := hn
    simpa only [Finset.mem_Ioc, e, A, B] using!
      (mem_harperScheduledPrimeBlock p).mp hp
  have hsum :
      (∑ n ∈ S.map e, (Real.sqrt (n : ℝ))⁻¹ ^ 3) ≤
        ∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
    apply Finset.sum_le_sum_of_subset_of_nonneg hsubset
    intro n hnB hnS
    positivity
  have hA : 1 ≤ A := Nat.one_le_iff_ne_zero.mpr
    (harperBlockEndpoint_pos j).ne'
  have hAB : A ≤ B := monotone_harperBlockEndpoint (by omega)
  have htail := sum_Ioc_harperCubicScale_le_inv_sqrt hA hAB
  unfold harperBlockCubicRemainder
  calc
    (∑ p ∈ S, (2 / 3 : ℝ) *
        (Real.sqrt (p.1 : ℝ))⁻¹ ^ 3) =
        ∑ n ∈ S.map e, (2 / 3 : ℝ) *
          (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
      rw [Finset.sum_map]
      rfl
    _ = (2 / 3 : ℝ) *
        ∑ n ∈ S.map e, (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
      rw [Finset.mul_sum]
    _ ≤ (2 / 3 : ℝ) *
        ∑ n ∈ Finset.Ioc A B, (Real.sqrt (n : ℝ))⁻¹ ^ 3 := by
      exact mul_le_mul_of_nonneg_left hsum (by norm_num)
    _ ≤ (2 / 3 : ℝ) *
        (2 * (Real.sqrt (A : ℝ))⁻¹) := by
      exact mul_le_mul_of_nonneg_left htail (by norm_num)
    _ = (4 / 3 : ℝ) *
        (Real.sqrt (harperBlockEndpoint j : ℝ))⁻¹ := by
      dsimp [A]
      ring

end Problem520
end Erdos
