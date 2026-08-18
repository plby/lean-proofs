/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos378.CentralCorrelation
import ErdosProblems.Erdos378.VaughanReciprocalFull

/-!
# One-dimensional central-range sums
-/

open scoped BigOperators ArithmeticFunction.vonMangoldt

namespace Erdos378
namespace CentralOneDimensional

open BoundedGaps.Maynard
open PrimeReciprocal
open AdaptiveShifts
open CentralCorrelation

noncomputable section

lemma central_frequency_upper_at_left
    {X : ℝ} {x y : ℕ} (hx : 1 ≤ x) (hyx : y ≤ 2 * x)
    (hXhi : X ≤ (y : ℝ) ^ 16) :
    X ≤ centralFrequencyConstant * (x : ℝ) ^ 31 := by
  have hyR : (y : ℝ) ≤ 2 * x := by exact_mod_cast hyx
  have hpow : (y : ℝ) ^ 16 ≤ (2 * (x : ℝ)) ^ 16 :=
    pow_le_pow_left₀ (by positivity) hyR 16
  have hxone : (1 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpow : (x : ℝ) ^ 16 ≤ (x : ℝ) ^ 31 :=
    pow_le_pow_right₀ hxone (by omega)
  calc
    X ≤ (y : ℝ) ^ 16 := hXhi
    _ ≤ (2 * (x : ℝ)) ^ 16 := hpow
    _ = 2 ^ 16 * (x : ℝ) ^ 16 := by ring
    _ ≤ 8 ^ 16 * (x : ℝ) ^ 31 := by
      have hc : (2 : ℝ) ^ 16 ≤ 8 ^ 16 := by norm_num
      gcongr
    _ = centralFrequencyConstant * (x : ℝ) ^ 31 := by
      rfl

theorem norm_central_reciprocal_interval_partial_le
    {X : ℝ} (hX : 0 < X) {x y b : ℕ}
    (hx : 1 ≤ x) (hxy : x < y) (hby : b ≤ y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition x) :
    ‖reciprocalProductIntervalSum X 1 x b‖ ≤
      adaptiveCorrelationEnvelope x := by
  by_cases hxb : x < b
  · have hxSq : (x : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := by
      have hxyR : (x : ℝ) ≤ y := by exact_mod_cast hxy.le
      exact pow_le_pow_left₀ (by positivity) hxyR 2
    have hQlo : (x : ℝ) ^ 2 ≤ 16 * X := by
      calc
        (x : ℝ) ^ 2 ≤ (y : ℝ) ^ 2 := hxSq
        _ ≤ 4 * X := hXlo
        _ ≤ 16 * X := by nlinarith
    have hQhi := central_frequency_upper_at_left hx hyx hXhi
    have hbase := baseShift_predicate_of_frequency_upper hX.le hx hQhi hsize
    exact norm_reciprocalProductIntervalSum_le_adaptive
      hX hx hQlo hbase hxb le_rfl (hby.trans hyx)
  · have hba : b ≤ x := Nat.le_of_not_gt hxb
    unfold reciprocalProductIntervalSum
    rw [Finset.Ioc_eq_empty (by omega)]
    simpa using adaptiveCorrelationEnvelope_nonneg hx

lemma central_log_sum_by_parts_aux
    (z : ℕ → ℂ) (a n : ℕ) :
    (∑ i ∈ Finset.Ioc a (a + n + 1),
      ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
      ((Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
          (∑ i ∈ Finset.Ioc a (a + n + 1), z i) -
        ∑ j ∈ Finset.Ioc a (a + n),
          ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc a j, z i := by
  induction n with
  | zero =>
      have hsum :
          (∑ i ∈ Finset.Ioc a (a + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
              ((Real.log ((a + 1 : ℕ) : ℝ) : ℝ) : ℂ) * z (a + 1) := by
        rw [show a + 1 = a + 1 by rfl,
          Finset.sum_Ioc_succ_top (le_refl a)]
        simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
      have hpref : (∑ i ∈ Finset.Ioc a (a + 1), z i) = z (a + 1) := by
        rw [Finset.sum_Ioc_succ_top (le_refl a)]
        simp only [Finset.Ioc_self, Finset.sum_empty, zero_add]
      rw [hsum, hpref]
      simp only [Nat.add_zero, Finset.Ioc_self, Finset.sum_empty, sub_zero]
  | succ n ih =>
      have hab : a ≤ a + n + 1 := by omega
      have hcorr : a ≤ a + n := by omega
      have hpref :
          (∑ i ∈ Finset.Ioc a ((a + n + 1) + 1), z i) =
            (∑ i ∈ Finset.Ioc a (a + n + 1), z i) + z ((a + n + 1) + 1) :=
        Finset.sum_Ioc_succ_top hab z
      have hcorrSum :
          (∑ j ∈ Finset.Ioc a (a + n + 1),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) =
            (∑ j ∈ Finset.Ioc a (a + n),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) -
                Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a (a + n + 1), z i :=
        Finset.sum_Ioc_succ_top hcorr _
      rw [show a + (n + 1) + 1 = (a + n + 1) + 1 by omega]
      calc
        (∑ i ∈ Finset.Ioc a ((a + n + 1) + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) =
          (∑ i ∈ Finset.Ioc a (a + n + 1),
            ((Real.log (i : ℝ) : ℝ) : ℂ) * z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                z ((a + n + 1) + 1) :=
          Finset.sum_Ioc_succ_top hab _
        _ = (((Real.log ((a + n + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
              (∑ i ∈ Finset.Ioc a (a + n + 1), z i) -
            ∑ j ∈ Finset.Ioc a (a + n),
              ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
                ∑ i ∈ Finset.Ioc a j, z i) +
              ((Real.log (((a + n + 1) + 1 : ℕ) : ℝ) : ℝ) : ℂ) *
                z ((a + n + 1) + 1) := by rw [ih]
        _ = _ := by
          simp only [Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] at hpref hcorrSum ⊢
          rw [hpref, hcorrSum]
          push_cast
          ring

lemma central_sum_log_succ_sub_Ioc (a n : ℕ) :
    (∑ j ∈ Finset.Ioc a (a + n),
        (Real.log ((j : ℝ) + 1) - Real.log (j : ℝ))) =
      Real.log ((a + n + 1 : ℕ) : ℝ) -
        Real.log ((a + 1 : ℕ) : ℝ) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have ha : a ≤ a + n := by omega
      rw [show a + (n + 1) = (a + n) + 1 by omega,
        Finset.sum_Ioc_succ_top ha, ih]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

theorem norm_log_weighted_central_interval_le
    {X : ℝ} (hX : 0 < X) {x y : ℕ}
    (hx : 1 ≤ x) (hxy : x < y)
    (hXlo : ((y : ℝ) ^ 2) ≤ 4 * X)
    (hXhi : X ≤ (y : ℝ) ^ 16) (hyx : y ≤ 2 * x)
    (hsize : centralCorrelationSizeCondition x) :
    ‖∑ h ∈ Finset.Ioc x y,
        ((Real.log (h : ℝ) : ℝ) : ℂ) * reciprocalWeight X h‖ ≤
      2 * Real.log (y : ℝ) * adaptiveCorrelationEnvelope x := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, y = x + n + 1 :=
    ⟨y - x - 1, by omega⟩
  let z : ℕ → ℂ := fun h ↦ reciprocalWeight X h
  have hparts := central_log_sum_by_parts_aux z x n
  change ‖∑ h ∈ Finset.Ioc x y,
      ((Real.log (h : ℝ) : ℝ) : ℂ) * z h‖ ≤ _
  rw [show Finset.Ioc x y = Finset.Ioc x (x + n + 1) by rw [hn]]
  rw [hparts]
  let B := adaptiveCorrelationEnvelope x
  have hB : 0 ≤ B := adaptiveCorrelationEnvelope_nonneg hx
  have hfull : ‖∑ i ∈ Finset.Ioc x (x + n + 1), z i‖ ≤ B := by
    simpa only [reciprocalProductIntervalSum, one_mul, z, hn] using
      norm_central_reciprocal_interval_partial_le hX hx hxy
        (show x + n + 1 ≤ y by rw [hn]) hXlo hXhi hyx hsize
  have hprefix (j : ℕ) (hj : j ∈ Finset.Ioc x (x + n)) :
      ‖∑ i ∈ Finset.Ioc x j, z i‖ ≤ B := by
    have hjy : j ≤ y := by
      have hjtop := (Finset.mem_Ioc.mp hj).2
      omega
    simpa only [reciprocalProductIntervalSum, one_mul, z] using
      norm_central_reciprocal_interval_partial_le hX hx hxy hjy
        hXlo hXhi hyx hsize
  have hlogY0 : 0 ≤ Real.log (y : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (hx.trans hxy.le))
  have hlogb : Real.log (x + n + 1 : ℕ) = Real.log (y : ℝ) := by rw [hn]
  have hdiff0 (j : ℕ) (hj : j ∈ Finset.Ioc x (x + n)) :
      0 ≤ Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) := by
    have hjpos : 0 < j := (show 0 < x from Nat.zero_lt_of_lt hx).trans
      (Finset.mem_Ioc.mp hj).1
    exact sub_nonneg.mpr (Real.log_le_log (by exact_mod_cast hjpos) (by
      exact_mod_cast (Nat.le_add_right j 1)))
  have hcorrection :
      ‖∑ j ∈ Finset.Ioc x (x + n),
          ((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc x j, z i‖ ≤
        (Real.log (x + n + 1 : ℕ) - Real.log (x + 1 : ℕ)) * B := by
    calc
      _ ≤ ∑ j ∈ Finset.Ioc x (x + n),
          ‖((Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ) : ℝ) : ℂ) *
            ∑ i ∈ Finset.Ioc x j, z i‖ := norm_sum_le _ _
      _ ≤ ∑ j ∈ Finset.Ioc x (x + n),
          (Real.log ((j + 1 : ℕ) : ℝ) - Real.log (j : ℝ)) * B := by
        apply Finset.sum_le_sum
        intro j hj
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
          abs_of_nonneg (hdiff0 j hj)]
        exact mul_le_mul_of_nonneg_left (hprefix j hj) (hdiff0 j hj)
      _ = (Real.log (x + n + 1 : ℕ) - Real.log (x + 1 : ℕ)) * B := by
        rw [← Finset.sum_mul]
        congr 1
        simpa only [Nat.cast_add, Nat.cast_one] using
          central_sum_log_succ_sub_Ioc x n
  have hsub : Real.log (x + n + 1 : ℕ) - Real.log (x + 1 : ℕ) ≤
      Real.log (y : ℝ) := by
    have hloga : 0 ≤ Real.log (x + 1 : ℕ) :=
      Real.log_nonneg (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le x))
    rw [hlogb]
    linarith
  refine (norm_sub_le _ _).trans ?_
  calc
    _ ≤ Real.log (x + n + 1 : ℕ) * B +
        (Real.log (x + n + 1 : ℕ) - Real.log (x + 1 : ℕ)) * B := by
      apply add_le_add
      · rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg]
        · exact mul_le_mul_of_nonneg_left hfull (by rw [hlogb]; exact hlogY0)
        · rw [hlogb]; exact hlogY0
      · exact hcorrection
    _ ≤ Real.log (y : ℝ) * B + Real.log (y : ℝ) * B := by
      exact add_le_add
        (mul_le_mul_of_nonneg_right hlogb.le hB)
        (mul_le_mul_of_nonneg_right hsub hB)
    _ = 2 * Real.log (y : ℝ) * B := by ring

end

end CentralOneDimensional
end Erdos378
