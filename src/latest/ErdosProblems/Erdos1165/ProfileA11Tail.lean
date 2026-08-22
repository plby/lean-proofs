/-
Copyright (c) 2026 The Erdos Problems Formalization Project.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Erdos Problems Formalization Project
-/
import ErdosProblems.Erdos1165.ProfileA11Assembly

/-!
# Shifted finite form of HLOZ (A.11)

The Taylor window used in (A.11) need not hold at the finitely many smallest
scales.  This file proves the same pathwise comparison on `Ico start n`.
Thus a fixed initial profile segment can be retained exactly, while all
asymptotic estimates begin at a sufficiently large deterministic scale.
-/

open scoped BigOperators

namespace Erdos1165.ProfileA11Tail

noncomputable section

open AppendixFirstMoment ProfileSmallBall ProfileTaylor ProfileA11Assembly

/-- Gaussian normalizer restricted to the scale interval `[start,n)`. -/
def gaussianNormalizerLogSumFrom (start n : ℕ) : ℝ :=
  ∑ l ∈ Finset.Ico start n,
    Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2

/-- Centered Gaussian energy restricted to `[start,n)`. -/
def gaussianEnergyFrom (start n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico start n,
    (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2)

/-- Parabolic increment energy restricted to `[start,n)`. -/
def parabolicEnergyFrom (start n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico start n,
    ((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
      (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2)

/-- Reference energy on `[start,n)`: two per edge plus Gaussian energy. -/
def parabolicReferenceEnergyFrom (start n : ℕ) (Delta : ℕ → ℝ) : ℝ :=
  ∑ l ∈ Finset.Ico start n,
    (2 + (Delta (l + 1) - Delta l) ^ 2 / (8 * (l : ℝ) ^ 2))

lemma parabolicReferenceEnergyFrom_eq {start n : ℕ} (hstartn : start ≤ n)
    (Delta : ℕ → ℝ) :
    parabolicReferenceEnergyFrom start n Delta =
      2 * (n - start) + gaussianEnergyFrom start n Delta := by
  unfold parabolicReferenceEnergyFrom gaussianEnergyFrom
  rw [Finset.sum_add_distrib]
  simp [Nat.card_Ico, hstartn]
  ring

/-- The decreasing-power sum over a tail is bounded by the already checked
sum from scale two. -/
lemma sum_Ico_rpow_sub_one_le_from {start n : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n) {q : ℝ}
    (hq : 0 < q) (hq1 : q ≤ 1) :
    (∑ l ∈ Finset.Ico start n, (l : ℝ) ^ (q - 1)) ≤
      (n : ℝ) ^ q / q := by
  calc
    (∑ l ∈ Finset.Ico start n, (l : ℝ) ^ (q - 1)) ≤
        ∑ l ∈ Finset.Ico 2 n, (l : ℝ) ^ (q - 1) := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · exact Finset.Ico_subset_Ico hstart le_rfl
      · intro l _hl _hnot
        positivity
    _ ≤ (n : ℝ) ^ q / q :=
      sum_rpow_sub_one_le hq hq1 n (hstart.trans hstartn)

/-- Taylor/Stirling comparison summed only over the tail `[start,n)`. -/
theorem abs_sum_edgeStirlingExponent_parabolic_le_from
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ) {delta A C : ℝ}
    (hdelta : 0 < delta) (hdeltaThird : delta ≤ 1 / 3)
    (hA : 0 ≤ A) (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico start n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico start n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico start n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico start n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    |∑ l ∈ Finset.Ico start n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2))| ≤
      parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
        (3 * delta) := by
  have hcoeff : 0 ≤ parabolicTaylorCoefficient A C := by
    unfold parabolicTaylorCoefficient
    positivity
  calc
    |∑ l ∈ Finset.Ico start n,
        (edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2))| ≤
      ∑ l ∈ Finset.Ico start n,
        |edgeStirlingExponent (m l) (m (l + 1)) +
          Real.log (8 * Real.pi * (l : ℝ) ^ 2) / 2 +
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ l ∈ Finset.Ico start n,
        parabolicTaylorCoefficient A C *
          (l : ℝ) ^ (3 * delta - 1) := by
      apply Finset.sum_le_sum
      intro l hl
      exact abs_edgeStirlingExponent_parabolic_le
        (hstart.trans (Finset.mem_Ico.mp hl).1) (hpos l hl)
        hdelta.le hA hC (hwindow l hl) (hbase l hl)
        (hclose l hl) (hmoderate l hl) (hinc l hl)
    _ = parabolicTaylorCoefficient A C *
        (∑ l ∈ Finset.Ico start n, (l : ℝ) ^ (3 * delta - 1)) := by
      rw [Finset.mul_sum]
    _ ≤ parabolicTaylorCoefficient A C *
        ((n : ℝ) ^ (3 * delta) / (3 * delta)) := by
      gcongr
      exact sum_Ico_rpow_sub_one_le_from hstart hstartn
        (by positivity) (by linarith)
    _ = parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
        (3 * delta) := by ring

/-- Exact decomposition of the shifted parabolic-energy correction. -/
lemma parabolicEnergyFrom_sub_reference_eq (start n : ℕ)
    (Delta : ℕ → ℝ) (hstart : 1 ≤ start) :
    parabolicEnergyFrom start n Delta -
        parabolicReferenceEnergyFrom start n Delta =
      (∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) +
      (∑ l ∈ Finset.Ico start n, 1 / (2 * (l : ℝ) ^ 2)) +
      (∑ l ∈ Finset.Ico start n,
        (Delta (l + 1) - Delta l) / (l : ℝ)) +
      ∑ l ∈ Finset.Ico start n,
        (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2) := by
  unfold parabolicEnergyFrom parabolicReferenceEnergyFrom
  rw [← Finset.sum_sub_distrib]
  calc
    ∑ l ∈ Finset.Ico start n,
        ((((2 * ((l + 1 : ℕ) : ℝ) ^ 2 + Delta (l + 1)) -
          (2 * (l : ℝ) ^ 2 + Delta l)) ^ 2 / (8 * (l : ℝ) ^ 2)) -
          (2 + (Delta (l + 1) - Delta l) ^ 2 /
            (8 * (l : ℝ) ^ 2))) =
      ∑ l ∈ Finset.Ico start n,
        (2 / (l : ℝ) + 1 / (2 * (l : ℝ) ^ 2) +
          (Delta (l + 1) - Delta l) / (l : ℝ) +
          (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)) := by
      apply Finset.sum_congr rfl
      intro l hl
      rw [parabolic_edge_energy_expansion (by
        have := (Finset.mem_Ico.mp hl).1
        omega : l ≠ 0)]
      ring
    _ = _ := by simp_rw [Finset.sum_add_distrib]

lemma sum_increment_div_eq_from (start n : ℕ) (Delta : ℕ → ℝ)
    (hstart : 1 ≤ start) :
    (∑ l ∈ Finset.Ico start n,
      (Delta (l + 1) - Delta l) / (l : ℝ)) =
      (∑ l ∈ Finset.Ico start n,
        (Delta (l + 1) / (l + 1 : ℕ) - Delta l / (l : ℝ))) +
      ∑ l ∈ Finset.Ico start n,
        Delta (l + 1) / ((l : ℝ) * (l + 1)) := by
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro l hl
  have hl0 : (l : ℝ) ≠ 0 := by
    have hlnat : 1 ≤ l := hstart.trans (Finset.mem_Ico.mp hl).1
    positivity
  have hls0 : ((l + 1 : ℕ) : ℝ) ≠ 0 := by positivity
  push_cast
  field_simp
  ring

lemma sum_telescoping_delta_div_from {start n : ℕ}
    (hstartn : start ≤ n) (Delta : ℕ → ℝ) :
    (∑ l ∈ Finset.Ico start n,
      (Delta (l + 1) / (l + 1 : ℕ) - Delta l / (l : ℝ))) =
      Delta n / n - Delta start / start := by
  let f : ℕ → ℝ := fun l ↦ Delta l / (l : ℝ)
  change (∑ l ∈ Finset.Ico start n, (f (l + 1) - f l)) =
    f n - f start
  rw [Finset.sum_Ico_eq_sub _ hstartn,
    Finset.sum_range_sub, Finset.sum_range_sub]
  ring

lemma abs_sum_increment_div_le_rpow_from {start n : ℕ}
    (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (Delta : ℕ → ℝ) {delta B : ℝ} (hdelta : 0 < delta)
    (hdelta1 : delta ≤ 1) (hB : 0 ≤ B)
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta) :
    |∑ l ∈ Finset.Ico start n,
      (Delta (l + 1) - Delta l) / (l : ℝ)| ≤
      4 * B * (n : ℝ) ^ delta / delta := by
  rw [sum_increment_div_eq_from start n Delta (by omega),
    sum_telescoping_delta_div_from hstartn]
  have hnpos : (0 : ℝ) < n := by
    have : 0 < n := by omega
    positivity
  have hnPow : 0 ≤ (n : ℝ) ^ delta := by positivity
  have hstartPow : (start : ℝ) ^ delta ≤ (n : ℝ) ^ delta :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast hstartn) hdelta.le
  have hBoundaryN : |Delta n / n| ≤ B * (n : ℝ) ^ delta := by
    rw [abs_div, abs_of_pos hnpos]
    apply (div_le_iff₀ hnpos).2
    have hd := hDelta n (by simp [hstartn])
    simpa only [mul_assoc, mul_comm, mul_left_comm] using hd
  have hBoundaryStart : |Delta start / start| ≤ B * (n : ℝ) ^ delta := by
    have hspos : (0 : ℝ) < start := by positivity
    rw [abs_div, abs_of_pos hspos]
    apply (div_le_iff₀ hspos).2
    have hd := hDelta start (by simp [hstartn])
    calc
      |Delta start| ≤ B * (start : ℝ) * (start : ℝ) ^ delta := hd
      _ ≤ B * (start : ℝ) * (n : ℝ) ^ delta := by
        gcongr
      _ = B * (n : ℝ) ^ delta * start := by ring
  have hterm : ∀ l ∈ Finset.Ico start n,
      |Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
        2 * B * (l : ℝ) ^ (delta - 1) := by
    intro l hl
    have hlbounds := Finset.mem_Ico.mp hl
    have hlNat : 1 ≤ l := by omega
    have hlpos : (0 : ℝ) < l := by positivity
    have hmem : l + 1 ∈ Finset.Icc start n := by
      rw [Finset.mem_Icc]
      exact ⟨by omega, hlbounds.2⟩
    have hd := hDelta (l + 1) hmem
    have hp := rpow_succ_le_two_mul hlNat hdelta.le hdelta1
    rw [abs_div, abs_mul, abs_of_pos hlpos,
      abs_of_pos (by positivity : (0 : ℝ) < (l : ℝ) + 1)]
    rw [div_le_iff₀
      (mul_pos hlpos (by positivity : (0 : ℝ) < (l : ℝ) + 1))]
    push_cast at hd ⊢
    rw [Real.rpow_sub hlpos]
    norm_num
    field_simp
    calc
      |Delta (l + 1)| ≤ B * ((l : ℝ) + 1) *
          (((l : ℝ) + 1) ^ delta) := by
        simpa only [Nat.cast_add, Nat.cast_one] using hd
      _ ≤ B * ((l : ℝ) + 1) * (2 * (l : ℝ) ^ delta) := by
        have hp' : ((l : ℝ) + 1) ^ delta ≤
            2 * (l : ℝ) ^ delta := by
          simpa only [Nat.cast_add, Nat.cast_one] using hp
        exact mul_le_mul_of_nonneg_left hp'
          (mul_nonneg hB (by positivity))
      _ = 2 * B * (l : ℝ) ^ delta * ((l : ℝ) + 1) := by ring
  calc
    |Delta n / n - Delta start / start +
        ∑ l ∈ Finset.Ico start n,
          Delta (l + 1) / ((l : ℝ) * (l + 1))| ≤
      |Delta n / n| + |Delta start / start| +
        ∑ l ∈ Finset.Ico start n,
          |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
      calc
        _ ≤ |Delta n / n - Delta start / start| +
            |∑ l ∈ Finset.Ico start n,
              Delta (l + 1) / ((l : ℝ) * (l + 1))| := abs_add_le _ _
        _ ≤ (|Delta n / n| + |Delta start / start|) +
            ∑ l ∈ Finset.Ico start n,
              |Delta (l + 1) / ((l : ℝ) * (l + 1))| := by
          gcongr
          · exact abs_sub _ _
          · exact Finset.abs_sum_le_sum_abs _ _
    _ ≤ B * (n : ℝ) ^ delta + B * (n : ℝ) ^ delta +
        ∑ l ∈ Finset.Ico start n,
          2 * B * (l : ℝ) ^ (delta - 1) := by
      gcongr with l hl
      exact hterm l hl
    _ = 2 * B * (n : ℝ) ^ delta +
        2 * B * (∑ l ∈ Finset.Ico start n,
          (l : ℝ) ^ (delta - 1)) := by
      rw [Finset.mul_sum]
      ring
    _ ≤ 2 * B * (n : ℝ) ^ delta +
        2 * B * ((n : ℝ) ^ delta / delta) := by
      gcongr
      exact sum_Ico_rpow_sub_one_le_from hstart hstartn hdelta hdelta1
    _ ≤ 4 * B * (n : ℝ) ^ delta / delta := by
      have hmul : 0 ≤ B * (n : ℝ) ^ delta := by positivity
      have hX : B * (n : ℝ) ^ delta ≤
          B * (n : ℝ) ^ delta / delta := by
        apply (le_div_iff₀ hdelta).2
        nlinarith [mul_le_mul_of_nonneg_left hdelta1 hmul]
      have htwice :=
        mul_le_mul_of_nonneg_left hX (by norm_num : (0 : ℝ) ≤ 2)
      calc
        2 * B * (n : ℝ) ^ delta +
            2 * B * ((n : ℝ) ^ delta / delta) =
          2 * (B * (n : ℝ) ^ delta) +
            2 * (B * (n : ℝ) ^ delta / delta) := by ring
        _ ≤ 2 * (B * (n : ℝ) ^ delta / delta) +
            2 * (B * (n : ℝ) ^ delta / delta) :=
          add_le_add htwice le_rfl
        _ = 4 * B * (n : ℝ) ^ delta / delta := by ring

/-- Shifted parabolic-to-Gaussian energy estimate. -/
theorem abs_parabolicEnergyFrom_sub_reference_le
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (Delta : ℕ → ℝ) {delta B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hB : 0 ≤ B) (hC : 0 ≤ C)
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hInc : ∀ l ∈ Finset.Ico start n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    |parabolicEnergyFrom start n Delta -
        parabolicReferenceEnergyFrom start n Delta| ≤
      (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
  have hdelta1 : delta ≤ 1 := by linarith
  have hlinear := abs_sum_increment_div_le_rpow_from
    hstart hstartn Delta hdelta hdelta1 hB hDelta
  rw [parabolicEnergyFrom_sub_reference_eq start n Delta (by omega)]
  have hsumPow := sum_Ico_rpow_sub_one_le_from
    hstart hstartn hdelta hdelta1
  have hFirst : (∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) ≤
      2 * ((n : ℝ) ^ delta / delta) := by
    calc
      _ ≤ ∑ l ∈ Finset.Ico start n,
          2 * (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl1 : 1 ≤ l := by
          have := (Finset.mem_Ico.mp hl).1
          omega
        calc
          2 / (l : ℝ) = 2 * (1 / (l : ℝ)) := by ring
          _ ≤ 2 * (l : ℝ) ^ (delta - 1) :=
            mul_le_mul_of_nonneg_left
              (one_div_le_rpow_sub_one hl1 hdelta.le) (by norm_num)
      _ = 2 * (∑ l ∈ Finset.Ico start n,
          (l : ℝ) ^ (delta - 1)) := by rw [Finset.mul_sum]
      _ ≤ 2 * ((n : ℝ) ^ delta / delta) := by gcongr
  have hSecond : (∑ l ∈ Finset.Ico start n,
      1 / (2 * (l : ℝ) ^ 2)) ≤ (n : ℝ) ^ delta / delta := by
    calc
      _ ≤ ∑ l ∈ Finset.Ico start n, (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        intro l hl
        have hl1 : 1 ≤ l := by
          have := (Finset.mem_Ico.mp hl).1
          omega
        have hL : (0 : ℝ) < l := by positivity
        calc
          1 / (2 * (l : ℝ) ^ 2) ≤ 1 / (l : ℝ) := by
            apply (div_le_div_iff₀ (by positivity) hL).2
            nlinarith [show (1 : ℝ) ≤ l by exact_mod_cast hl1,
              sq_nonneg ((l : ℝ) - 1)]
          _ ≤ (l : ℝ) ^ (delta - 1) :=
            one_div_le_rpow_sub_one hl1 hdelta.le
      _ ≤ (n : ℝ) ^ delta / delta := hsumPow
  have hExtraTerm : ∀ l ∈ Finset.Ico start n,
      |(Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
        C / 2 * (l : ℝ) ^ (delta - 1) := by
    intro l hl
    have hL : (0 : ℝ) < l := by
      have : 1 ≤ l := by
        have := (Finset.mem_Ico.mp hl).1
        omega
      positivity
    rw [abs_div, abs_mul, abs_pow, abs_of_pos hL,
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    calc
      |Delta (l + 1) - Delta l| / (2 * (l : ℝ) ^ 2) ≤
          (C * (l : ℝ) * (l : ℝ) ^ delta) /
            (2 * (l : ℝ) ^ 2) :=
        div_le_div_of_nonneg_right (hInc l hl) (by positivity)
      _ = C / 2 * (l : ℝ) ^ (delta - 1) := by
        rw [Real.rpow_sub hL, Real.rpow_one]
        field_simp
  have hExtra : |∑ l ∈ Finset.Ico start n,
      (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
      C / 2 * ((n : ℝ) ^ delta / delta) := by
    calc
      _ ≤ ∑ l ∈ Finset.Ico start n,
          |(Delta (l + 1) - Delta l) /
            (2 * (l : ℝ) ^ 2)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ l ∈ Finset.Ico start n,
          C / 2 * (l : ℝ) ^ (delta - 1) := by
        apply Finset.sum_le_sum
        exact hExtraTerm
      _ = C / 2 * (∑ l ∈ Finset.Ico start n,
          (l : ℝ) ^ (delta - 1)) := by rw [Finset.mul_sum]
      _ ≤ C / 2 * ((n : ℝ) ^ delta / delta) := by gcongr
  have hFirst0 : 0 ≤ ∑ l ∈ Finset.Ico start n, 2 / (l : ℝ) := by positivity
  have hSecond0 : 0 ≤ ∑ l ∈ Finset.Ico start n,
      1 / (2 * (l : ℝ) ^ 2) := by positivity
  calc
    |(∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) +
      (∑ l ∈ Finset.Ico start n, 1 / (2 * (l : ℝ) ^ 2)) +
        (∑ l ∈ Finset.Ico start n,
          (Delta (l + 1) - Delta l) / (l : ℝ)) +
        ∑ l ∈ Finset.Ico start n,
          (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| ≤
      (∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) +
        (∑ l ∈ Finset.Ico start n, 1 / (2 * (l : ℝ) ^ 2)) +
        |∑ l ∈ Finset.Ico start n,
          (Delta (l + 1) - Delta l) / (l : ℝ)| +
        |∑ l ∈ Finset.Ico start n,
          (Delta (l + 1) - Delta l) / (2 * (l : ℝ) ^ 2)| := by
      calc
        _ ≤ |(∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) +
              (∑ l ∈ Finset.Ico start n,
                1 / (2 * (l : ℝ) ^ 2)) +
              (∑ l ∈ Finset.Ico start n,
                (Delta (l + 1) - Delta l) / (l : ℝ))| +
            |∑ l ∈ Finset.Ico start n,
              (Delta (l + 1) - Delta l) /
                (2 * (l : ℝ) ^ 2)| := abs_add_le _ _
        _ ≤ (|(∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)) +
              (∑ l ∈ Finset.Ico start n,
                1 / (2 * (l : ℝ) ^ 2))| +
              |∑ l ∈ Finset.Ico start n,
                (Delta (l + 1) - Delta l) / (l : ℝ)|) +
            |∑ l ∈ Finset.Ico start n,
              (Delta (l + 1) - Delta l) /
                (2 * (l : ℝ) ^ 2)| := by
          gcongr
          exact abs_add_le _ _
        _ ≤ (|∑ l ∈ Finset.Ico start n, 2 / (l : ℝ)| +
              |∑ l ∈ Finset.Ico start n,
                1 / (2 * (l : ℝ) ^ 2)| +
              |∑ l ∈ Finset.Ico start n,
                (Delta (l + 1) - Delta l) / (l : ℝ)|) +
            |∑ l ∈ Finset.Ico start n,
              (Delta (l + 1) - Delta l) /
                (2 * (l : ℝ) ^ 2)| := by
          gcongr
          exact abs_add_le _ _
        _ = _ := by rw [abs_of_nonneg hFirst0, abs_of_nonneg hSecond0]
    _ ≤ 2 * ((n : ℝ) ^ delta / delta) +
        ((n : ℝ) ^ delta / delta) +
        4 * B * (n : ℝ) ^ delta / delta +
        C / 2 * ((n : ℝ) ^ delta / delta) := by gcongr
    _ = (3 + 4 * B + C / 2) * ((n : ℝ) ^ delta / delta) := by ring
    _ ≤ (3 + 4 * B + C / 2) *
        ((n : ℝ) ^ (3 * delta) / delta) := by
      gcongr
      · exact_mod_cast (show 1 ≤ n by omega)
      · linarith
    _ = (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
      ring

/-- **Shifted pathwise HLOZ (A.11), logarithmic form.** -/
theorem sum_edgeStirlingExponent_add_gaussian_ge_from
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ) (Delta : ℕ → ℝ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico start n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico start n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico start n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico start n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + Delta l)
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico start n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    -(2 * (n - start : ℕ) : ℝ) - gaussianEnergyFrom start n Delta -
        a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) ≤
      (∑ l ∈ Finset.Ico start n,
        edgeStirlingExponent (m l) (m (l + 1))) +
        gaussianNormalizerLogSumFrom start n := by
  have htaylor := abs_sum_edgeStirlingExponent_parabolic_le_from
    start n hstart hstartn m hdelta hdeltaThird hA hC hpos hwindow
    hbase hclose hmoderate hinc
  have henergy := abs_parabolicEnergyFrom_sub_reference_le
    start n hstart hstartn Delta hdelta hdeltaThird hB hC hDelta hDeltaInc
  have htaylorLower := neg_le_of_abs_le htaylor
  have henergyUpper := le_of_abs_le henergy
  have href := parabolicReferenceEnergyFrom_eq hstartn Delta
  have hparaEnergy :
      parabolicEnergyFrom start n Delta =
        ∑ l ∈ Finset.Ico start n,
          parabolicTransitionIncrement (m l) (m (l + 1)) ^ 2 /
            (8 * (l : ℝ) ^ 2) := by
    unfold parabolicEnergyFrom parabolicTransitionIncrement
    apply Finset.sum_congr rfl
    intro l hl
    rw [hparabolic (l + 1), hparabolic l]
  rw [hparaEnergy] at henergyUpper
  rw [href] at henergyUpper
  unfold gaussianNormalizerLogSumFrom
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib] at htaylorLower
  have hcast : ((n - start : ℕ) : ℝ) = (n : ℝ) - start := by
    rw [Nat.cast_sub hstartn]
  have herr :
      a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) =
        parabolicTaylorCoefficient A C * (n : ℝ) ^ (3 * delta) /
            (3 * delta) +
          (3 + 4 * B + C / 2) * (n : ℝ) ^ (3 * delta) / delta := by
    unfold a11ErrorCoefficient
    ring
  rw [hcast, herr]
  linarith

/-- Exponentiated shifted form of HLOZ (A.11). -/
theorem exp_a11Error_mul_gaussianLogWeight_le_from
    (start n : ℕ) (hstart : 2 ≤ start) (hstartn : start ≤ n)
    (m : ℕ → ℕ) (Delta : ℕ → ℝ)
    {delta A B C : ℝ} (hdelta : 0 < delta)
    (hdeltaThird : delta ≤ 1 / 3) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hC : 0 ≤ C)
    (hpos : ∀ l ∈ Finset.Ico start n, 2 ≤ m l)
    (hwindow : ∀ l ∈ Finset.Ico start n,
      InEdgeTaylorWindow (m l) (m (l + 1)))
    (hbase : ∀ l ∈ Finset.Ico start n,
      (l : ℝ) ^ 2 ≤ (m l - 1 : ℕ))
    (hclose : ∀ l ∈ Finset.Ico start n,
      |2 * (l : ℝ) ^ 2 - (m l - 1 : ℕ)| ≤
        A * (l : ℝ) * (l : ℝ) ^ delta)
    (hmoderate : ∀ l ∈ Finset.Ico start n,
      A * (l : ℝ) * (l : ℝ) ^ delta ≤ (l : ℝ) ^ 2)
    (hinc : ∀ l ∈ Finset.Ico start n,
      |parabolicTransitionIncrement (m l) (m (l + 1))| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta)
    (hparabolic : ∀ l, (m l : ℝ) = 2 * (l : ℝ) ^ 2 + Delta l)
    (hDelta : ∀ l ∈ Finset.Icc start n,
      |Delta l| ≤ B * (l : ℝ) * (l : ℝ) ^ delta)
    (hDeltaInc : ∀ l ∈ Finset.Ico start n,
      |Delta (l + 1) - Delta l| ≤
        C * (l : ℝ) * (l : ℝ) ^ delta) :
    Real.exp
        (-(2 * (n - start : ℕ) : ℝ) -
          a11ErrorCoefficient delta A B C * (n : ℝ) ^ (3 * delta) -
          gaussianEnergyFrom start n Delta -
          gaussianNormalizerLogSumFrom start n) ≤
      Real.exp
        (∑ l ∈ Finset.Ico start n,
          edgeStirlingExponent (m l) (m (l + 1))) := by
  apply Real.exp_le_exp.mpr
  have h := sum_edgeStirlingExponent_add_gaussian_ge_from
    start n hstart hstartn m Delta hdelta hdeltaThird hA hB hC hpos
    hwindow hbase hclose hmoderate hinc hparabolic hDelta hDeltaInc
  linarith

end

end Erdos1165.ProfileA11Tail
