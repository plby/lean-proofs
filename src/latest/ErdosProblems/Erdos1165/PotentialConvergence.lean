/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialKernel
import ErdosProblems.Erdos1165.OffDiagonal
import ErdosProblems.Erdos1165.EndpointDiagonal
import ErdosProblems.Erdos1165.BinomialGaussian
import Mathlib.Analysis.PSeries

/-!
# Convergence of the planar potential kernel

This file supplies the analytic cancellation missing from
`PotentialKernel.lean`.  The key elementary observation is that, for a fixed
diagonal displacement `d`, the loss between a centered binomial mass and the
mass displaced by `d` is `O_d(n⁻¹)` relative to the centered mass.  The
product of two centered masses is the planar return probability, itself at
most `1/(n+1)`.  Thus the difference of the two-dimensional masses is bounded
by a constant times `1/(n(n+1))` and is summable.

The period-two walk needs a little care.  For a point in the even parity
class, the odd summands vanish and the potential series is absolutely
summable.  For a point in the odd parity class the even and odd subseries
diverge separately; only consecutive pairs cancel.  Accordingly the final
potential is defined from paired terms, while convergence of ordinary
chronological partial sums is stated as an ordered `Tendsto` theorem rather
than the (unconditional) Mathlib predicate `Summable`.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialConvergence

open BinomialGaussian EndpointDiagonal PotentialKernel

/-! ## A summable fixed-displacement binomial loss -/

/-- A deliberately coarse polynomial constant for a fixed binomial offset. -/
def binomialLossConstant (d : ℕ) : ℝ := 12 * (d + 1 : ℝ) ^ 3

lemma binomialLossConstant_nonneg (d : ℕ) : 0 ≤ binomialLossConstant d := by
  unfold binomialLossConstant
  positivity

/-- The explicit Gaussian error from `BinomialGaussian` is `O_d(1/n)` for a
fixed offset.  The coarse constant keeps later summability arguments short. -/
theorem center_sub_shift_le {n d : ℕ} (hn : 0 < n) (hmoderate : 2 * d ≤ n) :
    evenSymmetricMass n 0 - evenSymmetricMass n d ≤
      binomialLossConstant d / n * evenSymmetricMass n 0 := by
  have hd : d < n := by omega
  have hraw := (evenSymmetricMass_center_sub_le hn hd hmoderate).2
  let E : ℝ := 8 * n * |relativeDeviation n d| ^ 3 + relativeDeviation n d ^ 2 +
    (1 : ℝ) / (6 * (n - d)) + (1 : ℝ) / (6 * n)
  have hnR : (0 : ℝ) < n := by positivity
  have hndR : (0 : ℝ) < n - d := by
    have hdR : (d : ℝ) < n := by exact_mod_cast hd
    linarith
  have hhalf : (n : ℝ) / 2 ≤ n - d := by
    have hm : (2 : ℝ) * d ≤ n := by exact_mod_cast hmoderate
    linarith
  have hinvSub : (1 : ℝ) / (n - d) ≤ 2 / n := by
    rw [div_le_div_iff₀ hndR hnR]
    nlinarith
  have hrel_nonneg : 0 ≤ relativeDeviation n d := by
    unfold relativeDeviation
    positivity
  have hcoeff : (d : ℝ) ^ 2 / n + E ≤ binomialLossConstant d / n := by
    dsimp [E, binomialLossConstant]
    rw [abs_of_nonneg hrel_nonneg]
    unfold relativeDeviation
    have hdR : (0 : ℝ) ≤ d := by positivity
    have hnOne : (1 : ℝ) ≤ n := by exact_mod_cast hn
    have hcube : 8 * (n : ℝ) * ((d : ℝ) / n) ^ 3 ≤
        8 * (d : ℝ) ^ 3 / n := by
      have hmul : (d : ℝ) ^ 3 ≤ n * (d : ℝ) ^ 3 :=
        by simpa using mul_le_mul_of_nonneg_right hnOne (pow_nonneg hdR 3)
      field_simp
      nlinarith [hmul]
    have hsquare : ((d : ℝ) / n) ^ 2 ≤ (d : ℝ) ^ 2 / n := by
      field_simp
      nlinarith
    have hsub : (1 : ℝ) / (6 * ((n : ℝ) - d)) ≤ 1 / (3 * n) := by
      have := hinvSub
      field_simp at this ⊢
      nlinarith
    calc
      (d : ℝ) ^ 2 / n +
          (8 * n * ((d : ℝ) / n) ^ 3 + ((d : ℝ) / n) ^ 2 +
            1 / (6 * ((n : ℝ) - d)) + 1 / (6 * n)) ≤
          (d : ℝ) ^ 2 / n +
            (8 * (d : ℝ) ^ 3 / n + (d : ℝ) ^ 2 / n +
              1 / (3 * n) + 1 / (6 * n)) := by gcongr
      _ ≤ 12 * ((d : ℝ) + 1) ^ 3 / n := by
        field_simp
        nlinarith [sq_nonneg ((d : ℝ) - 1), pow_nonneg hdR 3]
  exact hraw.trans (mul_le_mul_of_nonneg_right hcoeff
    (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le)

/-- The centered binomial mass is nonnegative, and a displaced mass is no
larger. -/
theorem center_sub_shift_nonneg (n d : ℕ) :
    0 ≤ evenSymmetricMass n 0 - evenSymmetricMass n d := by
  exact sub_nonneg.mpr (evenSymmetricMass_le_center n d)

/-- Product mass at two diagonal offsets. -/
noncomputable def diagonalProductMass (n d e : ℕ) : ℝ :=
  evenSymmetricMass n d * evenSymmetricMass n e

/-- Loss of the two-dimensional product mass from its centered value. -/
noncomputable def diagonalProductLoss (d e n : ℕ) : ℝ :=
  diagonalProductMass n 0 0 - diagonalProductMass n d e

lemma diagonalProductMass_center (n : ℕ) :
    diagonalProductMass n 0 0 = planarReturnProbability n := by
  have hpow : (2 : ℝ) ^ (2 * n) = 4 ^ n := by
    rw [pow_mul]
    norm_num
  unfold diagonalProductMass evenSymmetricMass symBinomialMass planarReturnProbability
  rw [Nat.centralBinom_eq_two_mul_choose, hpow]
  rw [div_mul_div_comm]
  congr 1
  · norm_num
    ring
  · rw [← mul_pow]
    norm_num

theorem diagonalProductLoss_nonneg (d e n : ℕ) :
    0 ≤ diagonalProductLoss d e n := by
  unfold diagonalProductLoss diagonalProductMass
  have hd := evenSymmetricMass_le_center n d
  have he := evenSymmetricMass_le_center n e
  have h0d := evenSymmetricMass_pos (n := n) (d := 0) (by omega)
  have hde0 : 0 ≤ evenSymmetricMass n d := by
    unfold evenSymmetricMass symBinomialMass
    positivity
  nlinarith

/-- The product loss has the summable `O(n⁻²)` envelope once `n` is
larger than both fixed offsets. -/
theorem diagonalProductLoss_le {d e n : ℕ} (hn : 0 < n)
    (hd : 2 * d ≤ n) (he : 2 * e ≤ n) :
    diagonalProductLoss d e n ≤
      (binomialLossConstant d + binomialLossConstant e) /
        ((n : ℝ) * (n + 1)) := by
  let c := evenSymmetricMass n 0
  let a := evenSymmetricMass n d
  let b := evenSymmetricMass n e
  have hca := center_sub_shift_le hn hd
  have hcb := center_sub_shift_le hn he
  have ha0 : 0 ≤ a := by
    dsimp [a, evenSymmetricMass, symBinomialMass]
    positivity
  have hac : a ≤ c := evenSymmetricMass_le_center n d
  have hbc : b ≤ c := evenSymmetricMass_le_center n e
  have hc0 : 0 ≤ c := (evenSymmetricMass_pos (n := n) (d := 0) (by omega)).le
  have hreturn := planarReturnProbability_upper_bound n
  rw [← diagonalProductMass_center] at hreturn
  change c * c ≤ 1 / (n + 1 : ℝ) at hreturn
  have hdecomp : diagonalProductLoss d e n = (c - a) * c + a * (c - b) := by
    dsimp [diagonalProductLoss, diagonalProductMass, c, a, b]
    ring
  rw [hdecomp]
  calc
    (c - a) * c + a * (c - b) ≤
        (binomialLossConstant d / n * c) * c +
          c * (binomialLossConstant e / n * c) := by
      gcongr
    _ = (binomialLossConstant d + binomialLossConstant e) / n * (c * c) := by ring
    _ ≤ (binomialLossConstant d + binomialLossConstant e) / n *
        (1 / (n + 1 : ℝ)) := by
      gcongr
      exact div_nonneg (add_nonneg (binomialLossConstant_nonneg d)
        (binomialLossConstant_nonneg e)) (by positivity)
    _ = (binomialLossConstant d + binomialLossConstant e) /
        ((n : ℝ) * (n + 1)) := by
      field_simp

lemma summable_inverse_nat_mul_succ :
    Summable (fun n : ℕ ↦ (1 : ℝ) / ((n : ℝ) * (n + 1))) := by
  have hsquare : Summable (fun n : ℕ ↦ (1 : ℝ) / (n : ℝ) ^ 2) :=
    Real.summable_one_div_nat_pow.mpr (by norm_num)
  apply Summable.of_nonneg_of_le (fun n ↦ by positivity) (fun n ↦ ?_) hsquare
  by_cases hn : n = 0
  · subst n
    simp
  · apply (div_le_div_iff₀ (by positivity : (0 : ℝ) < (n : ℝ) * (n + 1))
        (by positivity : (0 : ℝ) < (n : ℝ) ^ 2)).2
    nlinarith

/-- Exact telescoping value of the shifted comparison series. -/
theorem hasSum_inverse_nat_mul_succ_shift {M : ℕ} (hM : 0 < M) :
    HasSum (fun n : ℕ ↦ (1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))) (1 / (M : ℝ)) := by
  let f : ℕ → ℝ := fun n ↦ (1 : ℝ) / ((n + M : ℕ) : ℝ)
  have hterm (n : ℕ) :
      (1 : ℝ) / (((n + M : ℕ) : ℝ) * (n + M + 1)) = f n - f (n + 1) := by
    dsimp [f]
    push_cast
    field_simp
    ring
  have hsum : Summable (fun n : ℕ ↦ (1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using
      (summable_nat_add_iff M).mpr summable_inverse_nat_mul_succ
  have hnorm : Summable (fun n : ℕ ↦ ‖(1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1))‖) := by
    apply hsum.congr
    intro n
    rw [Real.norm_eq_abs, abs_of_nonneg]
    positivity
  apply (hasSum_iff_tendsto_nat_of_summable_norm hnorm).2
  have hf_zero : Tendsto f atTop (nhds 0) := by
    apply squeeze_zero' (Filter.Eventually.of_forall fun n ↦ by
        dsimp [f]
        have hnM : (0 : ℝ) < (n + M : ℕ) := by exact_mod_cast (show 0 < n + M by omega)
        positivity)
      (Filter.Eventually.of_forall fun n ↦ ?_) tendsto_one_div_add_atTop_nhds_zero_nat
    dsimp [f]
    apply one_div_le_one_div_of_le (by positivity)
    exact_mod_cast (show n + 1 ≤ n + M by omega)
  have hpartial : ∀ n : ℕ,
      ∑ i ∈ Finset.range n, (1 : ℝ) /
          (((i + M : ℕ) : ℝ) * (i + M + 1)) = f 0 - f n := by
    intro n
    simp_rw [hterm]
    exact Finset.sum_range_sub' f n
  simp_rw [hpartial]
  simpa [f] using (tendsto_const_nhds.sub hf_zero)

theorem tsum_inverse_nat_mul_succ_shift {M : ℕ} (hM : 0 < M) :
    ∑' n : ℕ, (1 : ℝ) / (((n + M : ℕ) : ℝ) * (n + M + 1)) =
      1 / (M : ℝ) :=
  (hasSum_inverse_nat_mul_succ_shift hM).tsum_eq

/-- For every pair of fixed diagonal offsets, the product-mass cancellation
is absolutely summable. -/
theorem summable_diagonalProductLoss (d e : ℕ) :
    Summable (diagonalProductLoss d e) := by
  let C : ℝ := binomialLossConstant d + binomialLossConstant e
  let N : ℕ := 2 * d + 2 * e + 1
  have henv : Summable (fun n : ℕ ↦ C *
      ((1 : ℝ) / ((n : ℝ) * (n + 1)))) :=
    summable_inverse_nat_mul_succ.mul_left C
  apply (summable_nat_add_iff N).mp
  have henvShift : Summable (fun n : ℕ ↦ C *
      ((1 : ℝ) / (((n + N : ℕ) : ℝ) * (n + N + 1)))) := by
    simpa only [Nat.cast_add, Nat.cast_one] using (summable_nat_add_iff N).mpr henv
  apply Summable.of_nonneg_of_le
    (fun n ↦ diagonalProductLoss_nonneg d e (n + N)) (fun n ↦ ?_) henvShift
  have hn0 : 0 < n + N := by dsimp [N]; omega
  have hd : 2 * d ≤ n + N := by dsimp [N]; omega
  have he : 2 * e ≤ n + N := by dsimp [N]; omega
  have h := diagonalProductLoss_le hn0 hd he
  dsimp [C]
  simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h

/-- Explicit tail estimate for the product cancellation. -/
theorem tsum_diagonalProductLoss_shift_le {d e M : ℕ} (hM : 0 < M)
    (hd : 2 * d ≤ M) (he : 2 * e ≤ M) :
    ∑' n : ℕ, diagonalProductLoss d e (n + M) ≤
      (binomialLossConstant d + binomialLossConstant e) / M := by
  let C : ℝ := binomialLossConstant d + binomialLossConstant e
  have hf : Summable (fun n : ℕ ↦ diagonalProductLoss d e (n + M)) :=
    (summable_nat_add_iff M).mpr (summable_diagonalProductLoss d e)
  have hg : Summable (fun n : ℕ ↦ C * ((1 : ℝ) /
      (((n + M : ℕ) : ℝ) * (n + M + 1)))) :=
    (hasSum_inverse_nat_mul_succ_shift hM).summable.mul_left C
  calc
    ∑' n : ℕ, diagonalProductLoss d e (n + M) ≤
        ∑' n : ℕ, C * ((1 : ℝ) /
          (((n + M : ℕ) : ℝ) * (n + M + 1))) := by
      apply Summable.tsum_le_tsum _ hf hg
      intro n
      have hn0 : 0 < n + M := by omega
      have hdn : 2 * d ≤ n + M := hd.trans (Nat.le_add_left M n)
      have hen : 2 * e ≤ n + M := he.trans (Nat.le_add_left M n)
      have h := diagonalProductLoss_le hn0 hdn hen
      dsimp [C]
      simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using h
    _ = C * (1 / (M : ℝ)) := by
      exact ((hasSum_inverse_nat_mul_succ_shift hM).mul_left C).tsum_eq
    _ = (binomialLossConstant d + binomialLossConstant e) / M := by
      dsimp [C]
      ring

/-! ## The infinite diagonal potential and logarithmic scale -/

/-- Infinite potential for a point whose two absolute diagonal offsets are
`d` and `e`. -/
noncomputable def diagonalPotential (d e : ℕ) : ℝ :=
  ∑' n : ℕ, diagonalProductLoss d e n

theorem diagonalPotential_nonneg (d e : ℕ) : 0 ≤ diagonalPotential d e := by
  exact tsum_nonneg (diagonalProductLoss_nonneg d e)

theorem diagonalProductMass_eq_zero_of_lt_left {n d e : ℕ} (hnd : n < d) :
    diagonalProductMass n d e = 0 := by
  unfold diagonalProductMass evenSymmetricMass symBinomialMass
  rw [Nat.choose_eq_zero_of_lt (by omega)]
  simp

theorem diagonalProductMass_eq_zero_of_lt_right {n d e : ℕ} (hne : n < e) :
    diagonalProductMass n d e = 0 := by
  have hz : (2 * n).choose (n + e) = 0 := Nat.choose_eq_zero_of_lt (by omega)
  unfold diagonalProductMass evenSymmetricMass symBinomialMass
  rw [hz]
  simp

theorem diagonalProductLoss_eq_return_of_lt_max {n d e : ℕ}
    (hn : n < max d e) :
    diagonalProductLoss d e n = planarReturnProbability n := by
  rw [lt_max_iff] at hn
  unfold diagonalProductLoss
  rw [diagonalProductMass_center]
  rcases hn with hn | hn
  · rw [diagonalProductMass_eq_zero_of_lt_left hn, sub_zero]
  · rw [diagonalProductMass_eq_zero_of_lt_right hn, sub_zero]

/-- A finite diagonal-potential prefix is at most the corresponding harmonic
sum, hence logarithmic in its length. -/
theorem sum_diagonalProductLoss_le_log {d e M : ℕ} (_hM : 0 < M) :
    ∑ n ∈ Finset.range M, diagonalProductLoss d e n ≤
      1 + Real.log (M : ℝ) := by
  calc
    ∑ n ∈ Finset.range M, diagonalProductLoss d e n ≤
        ∑ n ∈ Finset.range M, planarReturnProbability n := by
      apply Finset.sum_le_sum
      intro n hn
      unfold diagonalProductLoss
      rw [diagonalProductMass_center]
      have hmass : 0 ≤ diagonalProductMass n d e := by
        unfold diagonalProductMass evenSymmetricMass symBinomialMass
        positivity
      linarith
    _ ≤ ∑ n ∈ Finset.range M, (1 / (n + 1 : ℝ)) := by
      exact Finset.sum_le_sum fun n _ ↦ planarReturnProbability_upper_bound n
    _ = (harmonic M : ℝ) := by simp [harmonic, one_div]
    _ ≤ 1 + Real.log (M : ℝ) := by
      exact_mod_cast harmonic_le_one_add_log M

/-- Finite propagation gives the matching logarithmic lower bound up to the
smaller of the displacement scale and the truncation scale. -/
theorem sum_diagonalProductLoss_log_lower {d e m : ℕ} (hm : m < max d e) :
    (1 / 4 : ℝ) * Real.log (m + 1 : ℝ) ≤
      ∑ n ∈ Finset.range (m + 1), diagonalProductLoss d e n := by
  have heq : ∑ n ∈ Finset.range (m + 1), diagonalProductLoss d e n =
      ∑ n ∈ Finset.range (m + 1), planarReturnProbability n := by
    apply Finset.sum_congr rfl
    intro n hn
    apply diagonalProductLoss_eq_return_of_lt_max
    exact (Nat.le_of_lt_succ (Finset.mem_range.mp hn)).trans_lt hm
  rw [heq]
  calc
    (1 / 4 : ℝ) * Real.log (m + 1 : ℝ) ≤
        (1 / 4 : ℝ) * (harmonic m : ℝ) := by
      gcongr
      exact_mod_cast log_add_one_le_harmonic m
    _ = ∑ n ∈ Finset.Icc 1 m, (1 / (4 * n : ℝ)) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro n hn
      field_simp
    _ ≤ ∑ n ∈ Finset.Icc 1 m, planarReturnProbability n := by
      apply Finset.sum_le_sum
      intro n hn
      exact planarReturnProbability_lower_bound (Finset.mem_Icc.mp hn).1
    _ ≤ ∑ n ∈ Finset.range (m + 1), planarReturnProbability n := by
      apply Finset.sum_le_sum_of_subset_of_nonneg
      · intro n hn
        rw [Finset.mem_range]
        exact Nat.lt_succ_of_le (Finset.mem_Icc.mp hn).2
      · intro n _ _
        exact (planarReturnProbability_pos n).le

/-- Every finite prefix is bounded by the infinite nonnegative potential. -/
theorem sum_diagonalProductLoss_le_potential (d e M : ℕ) :
    ∑ n ∈ Finset.range M, diagonalProductLoss d e n ≤ diagonalPotential d e := by
  exact (summable_diagonalProductLoss d e).sum_le_tsum _
    (fun n _ ↦ diagonalProductLoss_nonneg d e n)

/-- Radial logarithmic lower bound for the infinite diagonal potential. -/
theorem diagonalPotential_log_lower {d e : ℕ} (hde : max d e ≠ 0) :
    (1 / 4 : ℝ) * Real.log (max d e : ℝ) ≤ diagonalPotential d e := by
  let m := max d e - 1
  have hm : m < max d e := by dsimp [m]; omega
  have hprefix := sum_diagonalProductLoss_log_lower (d := d) (e := e) hm
  have hle := sum_diagonalProductLoss_le_potential d e (m + 1)
  have hcast : ((m + 1 : ℕ) : ℝ) = max d e := by
    congr 1
    dsimp [m]
    omega
  norm_num only [Nat.cast_add, Nat.cast_one] at hcast hprefix
  rw [hcast] at hprefix
  simpa only [Nat.cast_max] using hprefix.trans hle

/-- A concrete radial scale large enough to make the summable tail at most
one. -/
def radialCutoff (d e : ℕ) : ℕ := 24 * (d + e + 1) ^ 3

lemma radialCutoff_pos (d e : ℕ) : 0 < radialCutoff d e := by
  unfold radialCutoff
  positivity

lemma two_mul_le_radialCutoff_left (d e : ℕ) : 2 * d ≤ radialCutoff d e := by
  unfold radialCutoff
  have hbase : d ≤ d + e + 1 := by omega
  have hpow : d + e + 1 ≤ (d + e + 1) ^ 3 := Nat.le_pow (by omega)
  nlinarith

lemma two_mul_le_radialCutoff_right (d e : ℕ) : 2 * e ≤ radialCutoff d e := by
  unfold radialCutoff
  have hbase : e ≤ d + e + 1 := by omega
  have hpow : d + e + 1 ≤ (d + e + 1) ^ 3 := Nat.le_pow (by omega)
  nlinarith

lemma lossConstant_add_le_radialCutoff (d e : ℕ) :
    binomialLossConstant d + binomialLossConstant e ≤ radialCutoff d e := by
  have hdA : ((d + 1 : ℕ) : ℝ) ≤ (d + e + 1 : ℕ) := by exact_mod_cast (by omega)
  have heA : ((e + 1 : ℕ) : ℝ) ≤ (d + e + 1 : ℕ) := by exact_mod_cast (by omega)
  have hdPow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (d + 1 : ℕ)) hdA 3
  have hePow := pow_le_pow_left₀ (by positivity : (0 : ℝ) ≤ (e + 1 : ℕ)) heA 3
  unfold binomialLossConstant radialCutoff
  norm_num only [Nat.cast_mul, Nat.cast_ofNat, Nat.cast_pow, Nat.cast_add, Nat.cast_one]
    at hdPow hePow ⊢
  nlinarith

/-- Explicit logarithmic upper bound.  Since `radialCutoff` is cubic in
`d+e+1`, this is `O(log(d+e+1))`. -/
theorem diagonalPotential_log_upper (d e : ℕ) :
    diagonalPotential d e ≤ 2 + Real.log (radialCutoff d e : ℝ) := by
  let M := radialCutoff d e
  have hsplit := (summable_diagonalProductLoss d e).sum_add_tsum_nat_add M
  have hprefix := sum_diagonalProductLoss_le_log (d := d) (e := e) (radialCutoff_pos d e)
  have htail := tsum_diagonalProductLoss_shift_le (d := d) (e := e)
    (radialCutoff_pos d e) (two_mul_le_radialCutoff_left d e)
      (two_mul_le_radialCutoff_right d e)
  have hratio : (binomialLossConstant d + binomialLossConstant e) /
      (radialCutoff d e : ℝ) ≤ 1 := by
    have hMReal : (0 : ℝ) < radialCutoff d e := by exact_mod_cast radialCutoff_pos d e
    rw [div_le_one hMReal]
    exact lossConstant_add_le_radialCutoff d e
  dsimp [diagonalPotential]
  rw [← hsplit]
  dsimp [M] at hprefix htail ⊢
  linarith

/-! ## One-step cancellation and arbitrary lattice points -/

lemma blockDisplacement_succ (u : Fin (N + 1) → Direction) :
    blockDisplacement u = directionVector (u 0) + blockDisplacement (Fin.tail u) := by
  rw [blockDisplacement, Fin.sum_univ_succ]
  rfl

/-- Split a nonempty direction word at its first step, retaining the endpoint
constraint on the remaining word. -/
noncomputable def endpointSuccFiberEquiv (N : ℕ) (x : Point) :
    {u : Fin (N + 1) → Direction // blockDisplacement u = x} ≃
      Σ d : Direction, {v : Fin N → Direction //
        blockDisplacement v = x - directionVector d} where
  toFun u := ⟨u.1 0, ⟨Fin.tail u.1, by
    have hu := u.2
    rw [blockDisplacement_succ] at hu
    apply (eq_sub_iff_add_eq).2
    simpa [add_comm] using hu⟩⟩
  invFun p := ⟨Fin.cons p.1 p.2.1, by
    rw [blockDisplacement_succ, Fin.cons_zero, Fin.tail_cons, p.2.2]
    abel⟩
  left_inv u := by
    apply Subtype.ext
    exact Fin.cons_self_tail u.1
  right_inv p := by
    rcases p with ⟨d, v⟩
    apply Sigma.ext
    · rfl
    · apply heq_of_eq
      apply Subtype.ext
      exact @Fin.tail_cons N (fun _ ↦ Direction) d v.1

theorem card_endpointBlocks_succ (N : ℕ) (x : Point) :
    (endpointBlocks (N + 1) x).card =
      ∑ d : Direction, (endpointBlocks N (x - directionVector d)).card := by
  let eLeft : ↑(endpointBlocks (N + 1) x) ≃
      {u : Fin (N + 1) → Direction // blockDisplacement u = x} :=
    { toFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mp u.2⟩
      invFun := fun u ↦ ⟨u.1, mem_endpointBlocks.mpr u.2⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  have hfiber (d : Direction) :
      Fintype.card {v : Fin N → Direction //
          blockDisplacement v = x - directionVector d} =
        (endpointBlocks N (x - directionVector d)).card := by
    let e : {v : Fin N → Direction //
          blockDisplacement v = x - directionVector d} ≃
        ↑(endpointBlocks N (x - directionVector d)) :=
      { toFun := fun v ↦ ⟨v.1, mem_endpointBlocks.mpr v.2⟩
        invFun := fun v ↦ ⟨v.1, mem_endpointBlocks.mp v.2⟩
        left_inv := fun _ ↦ rfl
        right_inv := fun _ ↦ rfl }
    exact (Fintype.card_congr e).trans (Fintype.card_coe _)
  calc
    (endpointBlocks (N + 1) x).card =
        Fintype.card {u : Fin (N + 1) → Direction // blockDisplacement u = x} := by
      rw [← Fintype.card_congr eLeft, Fintype.card_coe]
    _ = Fintype.card (Σ d : Direction, {v : Fin N → Direction //
          blockDisplacement v = x - directionVector d}) :=
      Fintype.card_congr (endpointSuccFiberEquiv N x)
    _ = ∑ d : Direction, Fintype.card {v : Fin N → Direction //
          blockDisplacement v = x - directionVector d} := Fintype.card_sigma
    _ = ∑ d : Direction, (endpointBlocks N (x - directionVector d)).card := by
      apply Finset.sum_congr rfl
      intro d _
      exact hfiber d

/-- Chapman--Kolmogorov for one final (equivalently first) step, at the exact
finite-count level. -/
theorem endpointProbability_succ (N : ℕ) (x : Point) :
    endpointProbability (N + 1) x =
      (1 / 4 : ℝ) * ∑ d : Direction,
        endpointProbability N (x - directionVector d) := by
  unfold endpointProbability
  rw [card_endpointBlocks_succ]
  push_cast
  rw [div_eq_mul_inv, Finset.sum_mul]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro d _
  rw [pow_succ]
  field_simp

/-- Chronological potential summand. -/
noncomputable def potentialTerm (x : Point) (N : ℕ) : ℝ :=
  endpointProbability N 0 - endpointProbability N x

/-- Consecutive even/odd pair.  Pairing is essential for the parity class
opposite the origin. -/
noncomputable def potentialPair (x : Point) (n : ℕ) : ℝ :=
  potentialTerm x (2 * n) + potentialTerm x (2 * n + 1)

/-- The infinite planar potential kernel, defined by its convergent
chronological pairs. -/
noncomputable def planarPotentialKernel (x : Point) : ℝ :=
  ∑' n : ℕ, potentialPair x n

theorem endpointProbability_odd_eq_zero_of_even {n : ℕ} {x : Point}
    (hx : Even (x.1 + x.2)) : endpointProbability (2 * n + 1) x = 0 := by
  unfold endpointProbability
  apply div_eq_zero_iff.mpr
  left
  norm_cast
  apply Finset.card_eq_zero.mpr
  ext u
  constructor
  · intro hu
    have hdiag :
        (blockDisplacement u).1 + (blockDisplacement u).2 =
          ∑ i, boolSign ((blockBitsEquiv (2 * n + 1) u).1 i) := by
      rw [blockDisplacement, Prod.fst_sum, Prod.snd_sum, ← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro i _
      have h := congrArg Prod.fst (diagonalMap_directionVector (u i))
      simpa [diagonalMap, blockBitsEquiv] using h
    rw [mem_endpointBlocks] at hu
    rw [hu] at hdiag
    rw [sum_boolSign_eq] at hdiag
    obtain ⟨z, hz⟩ := hx
    rw [hz] at hdiag
    norm_num only [Fintype.card_fin, Nat.cast_add, Nat.cast_mul, Nat.cast_one] at hdiag
    omega
  · intro hu
    simp at hu

theorem endpointProbability_odd_zero (n : ℕ) :
    endpointProbability (2 * n + 1) 0 = 0 := by
  exact endpointProbability_odd_eq_zero_of_even (by simp)

theorem endpointProbability_even_eq_diagonalProductMass_of_even
    {x : Point} (hx : Even (x.1 + x.2)) (n : ℕ) :
    endpointProbability (2 * n) x = diagonalProductMass n
      (firstDiagonalOffset x) (secondDiagonalOffset x) := by
  rw [endpointProbability_even_formula]
  by_cases hfirst : firstDiagonalOffset x ≤ n
  · by_cases hsecond : secondDiagonalOffset x ≤ n
    · rw [if_pos ⟨hx, hfirst, hsecond⟩]
      rfl
    · rw [if_neg (fun h ↦ hsecond h.2.2)]
      symm
      apply diagonalProductMass_eq_zero_of_lt_right
      omega
  · rw [if_neg (fun h ↦ hfirst h.2.1)]
    symm
    apply diagonalProductMass_eq_zero_of_lt_left
    omega

theorem potentialPair_eq_diagonalProductLoss_of_even {x : Point}
    (hx : Even (x.1 + x.2)) (n : ℕ) :
    potentialPair x n = diagonalProductLoss
      (firstDiagonalOffset x) (secondDiagonalOffset x) n := by
  unfold potentialPair potentialTerm diagonalProductLoss
  rw [endpointProbability_even_zero,
    endpointProbability_even_eq_diagonalProductMass_of_even hx,
    endpointProbability_odd_zero,
    endpointProbability_odd_eq_zero_of_even hx,
    diagonalProductMass_center]
  ring

theorem summable_potentialPair_of_even {x : Point} (hx : Even (x.1 + x.2)) :
    Summable (potentialPair x) := by
  apply (summable_diagonalProductLoss (firstDiagonalOffset x)
    (secondDiagonalOffset x)).congr
  intro n
  exact (potentialPair_eq_diagonalProductLoss_of_even hx n).symm

lemma neighbor_even_of_not_even {x : Point} (hx : ¬Even (x.1 + x.2)) (d : Direction) :
    Even ((x - directionVector d).1 + (x - directionVector d).2) := by
  have hxodd : Odd (x.1 + x.2) := Int.not_even_iff_odd.mp hx
  have hdodd : Odd ((directionVector d).1 + (directionVector d).2) := by
    fin_cases d <;> norm_num [directionVector]
  have h := hxodd.sub_odd hdodd
  change Even ((x.1 - (directionVector d).1) + (x.2 - (directionVector d).2))
  have heq : (x.1 - (directionVector d).1) + (x.2 - (directionVector d).2) =
      x.1 + x.2 - ((directionVector d).1 + (directionVector d).2) := by ring
  rw [heq]
  exact h

theorem potentialPair_eq_neighbor_average_of_not_even {x : Point}
    (hx : ¬Even (x.1 + x.2)) (n : ℕ) :
    potentialPair x n = (1 / 4 : ℝ) * ∑ d : Direction,
      potentialPair (x - directionVector d) n := by
  have hneighbor (d : Direction) := neighbor_even_of_not_even hx d
  unfold potentialPair potentialTerm
  rw [endpointProbability_even_eq_zero_of_not_even hx,
    endpointProbability_odd_zero, endpointProbability_succ]
  simp_rw [endpointProbability_odd_eq_zero_of_even (hneighbor _)]
  simp only [sub_zero, add_zero]
  rw [Finset.sum_sub_distrib]
  have hcard : ∑ _d : Direction, endpointProbability (2 * n) 0 =
      4 * endpointProbability (2 * n) 0 := by simp
  rw [hcard]
  ring

theorem summable_potentialPair_of_not_even {x : Point}
    (hx : ¬Even (x.1 + x.2)) : Summable (potentialPair x) := by
  have hneighbors : Summable (fun n : ℕ ↦ ∑ d : Direction,
      potentialPair (x - directionVector d) n) := by
    apply summable_sum
    intro d hd
    exact summable_potentialPair_of_even (neighbor_even_of_not_even hx d)
  have havg := hneighbors.mul_left (1 / 4 : ℝ)
  apply havg.congr
  intro n
  exact (potentialPair_eq_neighbor_average_of_not_even hx n).symm

/-- Absolute summability of the paired potential for every lattice point. -/
theorem summable_potentialPair (x : Point) : Summable (potentialPair x) := by
  by_cases hx : Even (x.1 + x.2)
  · exact summable_potentialPair_of_even hx
  · exact summable_potentialPair_of_not_even hx

theorem planarPotentialKernel_eq_diagonalPotential_of_even {x : Point}
    (hx : Even (x.1 + x.2)) :
    planarPotentialKernel x = diagonalPotential
      (firstDiagonalOffset x) (secondDiagonalOffset x) := by
  unfold planarPotentialKernel diagonalPotential
  apply tsum_congr
  intro n
  exact potentialPair_eq_diagonalProductLoss_of_even hx n


end PotentialConvergence
end Erdos1165
