/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos984.HunterFourier
import Mathlib.Data.Nat.Choose.Central
import Mathlib.Data.Nat.Choose.Sum

/-!
# Coefficients of the product cosine-power kernel

The one-dimensional kernel `cos(πx)^(2k)` has coefficient
`choose (2k) q / 4^k` at frequency `q-k`.  We first establish all positivity,
normalization, and maximal-coefficient facts independently of the analytic
identity with the cosine power.
-/

open scoped BigOperators

namespace Erdos984

noncomputable section

/-- Power of the localized trigonometric kernel. -/
def hunterKernelPower (D : ℕ) : ℕ := D ^ 250

abbrev HunterKernelDigit (k : ℕ) := Fin (2 * k + 1)

/-- Signed frequency represented by a kernel digit. -/
def decodeKernelDigit (k : ℕ) (q : HunterKernelDigit k) : ℤ :=
  (q.val : ℤ) - k

/-- The digit representing frequency zero. -/
def kernelZeroDigit (k : ℕ) : HunterKernelDigit k :=
  ⟨k, by omega⟩

@[simp] lemma decodeKernelDigit_zero (k : ℕ) :
    decodeKernelDigit k (kernelZeroDigit k) = 0 := by
  simp [decodeKernelDigit, kernelZeroDigit]

/-- One-dimensional Fourier coefficient of the cosine-power kernel. -/
def kernelDigitCoeff (k : ℕ) (q : HunterKernelDigit k) : ℝ :=
  (Nat.choose (2 * k) q.val : ℝ) / (4 : ℝ) ^ k

/-- Product coefficient in dimension `D`. -/
def kernelCoeff {D : Type*} [Fintype D] (k : ℕ)
    (q : D → HunterKernelDigit k) : ℝ :=
  ∏ j, kernelDigitCoeff k (q j)

/-- Frequency vector decoded from a product digit. -/
def kernelFrequency {D : Type*} (k : ℕ)
    (q : D → HunterKernelDigit k) : D → ℤ :=
  fun j ↦ decodeKernelDigit k (q j)

lemma kernelDigitCoeff_nonneg (k : ℕ) (q : HunterKernelDigit k) :
    0 ≤ kernelDigitCoeff k q := by
  unfold kernelDigitCoeff
  positivity

lemma kernelCoeff_nonneg {D : Type*} [Fintype D] (k : ℕ)
    (q : D → HunterKernelDigit k) : 0 ≤ kernelCoeff k q := by
  exact Finset.prod_nonneg fun _ _ ↦ kernelDigitCoeff_nonneg _ _

lemma sum_choose_two_mul (k : ℕ) :
    ∑ q : Fin (2 * k + 1), Nat.choose (2 * k) q.val = 4 ^ k := by
  rw [Fin.sum_univ_eq_sum_range, Nat.sum_range_choose]
  rw [show 4 ^ k = (2 ^ 2) ^ k by norm_num, ← pow_mul]

lemma sum_kernelDigitCoeff (k : ℕ) :
    ∑ q : HunterKernelDigit k, kernelDigitCoeff k q = 1 := by
  unfold kernelDigitCoeff
  rw [← Finset.sum_div]
  rw [← Nat.cast_sum, sum_choose_two_mul]
  push_cast
  field_simp

lemma sum_kernelCoeff {D : Type*} [Fintype D] [DecidableEq D] (k : ℕ) :
    ∑ q : D → HunterKernelDigit k, kernelCoeff k q = 1 := by
  unfold kernelCoeff
  rw [← Fintype.prod_sum]
  simp [sum_kernelDigitCoeff]

/-- The zero-frequency coefficient in one dimension. -/
def kernelMean1 (k : ℕ) : ℝ :=
  (Nat.centralBinom k : ℝ) / (4 : ℝ) ^ k

@[simp] lemma kernelDigitCoeff_zero (k : ℕ) :
    kernelDigitCoeff k (kernelZeroDigit k) = kernelMean1 k := by
  simp [kernelDigitCoeff, kernelZeroDigit, kernelMean1, Nat.centralBinom]

lemma kernelMean1_pos (k : ℕ) : 0 < kernelMean1 k := by
  unfold kernelMean1
  exact div_pos (Nat.cast_pos.2 (Nat.centralBinom_pos k)) (by positivity)

lemma kernelDigitCoeff_le_mean (k : ℕ) (q : HunterKernelDigit k) :
    kernelDigitCoeff k q ≤ kernelMean1 k := by
  unfold kernelDigitCoeff kernelMean1
  exact div_le_div_of_nonneg_right
    (by exact_mod_cast Nat.choose_le_centralBinom q.val k) (by positivity)

lemma one_div_two_mul_add_one_le_kernelMean1 (k : ℕ) :
    (1 : ℝ) / (2 * k + 1) ≤ kernelMean1 k := by
  have hnat := Nat.four_pow_le_two_mul_add_one_mul_central_binom k
  have hreal : (4 : ℝ) ^ k ≤
      (2 * k + 1 : ℕ) * (Nat.centralBinom k : ℕ) := by
    exact_mod_cast hnat
  rw [kernelMean1]
  push_cast at hreal ⊢
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  simpa [mul_comm] using hreal

lemma kernelFrequency_bound {D : Type*} (k : ℕ)
    (q : D → HunterKernelDigit k) (j : D) :
    |kernelFrequency k q j| ≤ k := by
  simp only [kernelFrequency, decodeKernelDigit]
  rw [abs_le]
  constructor <;> omega

lemma hunterKernelPower_pos {D : ℕ} (hD : 0 < D) :
    0 < hunterKernelPower D := by
  exact pow_pos hD _

lemma hunterKernelPower_le_frequencyBound (D : ℕ) (hD : 0 < D) :
    hunterKernelPower D ≤ hunterFrequencyBound D := by
  rw [hunterKernelPower, hunterFrequencyBound,
    show 300 = 250 + 50 by omega, pow_add]
  exact Nat.le_mul_of_pos_right _ (pow_pos hD 50)

end

end Erdos984
