import ErdosProblems.Erdos4.RestrictedProductNorm
import Mathlib.Analysis.Complex.Basic

/-!
# Norm-sensitive bounds for coefficient slices

The estimates retain the exact squared coefficient norm. In particular,
their constants do not contain a crude count of divisor coefficients.
-/

open scoped BigOperators

namespace Erdos4.SliceBounds

open ProductOrthogonality RestrictedProductNorm

variable {P : Type*} [Fintype P] [DecidableEq P] {k : ℕ}

theorem energy_le_of_pointwise (v w : (P → Option (Fin k)) → ℝ) {c : ℝ}
    (hc : 0 ≤ c) (hvw : ∀ a, |v a| ≤ c * |w a|) : energy v ≤ c ^ 2 * energy w := by
  unfold energy
  rw [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro a _ha
  have hh := (sq_le_sq₀ (abs_nonneg (v a)) (mul_nonneg hc (abs_nonneg (w a)))).mpr (hvw a)
  simpa only [mul_pow, sq_abs] using hh

theorem slice_energy_le_total {A : Type*} [Fintype A]
    (v : A → (P → Option (Fin k)) → ℝ) (base : A) (c : A → ℝ)
    (hc : ∀ a, 0 ≤ c a) (hv : ∀ a x, |v a x| ≤ c a * |v base x|) (a : A) :
    energy (v a) ≤ c a ^ 2 * ∑ b, energy (v b) := by
  have hbase : energy (v base) ≤ ∑ b, energy (v b) :=
    Finset.single_le_sum (fun b _hb => energy_nonneg (v b)) (Finset.mem_univ base)
  exact (energy_le_of_pointwise (v a) (v base) (hc a) (hv a)).trans
    (mul_le_mul_of_nonneg_left hbase (sq_nonneg _))

theorem abs_restrictedForm_le_scaled_energy
    (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask0 : ∀ s, 0 ≤ mask s)
    (hmask1 : ∀ s, mask s ≤ 1) (v w : (P → Option (Fin k)) → ℝ)
    {a b N : ℝ} (ha : 0 ≤ a) (hb : 0 ≤ b) (hN : 0 ≤ N)
    (hv : energy v ≤ a ^ 2 * N) (hw : energy w ≤ b ^ 2 * N) :
    |restrictedForm ell mask v w| ≤ a * b * N := by
  have hsq := restrictedForm_sq_le_energy ell hell mask hmask0 hmask1 v w
  have hprod := mul_le_mul hv hw (energy_nonneg w) (mul_nonneg (sq_nonneg a) hN)
  have hrhs : (a ^ 2 * N) * (b ^ 2 * N) = (a * b * N) ^ 2 := by ring
  rw [hrhs] at hprod
  have hpositive : 0 ≤ a * b * N := mul_nonneg (mul_nonneg ha hb) hN
  have hh := hsq.trans hprod
  exact abs_le.mpr ⟨by nlinarith, by nlinarith⟩

/-- A local complex matrix can be bounded after contracting the untouched
prime coordinates, using the coefficient-slice bounds alone. -/
theorem norm_matrix_slice_sum_le {A : Type*} [Fintype A]
    (ell : P → ℝ) (hell : ∀ p, (k : ℝ) < ell p)
    (mask : (P → Option (Fin k)) → ℝ) (hmask0 : ∀ s, 0 ≤ mask s)
    (hmask1 : ∀ s, mask s ≤ 1)
    (v : A → (P → Option (Fin k)) → ℝ) (c : A → ℝ) (M : A → A → ℂ)
    {N : ℝ} (hN : 0 ≤ N) (hc : ∀ a, 0 ≤ c a)
    (hv : ∀ a, energy (v a) ≤ c a ^ 2 * N) :
    ‖∑ a, ∑ b, M a b * (restrictedForm ell mask (v a) (v b) : ℂ)‖ ≤
      N * ∑ a, ∑ b, ‖M a b‖ * c a * c b := by
  have hterm : ∀ a b, ‖M a b * (restrictedForm ell mask (v a) (v b) : ℂ)‖ ≤
      N * (‖M a b‖ * c a * c b) := by
    intro a b
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    have hh := abs_restrictedForm_le_scaled_energy ell hell mask hmask0 hmask1
      (v a) (v b) (hc a) (hc b) hN (hv a) (hv b)
    have hmul := mul_le_mul_of_nonneg_left hh (norm_nonneg (M a b))
    calc
      ‖M a b‖ * |restrictedForm ell mask (v a) (v b)| ≤ ‖M a b‖ * (c a * c b * N) := hmul
      _ = N * (‖M a b‖ * c a * c b) := by ring
  calc
    ‖∑ a, ∑ b, M a b * (restrictedForm ell mask (v a) (v b) : ℂ)‖ ≤
        ∑ a, ∑ b, ‖M a b * (restrictedForm ell mask (v a) (v b) : ℂ)‖ :=
      (norm_sum_le _ _).trans (Finset.sum_le_sum (fun a _ha => norm_sum_le _ _))
    _ ≤ ∑ a, ∑ b, N * (‖M a b‖ * c a * c b) :=
      Finset.sum_le_sum (fun a _ha => Finset.sum_le_sum (fun b _hb => hterm a b))
    _ = N * ∑ a, ∑ b, ‖M a b‖ * c a * c b := by simp_rw [Finset.mul_sum]

theorem sum_sum_product {J A : Type*} [Fintype J] [DecidableEq J] [Fintype A]
    (f : J → A → A → ℝ) :
    (∑ a : J → A, ∑ b : J → A, ∏ j, f j (a j) (b j)) =
      ∏ j, ∑ a : A, ∑ b : A, f j a b := by
  have hinner : ∀ a : J → A, (∑ b : J → A, ∏ j, f j (a j) (b j)) =
      ∏ j, ∑ b : A, f j (a j) b := by
    intro a
    exact (Fintype.prod_sum (fun j b => f j (a j) b)).symm
  simp_rw [hinner]
  exact (Fintype.prod_sum (fun j a => ∑ b : A, f j a b)).symm

end Erdos4.SliceBounds
