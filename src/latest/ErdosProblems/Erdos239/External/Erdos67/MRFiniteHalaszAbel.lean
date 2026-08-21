import ErdosProblems.Erdos239.External.Erdos67.LSeriesLogPhaseBridge
import ErdosProblems.Erdos239.External.Erdos67.MRLemma14

/-!
# Abel reduction for the finite Halasz polynomial

The near-frequency input in Appendix A, Proposition A.3 is a bound for the
finite dyadic polynomial on `Re s = 1`.  This file isolates the lossless
finite reduction from raw partial sums of the twisted coefficient.  It does
not replace the Halasz estimate: it records the exact form in which that
estimate is consumed downstream.
-/

open scoped BigOperators
open Finset

namespace Erdos67

noncomputable section

open LSeriesLogPhaseBridge

/-- The raw coefficient whose partial sums feed the finite dyadic Halasz
polynomial.  Membership in `S` is built into the coefficient, so the Abel
summation interval itself remains an ordinary interval. -/
def dyadicHalaszRawCoefficient
    (S : Finset ℕ) (f : ℕ → ℂ) (t : ℝ) (n : ℕ) : ℂ :=
  if n ∈ S then f n * logarithmicPhase n (-t) else 0

/-- The dyadic vertical polynomial is exactly the harmonic Abel transform
of the raw coefficient on `[X+1,2X]`. -/
theorem dyadicVerticalDirichletPolynomial_eq_harmonic_raw
    (S : Finset ℕ) (f : ℕ → ℂ) {X : ℕ} (hX : 0 < X) (t : ℝ) :
    dyadicVerticalDirichletPolynomial S f X t =
      ∑ n ∈ Finset.Icc (X + 1) (2 * X),
        dyadicHalaszRawCoefficient S f t n * (((n : ℝ)⁻¹ : ℝ) : ℂ) := by
  classical
  unfold dyadicVerticalDirichletPolynomial logarithmicDirichletPolynomial
  rw [show dyadicRestrictedSupport S X =
      (Finset.Icc (X + 1) (2 * X)).filter (fun n ↦ n ∈ S) by
    ext n
    simp only [dyadicRestrictedSupport, Finset.mem_inter, Finset.mem_Ioc,
      Finset.mem_filter, Finset.mem_Icc]
    constructor
    · rintro ⟨⟨hlo, hup⟩, hnS⟩
      exact ⟨⟨by omega, hup⟩, hnS⟩
    · rintro ⟨⟨hlo, hup⟩, hnS⟩
      exact ⟨⟨by omega, hup⟩, hnS⟩]
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hnS : n ∈ S
  · simp only [hnS, if_true, dyadicHalaszRawCoefficient]
    rw [div_eq_mul_inv, ← Complex.ofReal_natCast, ← Complex.ofReal_inv]
    ring
  · simp [hnS, dyadicHalaszRawCoefficient]

/-- A uniform raw-prefix bound implies the corresponding finite dyadic
Halasz bound, with the exact left-endpoint harmonic weight. -/
theorem norm_dyadicVerticalDirichletPolynomial_le_of_prefix_bound
    (S : Finset ℕ) (f : ℕ → ℂ) {X : ℕ} (hX : 0 < X)
    (t : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ y ∈ Finset.Icc (X + 1) (2 * X),
      ‖complexIntervalPartialSum
          (dyadicHalaszRawCoefficient S f t) (X + 1) y‖ ≤ B) :
    ‖dyadicVerticalDirichletPolynomial S f X t‖ ≤
      B * ((X + 1 : ℕ) : ℝ)⁻¹ := by
  rw [dyadicVerticalDirichletPolynomial_eq_harmonic_raw S f hX t]
  apply norm_sum_Icc_mul_le_of_prefix_bound
    (dyadicHalaszRawCoefficient S f t) (fun n ↦ ((n : ℝ)⁻¹ : ℝ))
    (by omega) hB
  · positivity
  · intro n hn
    exact inv_anti₀ (by
      have := (Finset.mem_Ico.mp hn).1
      exact_mod_cast (show 0 < n by omega)) (by exact_mod_cast Nat.le_succ n)
  · exact hprefix

/-- A slightly coarser normalization, convenient when a partial-sum theorem
is stated as `B * X`. -/
theorem norm_dyadicVerticalDirichletPolynomial_le_of_prefix_bound_mul
    (S : Finset ℕ) (f : ℕ → ℂ) {X : ℕ} (hX : 0 < X)
    (t : ℝ) {B : ℝ} (hB : 0 ≤ B)
    (hprefix : ∀ y ∈ Finset.Icc (X + 1) (2 * X),
      ‖complexIntervalPartialSum
          (dyadicHalaszRawCoefficient S f t) (X + 1) y‖ ≤ B * X) :
    ‖dyadicVerticalDirichletPolynomial S f X t‖ ≤ B := by
  have hbase := norm_dyadicVerticalDirichletPolynomial_le_of_prefix_bound
    S f hX t (mul_nonneg hB (Nat.cast_nonneg X)) hprefix
  have hXR : (0 : ℝ) < X := by exact_mod_cast hX
  calc
    ‖dyadicVerticalDirichletPolynomial S f X t‖ ≤
        (B * X) * ((X + 1 : ℕ) : ℝ)⁻¹ := hbase
    _ ≤ B := by
      rw [mul_assoc]
      have hratio : (X : ℝ) * ((X + 1 : ℕ) : ℝ)⁻¹ ≤ 1 := by
        rw [← div_eq_mul_inv]
        exact (div_le_one (by positivity)).2 (by norm_num)
      simpa only [mul_one] using mul_le_mul_of_nonneg_left hratio hB

end

end Erdos67
