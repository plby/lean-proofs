/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierRelativeComparison

/-!
# The generic and exceptional parts of the singular Euler factor

The generic factor differs from one quadratically. The exceptional
integer count contributes a separate first-order term. It can only
increase the nonnegative real singular factor at a sufficiently large
prime.
-/

namespace Erdos4b

noncomputable section

theorem norm_zeroExponentSingularFactor_sub_one_le
    (n : ℕ) {p : ℝ} (hp : 2 ≤ p) (hcard : 7 * (n : ℝ) ≤ p) (D : ℂ) :
    ‖(1 - ((n : ℂ) - D) / (p : ℂ)) / (1 - 1 / (p : ℂ)) ^ n - 1‖ ≤
      (2 : ℝ) ^ n * (pairProductErrorConstant n / p ^ 2 + ‖D‖ / p) := by
  have hp0 : 0 < p := by linarith
  have hC := pairProductErrorConstant_nonneg n
  have hlow := pow_half_le_norm_zeroExponentPairProduct n hp
  have hdenpos : 0 < ‖(1 - 1 / (p : ℂ)) ^ n‖ := lt_of_lt_of_le (by positivity) hlow
  have hden0 : (1 - 1 / (p : ℂ)) ^ n ≠ 0 := norm_pos_iff.mp hdenpos
  have hbase : ‖(1 - (n : ℂ) / p) - (1 - 1 / (p : ℂ)) ^ n‖ ≤
      pairProductErrorConstant n / p ^ 2 := by
    simpa only [Finset.card_range, norm_sub_rev] using
      norm_zeroExponentPairProduct_error_le (Finset.range n) hp
        (by simpa only [Finset.card_range] using hcard)
  have hnum : ‖(1 - ((n : ℂ) - D) / p) - (1 - 1 / (p : ℂ)) ^ n‖ ≤
      pairProductErrorConstant n / p ^ 2 + ‖D‖ / p := by
    rw [show (1 - ((n : ℂ) - D) / p) - (1 - 1 / (p : ℂ)) ^ n =
      ((1 - (n : ℂ) / p) - (1 - 1 / (p : ℂ)) ^ n) + D / p by ring]
    have hD : ‖D / (p : ℂ)‖ = ‖D‖ / p := by
      rw [norm_div, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hp0]
    exact (norm_add_le _ _).trans (by rw [hD]; exact add_le_add hbase le_rfl)
  rw [show (1 - ((n : ℂ) - D) / p) / (1 - 1 / (p : ℂ)) ^ n - 1 =
      ((1 - ((n : ℂ) - D) / p) - (1 - 1 / (p : ℂ)) ^ n) /
        (1 - 1 / (p : ℂ)) ^ n by
      conv_rhs => rw [sub_div, div_self hden0], norm_div]
  calc
    _ ≤ (pairProductErrorConstant n / p ^ 2 + ‖D‖ / p) /
        ‖(1 - 1 / (p : ℂ)) ^ n‖ := div_le_div_of_nonneg_right hnum hdenpos.le
    _ ≤ (pairProductErrorConstant n / p ^ 2 + ‖D‖ / p) / (1 / 2 : ℝ) ^ n :=
      div_le_div_of_nonneg_left (by positivity) (by positivity) hlow
    _ = _ := by rw [div_eq_mul_inv, ← inv_pow]; norm_num; ring

theorem norm_doubledFourierSingularFactor_sub_one_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p : ℕ} (hp : 2 ≤ (p : ℝ)) (hcard : 7 * (Fintype.card (ι ⊕ ι) : ℝ) ≤ p) :
    ‖doubledFourierSingularFactor edges companion p - 1‖ ≤
      (2 : ℝ) ^ Fintype.card (ι ⊕ ι) *
        (pairProductErrorConstant (Fintype.card (ι ⊕ ι)) / (p : ℝ) ^ 2 +
          (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℝ) / p) := by
  simpa only [Complex.norm_natCast, Complex.ofReal_natCast, doubledFourierSingularFactor] using
    norm_zeroExponentSingularFactor_sub_one_le (Fintype.card (ι ⊕ ι)) hp hcard
      (doubledFourierExceptionalCount Finset.univ (edges p) (companion p) : ℂ)

def genericFourierSingularFactor (n : ℕ) (p : ℕ) : ℂ :=
  (1 - (n : ℂ) / p) / (1 - 1 / (p : ℂ)) ^ n

theorem doubledFourierSingularFactor_eq_ofReal
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool) (p : ℕ) :
    doubledFourierSingularFactor edges companion p =
      (((1 - ((Fintype.card (ι ⊕ ι) : ℝ) -
        doubledFourierExceptionalCount Finset.univ (edges p) (companion p)) / p) /
        (1 - 1 / (p : ℝ)) ^ Fintype.card (ι ⊕ ι) : ℝ) : ℂ) := by
  push_cast
  rfl

theorem genericFourierSingularFactor_eq_ofReal (n p : ℕ) :
    genericFourierSingularFactor n p =
      (((1 - (n : ℝ) / p) / (1 - 1 / (p : ℝ)) ^ n : ℝ) : ℂ) := by
  push_cast
  rfl

theorem norm_genericFourierSingularFactor_le
    {ι : Type*} [Fintype ι] (edges : ℕ → Finset (ι × ι)) (companion : ℕ → Bool)
    {p : ℕ} (hp : 2 ≤ (p : ℝ)) (hcard : (Fintype.card (ι ⊕ ι) : ℝ) ≤ p) :
    ‖genericFourierSingularFactor (Fintype.card (ι ⊕ ι)) p‖ ≤
      ‖doubledFourierSingularFactor edges companion p‖ := by
  have hp0 : (0 : ℝ) < p := by linarith
  have hNp : (Fintype.card (ι ⊕ ι) : ℝ) / p ≤ 1 := (div_le_one hp0).mpr hcard
  have hD : (0 : ℝ) ≤ doubledFourierExceptionalCount Finset.univ (edges p) (companion p) :=
    Nat.cast_nonneg _
  have hnum : 1 - (Fintype.card (ι ⊕ ι) : ℝ) / p ≤
      1 - ((Fintype.card (ι ⊕ ι) : ℝ) -
        doubledFourierExceptionalCount Finset.univ (edges p) (companion p)) / p := by
    exact sub_le_sub_left (div_le_div_of_nonneg_right (sub_le_self _ hD) hp0.le) 1
  have hden : 0 ≤ (1 - 1 / (p : ℝ)) ^ Fintype.card (ι ⊕ ι) := by
    apply pow_nonneg
    have hrec : (1 : ℝ) / p ≤ 1 := (div_le_one hp0).mpr (by linarith)
    linarith
  have hgen0 := div_nonneg (sub_nonneg.mpr hNp) hden
  have hactual0 := div_nonneg ((sub_nonneg.mpr hNp).trans hnum) hden
  rw [genericFourierSingularFactor_eq_ofReal, doubledFourierSingularFactor_eq_ofReal,
    Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
    abs_of_nonneg hgen0, abs_of_nonneg hactual0]
  exact div_le_div_of_nonneg_right hnum hden

end

end Erdos4b
