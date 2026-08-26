import ErdosProblems.Erdos327.Analytic.WeightedLinearSieveBoundarySharp

/-!
# An elementary geometric bound for the Bonferroni factorial tail

The finite sieve produces `μ^(2R+1)/(2R+1)!`.  Taking `R` larger than a
constant multiple of `μ²` makes this tail geometrically small.  The proof
uses only the elementary factorial lower bound already in Mathlib.
-/

namespace Erdos327.Analytic

open Real

/-- The last `R` factors in `(2R)!` already contribute at least `R^R`. -/
theorem pow_le_factorial_two_mul (R : ℕ) :
    R ^ R ≤ (2 * R).factorial := by
  have h :=
    Nat.factorial_mul_pow_sub_le_factorial
      (n := R) (m := 2 * R) (by omega)
  have hfac : 1 ≤ R.factorial := Nat.factorial_pos R
  have hpow :
      R ^ R ≤ R.factorial * R ^ R :=
    Nat.le_mul_of_pos_left _ hfac
  calc
    R ^ R ≤ R.factorial * R ^ R := hpow
    _ = R.factorial * R ^ (2 * R - R) := by
      congr 2
      omega
    _ ≤ (2 * R).factorial := h

/-- Real-cast form of `pow_le_factorial_two_mul`. -/
theorem pow_le_factorial_two_mul_real (R : ℕ) :
    (R : ℝ) ^ R ≤ ((2 * R).factorial : ℝ) := by
  exact_mod_cast pow_le_factorial_two_mul R

/-- If `μ ≤ R` and `μ² ≤ R/4`, the odd factorial tail is at most
`4⁻ᴿ`.  This form is tailored to the `2R+1` Bonferroni truncation. -/
theorem pow_div_factorial_two_mul_add_one_le
    {μ : ℝ} {R : ℕ}
    (hμ0 : 0 ≤ μ) (hR : 1 ≤ R)
    (hμR : μ ≤ R) (hμsq : μ ^ 2 ≤ (R : ℝ) / 4) :
    μ ^ (2 * R + 1) / ((2 * R + 1).factorial : ℝ) ≤
      (1 / 4 : ℝ) ^ R := by
  have hR0 : (0 : ℝ) < R := by exact_mod_cast hR
  have htwoRfac0 : (0 : ℝ) < ((2 * R).factorial : ℝ) := by
    exact_mod_cast Nat.factorial_pos (2 * R)
  have hsucc0 : (0 : ℝ) < ((2 * R + 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < 2 * R + 1 by omega)
  have hμsucc : μ / (2 * R + 1 : ℕ) ≤ 1 := by
    apply (div_le_one₀ hsucc0).mpr
    exact hμR.trans (by exact_mod_cast (show R ≤ 2 * R + 1 by omega))
  have hpowEven :
      μ ^ (2 * R) = (μ ^ 2) ^ R := by
    rw [← pow_mul]
  have hnum :
      μ ^ (2 * R) ≤ ((R : ℝ) / 4) ^ R := by
    rw [hpowEven]
    exact pow_le_pow_left₀ (sq_nonneg μ) hμsq R
  have hfactorial :
      (R : ℝ) ^ R ≤ ((2 * R).factorial : ℝ) :=
    pow_le_factorial_two_mul_real R
  have hRpow0 : 0 < (R : ℝ) ^ R := pow_pos hR0 R
  have heven :
      μ ^ (2 * R) / ((2 * R).factorial : ℝ) ≤
        (1 / 4 : ℝ) ^ R := by
    calc
      μ ^ (2 * R) / ((2 * R).factorial : ℝ) ≤
          ((R : ℝ) / 4) ^ R /
            ((2 * R).factorial : ℝ) :=
        div_le_div_of_nonneg_right hnum htwoRfac0.le
      _ ≤ ((R : ℝ) / 4) ^ R / (R : ℝ) ^ R := by
        exact div_le_div_of_nonneg_left
          (by positivity) hRpow0 hfactorial
      _ = (1 / 4 : ℝ) ^ R := by
        rw [← div_pow]
        congr 1
        field_simp [hR0.ne']
  have hrewrite :
      μ ^ (2 * R + 1) / ((2 * R + 1).factorial : ℝ) =
        (μ / (2 * R + 1 : ℕ)) *
          (μ ^ (2 * R) / ((2 * R).factorial : ℝ)) := by
    rw [pow_succ, Nat.factorial_succ]
    push_cast
    field_simp
  rw [hrewrite]
  exact (mul_le_mul hμsucc heven
    (by positivity) (by norm_num)).trans (by simp)

end Erdos327.Analytic
