import ErdosProblems.Erdos788.TrevisanParameters
import ErdosProblems.Erdos788.Statement
import Mathlib.NumberTheory.Bertrand

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Prime and dimension choices for every interval length

The field size is selected by Bertrand's postulate.  The ambient dimension is
an integral ceiling logarithm, so coverage of the first `N` vertices is an
exact natural-number inequality.
-/

namespace Erdos788

/-- The nonnegative reciprocal-correction scale. -/
noncomputable def inverseCorrectionScale (N : ℕ) : ℝ :=
  max 0 (exponentCorrection N)⁻¹

/-- We add `log log N`, a lower-order term, to make the later comparison
`log r ≤ log p` completely transparent. -/
noncomputable def primeLogScale (N : ℕ) : ℝ :=
  inverseCorrectionScale N + max 0 (Real.log (Real.log (N : ℝ)))

theorem exponentCorrection_pos {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    0 < exponentCorrection N := by
  rw [exponentCorrection]
  exact Real.rpow_pos_of_pos (div_pos hLL hL) _

theorem exponentCorrection_pow_three {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    exponentCorrection N ^ 3 =
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) := by
  rw [exponentCorrection]
  have hbase : 0 ≤
      Real.log (Real.log (N : ℝ)) / Real.log (N : ℝ) :=
    (div_pos hLL hL).le
  simpa [one_div] using!
    (Real.rpow_inv_natCast_pow hbase (by norm_num : (3 : ℕ) ≠ 0))

theorem correction_mul_inverseCorrectionScale {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    exponentCorrection N * inverseCorrectionScale N = 1 := by
  have hδ := exponentCorrection_pos hL hLL
  rw [inverseCorrectionScale, max_eq_right (inv_nonneg.mpr hδ.le), mul_inv_cancel₀]
  exact hδ.ne'

/-- Integral threshold to which Bertrand's postulate is applied. -/
noncomputable def primeThreshold (N : ℕ) : ℕ :=
  max 2 ⌈Real.exp (primeLogScale N)⌉₊

theorem two_le_primeThreshold (N : ℕ) : 2 ≤ primeThreshold N := by
  simp [primeThreshold]

theorem primeThreshold_ne_zero (N : ℕ) : primeThreshold N ≠ 0 := by
  exact Nat.ne_of_gt (lt_of_lt_of_le (by omega) (two_le_primeThreshold N))

/-- A deterministic prime between the threshold and twice the threshold. -/
noncomputable def parameterPrime (N : ℕ) : ℕ :=
  Classical.choose
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))

theorem parameterPrime_prime (N : ℕ) : (parameterPrime N).Prime :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).1

theorem primeThreshold_lt_parameterPrime (N : ℕ) :
    primeThreshold N < parameterPrime N :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).2.1

theorem parameterPrime_le_two_mul_threshold (N : ℕ) :
    parameterPrime N ≤ 2 * primeThreshold N :=
  (Classical.choose_spec
    (Nat.exists_prime_lt_and_le_two_mul
      (primeThreshold N) (primeThreshold_ne_zero N))).2.2

theorem two_lt_parameterPrime (N : ℕ) : 2 < parameterPrime N :=
  (two_le_primeThreshold N).trans_lt (primeThreshold_lt_parameterPrime N)

theorem primeLogScale_nonneg (N : ℕ) : 0 ≤ primeLogScale N := by
  rw [primeLogScale]
  exact add_nonneg (le_max_left _ _) (le_max_left _ _)

theorem cast_primeThreshold_le_two_mul_exp (N : ℕ) :
    (primeThreshold N : ℝ) ≤ 2 * Real.exp (primeLogScale N) := by
  have hexp1 : (1 : ℝ) ≤ Real.exp (primeLogScale N) :=
    Real.one_le_exp (primeLogScale_nonneg N)
  have hceil : (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) ≤
      2 * Real.exp (primeLogScale N) := by
    have h : (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) <
        Real.exp (primeLogScale N) + 1 :=
      Nat.ceil_lt_add_one (Real.exp_pos (primeLogScale N)).le
    nlinarith
  rw [primeThreshold, Nat.cast_max]
  apply max_le
  · simpa using!
      (mul_le_mul_of_nonneg_left hexp1 (by norm_num : (0 : ℝ) ≤ 2))
  · exact hceil

theorem cast_parameterPrime_le_four_mul_exp (N : ℕ) :
    (parameterPrime N : ℝ) ≤ 4 * Real.exp (primeLogScale N) := by
  have hp : (parameterPrime N : ℝ) ≤ 2 * primeThreshold N := by
    exact_mod_cast parameterPrime_le_two_mul_threshold N
  have hP := cast_primeThreshold_le_two_mul_exp N
  nlinarith

theorem primeLogScale_lt_log_parameterPrime (N : ℕ) :
    primeLogScale N < Real.log (parameterPrime N) := by
  have hexpP : Real.exp (primeLogScale N) ≤ (primeThreshold N : ℝ) := by
    calc
      Real.exp (primeLogScale N) ≤
          (⌈Real.exp (primeLogScale N)⌉₊ : ℝ) := Nat.le_ceil _
      _ ≤ (primeThreshold N : ℝ) := by
        exact_mod_cast (le_max_right 2 ⌈Real.exp (primeLogScale N)⌉₊)
  have hPp : (primeThreshold N : ℝ) < parameterPrime N := by
    exact_mod_cast primeThreshold_lt_parameterPrime N
  have hlog := Real.log_lt_log (Real.exp_pos _) (hexpP.trans_lt hPp)
  simpa using! hlog

theorem log_parameterPrime_le_scale_add_log_four (N : ℕ) :
    Real.log (parameterPrime N) ≤ primeLogScale N + Real.log 4 := by
  have hp0 : (0 : ℝ) < parameterPrime N := by
    exact_mod_cast (Nat.zero_lt_of_lt (two_lt_parameterPrime N))
  have hupper := cast_parameterPrime_le_four_mul_exp N
  have hlog := Real.log_le_log hp0 hupper
  rw [Real.log_mul (by norm_num : (4 : ℝ) ≠ 0) (Real.exp_ne_zero _),
    Real.log_exp] at hlog
  linarith

theorem loglog_le_log_parameterPrime (N : ℕ) :
    Real.log (Real.log (N : ℝ)) ≤ Real.log (parameterPrime N) := by
  have hscale : Real.log (Real.log (N : ℝ)) ≤ primeLogScale N := by
    rw [primeLogScale]
    calc
      Real.log (Real.log (N : ℝ)) ≤
          max 0 (Real.log (Real.log (N : ℝ))) := le_max_right _ _
      _ ≤ inverseCorrectionScale N +
          max 0 (Real.log (Real.log (N : ℝ))) :=
        le_add_of_nonneg_left (le_max_left _ _)
  exact hscale.trans (primeLogScale_lt_log_parameterPrime N).le

theorem log_parameterPrime_le_two_div_correction {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ)))
    (hsmall : exponentCorrection N *
        (Real.log (Real.log (N : ℝ)) + Real.log 4) ≤ 1) :
    Real.log (parameterPrime N) ≤ 2 / exponentCorrection N := by
  have hδ := exponentCorrection_pos hL hLL
  have hbase := log_parameterPrime_le_scale_add_log_four N
  rw [primeLogScale, inverseCorrectionScale,
    max_eq_right (inv_nonneg.mpr hδ.le), max_eq_right hLL.le] at hbase
  have hinv : exponentCorrection N * (exponentCorrection N)⁻¹ = 1 :=
    mul_inv_cancel₀ hδ.ne'
  have haux : (exponentCorrection N)⁻¹ +
      Real.log (Real.log (N : ℝ)) + Real.log 4 ≤
        2 / exponentCorrection N := by
    rw [div_eq_mul_inv]
    nlinarith
  exact hbase.trans haux

theorem one_div_log_parameterPrime_lt_correction {N : ℕ}
    (hL : 0 < Real.log (N : ℝ))
    (hLL : 0 < Real.log (Real.log (N : ℝ))) :
    1 / Real.log (parameterPrime N) < exponentCorrection N := by
  have hδ : 0 < exponentCorrection N := exponentCorrection_pos hL hLL
  have hinv : (exponentCorrection N)⁻¹ ≤ primeLogScale N := by
    rw [primeLogScale, inverseCorrectionScale,
      max_eq_right (inv_nonneg.mpr hδ.le)]
    exact le_add_of_nonneg_right (le_max_left _ _)
  have hinvpos : 0 < (exponentCorrection N)⁻¹ := inv_pos.mpr hδ
  have hinvlog : (exponentCorrection N)⁻¹ <
      Real.log (parameterPrime N) :=
    hinv.trans_lt (primeLogScale_lt_log_parameterPrime N)
  have h' := one_div_lt_one_div_of_lt hinvpos hinvlog
  simpa [one_div] using! h'

noncomputable instance parameterPrimeFact (N : ℕ) :
    Fact (parameterPrime N).Prime :=
  ⟨parameterPrime_prime N⟩

/-- Least `r` for which the `p^(2r)`-vertex finite-field model covers `N`. -/
noncomputable def parameterDimension (N : ℕ) : ℕ :=
  Nat.clog ((parameterPrime N) ^ 2) N

theorem parameterDimension_cover (N : ℕ) :
    N ≤ parameterPrime N ^ (2 * parameterDimension N) := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  have hbase : 1 < parameterPrime N ^ 2 := by
    exact Nat.one_lt_pow (by norm_num) hp1
  have h := Nat.le_pow_clog hbase N
  simpa [parameterDimension, pow_mul] using! h

theorem parameterDimension_pos {N : ℕ} (hN : 1 < N) :
    0 < parameterDimension N := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  apply Nat.clog_pos
  · exact Nat.one_lt_pow (by norm_num) hp1
  · exact hN

/-- The exact real ceiling bound for the chosen dimension. -/
theorem cast_parameterDimension_lt_logb_add_one {N : ℕ} (hN : 1 ≤ N) :
    ((parameterDimension N : ℕ) : ℝ) <
      Real.logb (parameterPrime N ^ 2) N + 1 := by
  have hp1 : 1 < parameterPrime N :=
    (by omega : 1 < 2).trans (two_lt_parameterPrime N)
  have hbase : 1 < parameterPrime N ^ 2 :=
    Nat.one_lt_pow (by norm_num) hp1
  simpa [parameterDimension, Nat.cast_pow] using!
    (cast_clog_lt_logb_add_one
      (b := parameterPrime N ^ 2) (n := N) hbase hN)

theorem cast_parameterDimension_lt_log_div_add_one {N : ℕ} (hN : 1 ≤ N) :
    ((parameterDimension N : ℕ) : ℝ) <
      Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) + 1 := by
  have h := cast_parameterDimension_lt_logb_add_one hN
  rw [Real.logb] at h
  norm_num [Nat.cast_pow, Real.log_pow] at h ⊢
  exact h

theorem log_div_le_cast_parameterDimension {N : ℕ} (hN : 0 < N) :
    Real.log (N : ℝ) / (2 * Real.log (parameterPrime N)) ≤
      (parameterDimension N : ℝ) := by
  have hpR : (1 : ℝ) < parameterPrime N := by
    exact_mod_cast ((by omega : 1 < 2).trans (two_lt_parameterPrime N))
  have hden : 0 < 2 * Real.log (parameterPrime N) := by
    exact mul_pos (by norm_num) (Real.log_pos hpR)
  have hcoverR : (N : ℝ) ≤
      (parameterPrime N ^ (2 * parameterDimension N) : ℕ) := by
    exact_mod_cast parameterDimension_cover N
  have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
  have hlog := Real.log_le_log hNreal hcoverR
  rw [Nat.cast_pow, Real.log_pow] at hlog
  apply (div_le_iff₀ hden).2
  push_cast at hlog ⊢
  nlinarith

end Erdos788
