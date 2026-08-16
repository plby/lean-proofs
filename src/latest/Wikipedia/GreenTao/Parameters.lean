import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecificLimits.Basic

/-!
# Quantitative parameters for the Green--Tao argument

This file fixes deliberately coarse constants for the sieve and
transference layers.  The important feature is their dependency order:
`maxAPForms`, `sieveExponent`, and `primeScale` depend only on the
progression length (and the fixed smooth-cutoff normalizer), while
`sieveLevel` is the first parameter that depends on the cyclic modulus.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Real

/-- A coarse upper bound for the number of affine-linear forms occurring
in any Boolean expansion of a `k`-term progression system. -/
def maxAPForms (k : ℕ) : ℕ :=
  k * 2 ^ (k - 1)

/-- The small power of the cyclic modulus used as the sieve level. -/
noncomputable def sieveExponent (k : ℕ) : ℝ :=
  (100 * maxAPForms k : ℝ)⁻¹

/-- The truncated-divisor-sum level. -/
noncomputable def sieveLevel (k N : ℕ) : ℕ :=
  ⌊(N : ℝ) ^ sieveExponent k⌋₊

/-- The absolute constant supplied by the quarter-interval Chebyshev
lower bound. -/
noncomputable def primeIntervalConstant : ℝ :=
  log 2 / 4

/-- A fixed scaling of the W-tricked von Mangoldt weight.  The second
term in the minimum reserves ample exponent room for majorization. -/
noncomputable def primeScale (k : ℕ)
    (cutoffNormalizer : ℝ) : ℝ :=
  min (1 / 2)
    (sieveExponent k / (8 * cutoffNormalizer))

/-- The fixed density passed to relative Szemerédi.  It is chosen before
the W-trick cutoff and cyclic modulus. -/
noncomputable def densityTarget (k : ℕ)
    (cutoffNormalizer : ℝ) : ℝ :=
  min (1 / 2)
    (primeScale k cutoffNormalizer * primeIntervalConstant / 100)

theorem maxAPForms_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < maxAPForms k := by
  exact Nat.mul_pos (by omega) (pow_pos (by norm_num) _)

theorem sieveExponent_pos {k : ℕ} (hk : 3 ≤ k) :
    0 < sieveExponent k := by
  rw [sieveExponent]
  apply inv_pos.mpr
  exact_mod_cast
    Nat.mul_pos (by norm_num) (maxAPForms_pos hk)

theorem primeIntervalConstant_pos :
    0 < primeIntervalConstant := by
  rw [primeIntervalConstant]
  exact div_pos (log_pos (by norm_num)) (by norm_num)

theorem primeScale_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < primeScale k cutoffNormalizer := by
  rw [primeScale]
  exact lt_min (by norm_num)
    (div_pos (sieveExponent_pos hk)
      (mul_pos (by norm_num) hnorm))

theorem primeScale_nonneg {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 ≤ primeScale k cutoffNormalizer :=
  (primeScale_pos hk hnorm).le

theorem primeScale_le_half (k : ℕ) (cutoffNormalizer : ℝ) :
    primeScale k cutoffNormalizer ≤ 1 / 2 := by
  exact min_le_left _ _

theorem primeScale_le_sieveExponent_div
    (k : ℕ) (cutoffNormalizer : ℝ) :
    primeScale k cutoffNormalizer ≤
      sieveExponent k / (8 * cutoffNormalizer) := by
  exact min_le_right _ _

theorem densityTarget_pos {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    0 < densityTarget k cutoffNormalizer := by
  rw [densityTarget]
  exact lt_min (by norm_num)
    (div_pos
      (mul_pos (primeScale_pos hk hnorm)
        primeIntervalConstant_pos)
      (by norm_num))

theorem densityTarget_le_half
    (k : ℕ) (cutoffNormalizer : ℝ) :
    densityTarget k cutoffNormalizer ≤ 1 / 2 := by
  exact min_le_left _ _

theorem densityTarget_le_one
    (k : ℕ) (cutoffNormalizer : ℝ) :
    densityTarget k cutoffNormalizer ≤ 1 :=
  (densityTarget_le_half k cutoffNormalizer).trans (by norm_num)

theorem densityTarget_le_primeScale_mul_interval
    (k : ℕ) (cutoffNormalizer : ℝ) :
    densityTarget k cutoffNormalizer ≤
      primeScale k cutoffNormalizer *
        primeIntervalConstant / 100 := by
  exact min_le_right _ _

/-- The density obtained from Chebyshev is stronger than the deliberately
conservative target used by transference. -/
theorem densityTarget_le_primeScale_mul_log_div
    {k : ℕ} {cutoffNormalizer : ℝ}
    (hk : 3 ≤ k) (hnorm : 0 < cutoffNormalizer) :
    densityTarget k cutoffNormalizer ≤
      primeScale k cutoffNormalizer * log 2 / 128 := by
  calc
    densityTarget k cutoffNormalizer ≤
        primeScale k cutoffNormalizer *
          primeIntervalConstant / 100 :=
      densityTarget_le_primeScale_mul_interval k cutoffNormalizer
    _ ≤ primeScale k cutoffNormalizer * log 2 / 128 := by
      rw [primeIntervalConstant]
      have hproduct :
          0 ≤ primeScale k cutoffNormalizer * log 2 :=
        mul_nonneg (primeScale_nonneg hk hnorm)
          (log_pos (by norm_num)).le
      nlinarith

/-- The sieve level tends to infinity for every progression length in the
nontrivial range. -/
theorem tendsto_sieveLevel_atTop {k : ℕ} (hk : 3 ≤ k) :
    Tendsto (sieveLevel k) atTop atTop := by
  change Tendsto
    (fun N : ℕ ↦ ⌊(N : ℝ) ^ sieveExponent k⌋₊)
    atTop atTop
  simpa [Function.comp_def] using
    tendsto_nat_floor_atTop.comp
      ((tendsto_rpow_atTop (sieveExponent_pos hk)).comp
        tendsto_natCast_atTop_atTop)

/-- The chosen sieve level is already nonzero at every positive ambient
modulus.  This supplies pointwise nonnegativity of the cyclic majorant even
before any eventual large-modulus threshold is imposed. -/
theorem one_le_sieveLevel
    {k N : ℕ} (hk : 3 ≤ k) (hN : 0 < N) :
    1 ≤ sieveLevel k N := by
  have hNone : 1 ≤ N := hN
  rw [sieveLevel]
  apply Nat.le_floor
  simpa only [Nat.cast_one] using
    Real.one_le_rpow
      (x := (N : ℝ))
      (z := sieveExponent k)
      (by exact_mod_cast hNone)
      (sieveExponent_pos hk).le

theorem eventually_two_le_sieveLevel {k : ℕ} (hk : 3 ≤ k) :
    ∀ᶠ N : ℕ in atTop, 2 ≤ sieveLevel k N :=
  (tendsto_sieveLevel_atTop hk).eventually
    (eventually_ge_atTop 2)

/-- Threshold form convenient for the final nested parameter choice. -/
theorem exists_threshold_two_le_sieveLevel
    {k : ℕ} (hk : 3 ≤ k) :
    ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → 2 ≤ sieveLevel k N := by
  exact eventually_atTop.1 (eventually_two_le_sieveLevel hk)

end Wikipedia.SzemeredisTheorem
