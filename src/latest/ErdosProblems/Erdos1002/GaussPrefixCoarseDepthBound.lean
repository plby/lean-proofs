import ErdosProblems.Erdos1002.GaussPrefixDeepestCylinder
import ErdosProblems.Erdos1002.GaussPrefixAnnularDepthBoxes

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# A coarse deterministic depth bound for denominator-bounded Gauss prefixes

The bad-denominator deletion in the marked-prefix argument needs one finite
ambient set of depths.  This file supplies it without using any probabilistic
input.  Positivity of the continued-fraction digits forces the terminal
denominator to grow by at least `2 ^ (n / 2)` at depth `n`; consequently a
prefix whose denominator is at most `N` has depth `O(log N)`.

The deliberately generous constant `4` keeps the proof elementary.  We also
record the exact normalized asymptotic of the chosen natural ceiling, so that
subsequent finite-family moment bounds do not have to hide a rounding step.
-/

open Filter
open scoped Topology

namespace Erdos1002

noncomputable section

/-- A finite logarithmic ambient set large enough to contain every positive
continued-fraction prefix whose terminal denominator is at most `N`. -/
def gaussCoarseDepthAmbientSize (N : ℕ) : ℕ :=
  ⌈4 * Real.log (N : ℝ)⌉₊ + 2

/-- Positive continued-fraction words of depth `n` have terminal denominator
at least `2 ^ (n / 2)`. -/
theorem pow_two_half_depth_le_cfTerminalDenominator
    {n : ℕ} (w : PositiveDigitWord n) :
    2 ^ (n / 2) ≤ cfTerminalDenominator w.1 := by
  have h :=
    pow_two_div_two_mul_cfTerminalDenominator_le_append
      ([] : List ℕ) w.2.2
  simpa [w.2.1] using! h

/-- Every denominator-bounded positive word lies in the coarse logarithmic
ambient depth range. -/
theorem depth_lt_gaussCoarseDepthAmbientSize_of_denominator_le
    {N n : ℕ} (w : PositiveDigitWord n)
    (hden : cfTerminalDenominator w.1 ≤ N) :
    n < gaussCoarseDepthAmbientSize N := by
  have hpowNat : 2 ^ (n / 2) ≤ N :=
    (pow_two_half_depth_le_cfTerminalDenominator w).trans hden
  have hpowReal :
      ((2 ^ (n / 2) : ℕ) : ℝ) ≤ (N : ℝ) := by
    exact_mod_cast hpowNat
  have hpowPos : 0 < ((2 ^ (n / 2) : ℕ) : ℝ) := by positivity
  have hlogle :
      Real.log (((2 ^ (n / 2) : ℕ) : ℝ)) ≤
        Real.log (N : ℝ) :=
    Real.log_le_log hpowPos hpowReal
  have hlogpow :
      Real.log (((2 ^ (n / 2) : ℕ) : ℝ)) =
        ((n / 2 : ℕ) : ℝ) * Real.log 2 := by
    rw [Nat.cast_pow, Nat.cast_ofNat, Real.log_pow]
  rw [hlogpow] at hlogle
  have hlogTwo : (1 / 2 : ℝ) ≤ Real.log 2 := by
    exact (by norm_num : (1 / 2 : ℝ) < 0.6931471803).le.trans
      Real.log_two_gt_d9.le
  have hhalf :
      ((n / 2 : ℕ) : ℝ) * (1 / 2 : ℝ) ≤
        ((n / 2 : ℕ) : ℝ) * Real.log 2 :=
    mul_le_mul_of_nonneg_left hlogTwo (Nat.cast_nonneg _)
  have hhalfDepth :
      ((n / 2 : ℕ) : ℝ) ≤ 2 * Real.log (N : ℝ) := by
    nlinarith
  have hnNat : n ≤ 2 * (n / 2) + 1 := by omega
  have hnReal :
      (n : ℝ) ≤ 4 * Real.log (N : ℝ) + 1 := by
    have hnReal' :
        (n : ℝ) ≤ 2 * ((n / 2 : ℕ) : ℝ) + 1 := by
      exact_mod_cast hnNat
    nlinarith
  have hceil :
      4 * Real.log (N : ℝ) ≤
        (⌈4 * Real.log (N : ℝ)⌉₊ : ℝ) :=
    Nat.le_ceil _
  have hnCeilReal :
      (n : ℝ) ≤ (⌈4 * Real.log (N : ℝ)⌉₊ : ℝ) + 1 := by
    linarith
  have hnCeilNat :
      n ≤ ⌈4 * Real.log (N : ℝ)⌉₊ + 1 := by
    exact_mod_cast hnCeilReal
  dsimp [gaussCoarseDepthAmbientSize]
  omega

/-- The coarse ambient size has the advertised normalized logarithmic
asymptotic. -/
theorem tendsto_gaussCoarseDepthAmbientSize_div_log :
    Tendsto
      (fun N : ℕ ↦
        (gaussCoarseDepthAmbientSize N : ℝ) /
          Real.log (N : ℝ))
      atTop (nhds 4) := by
  have hceil :
      Tendsto
        (fun N : ℕ ↦
          (⌈4 * Real.log (N : ℝ)⌉₊ : ℝ) /
            Real.log (N : ℝ))
        atTop (nhds 4) := by
    simpa using!
      (tendsto_natCeil_const_mul_scale_div
        (fun N : ℕ ↦ Real.log (N : ℝ))
        tendsto_log_natCast_atTop
        (c := (4 : ℝ)) (d := (1 : ℝ))
        (by norm_num) (by norm_num))
  have htwo :
      Tendsto
        (fun N : ℕ ↦ (2 : ℝ) / Real.log (N : ℝ))
        atTop (nhds 0) :=
    tendsto_log_natCast_atTop.const_div_atTop 2
  have hadd := hceil.add htwo
  convert! hadd using 1
  · funext N
    simp only [gaussCoarseDepthAmbientSize, Nat.cast_add,
      Nat.cast_ofNat]
    ring
  · norm_num

end

end Erdos1002
