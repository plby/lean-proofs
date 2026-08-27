/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.KSSSPatternDeterministicBounds

/-! # Fixed numerical requirements for a bounded pattern in the power hierarchy -/

namespace Erdos207

noncomputable section

def ksssPatternStepCoefficient (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) : ℝ :=
  3 * ksssPatternHazardCoefficient q coeff h m + 1

def ksssPatternJumpCoefficient (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) : ℝ :=
  2 + 4 * ksssPatternStepCoefficient q coeff h m + 16

def ksssPatternVarianceCoefficient (q : ℕ) (coeff : ℕ → ℝ) (h m : ℕ) : ℝ :=
  192 * (ksssPatternHazardCoefficient q coeff h m + patternHazardErrorCoefficient q h m) +
    64 * ksssPatternStepCoefficient q coeff h m ^ 2 + 2 * 16 ^ 2

structure KSSSPatternPowerRequirements
    (q b B k Rmin h m t : ℕ) (coeff : ℕ → ℝ) : Prop where
  density_exponent : 1 ≤ b
  clock_exponent : 2 * b ≤ ksssPowerDenominatorExponent q b B k Rmin
  taylor_exponent : b * h + m + ksssPowerErrorExponent b B + b + 1 ≤
    2 * ksssPowerDenominatorExponent q b B k Rmin
  selector_exponent : 2 * b + ksssPowerErrorExponent b B + 1 ≤
    2 * ksssPowerDenominatorExponent q b B k Rmin
  selector_coefficient : 3 * (m : ℝ) ≤ t
  taylor_coefficient : ksssPatternTaylorCoefficient q coeff h m ≤ t
  drift_coefficient : (patternHazardErrorCoefficient q h m : ℝ) +
    2 * ksssPatternHazardCoefficient q coeff h m ≤ t
  target_step_coefficient : 2 * ksssPatternStepCoefficient q coeff h m ≤ t
  envelope_coefficient : 6 * ((B + 2 : ℕ) : ℝ) * 2 ^ (B + 2) ≤ t
  jump_coefficient : ksssPatternJumpCoefficient q coeff h m ≤ t
  variance_coefficient : ksssPatternVarianceCoefficient q coeff h m ≤ t

end

end Erdos207
