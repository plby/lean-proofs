/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Tactic

/-! # Polynomial product curvature without division by the time coordinate -/

namespace Erdos207

def powerProductSlope (c m : ℕ) (A A₁ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (c : ℝ) * t ^ (c - 1) * A t ^ m + (m : ℝ) * t ^ c * A t ^ (m - 1) * A₁ t

def powerProductCurvature (c m : ℕ) (A A₁ A₂ : ℝ → ℝ) (t : ℝ) : ℝ :=
  (c : ℝ) * (c - 1 : ℕ) * t ^ (c - 2) * A t ^ m +
    2 * (c : ℝ) * (m : ℝ) * t ^ (c - 1) * A t ^ (m - 1) * A₁ t +
      (m : ℝ) * (m - 1 : ℕ) * t ^ c * A t ^ (m - 2) * A₁ t ^ 2 +
        (m : ℝ) * t ^ c * A t ^ (m - 1) * A₂ t

theorem hasDerivAt_powerProduct
    (c m : ℕ) (A A₁ : ℝ → ℝ) (t : ℝ) (hA : HasDerivAt A (A₁ t) t) :
    HasDerivAt (fun u ↦ u ^ c * A u ^ m) (powerProductSlope c m A A₁ t) t := by
  convert! (hasDerivAt_pow c t).mul (hA.pow m) using 1
  dsimp only [powerProductSlope, Pi.pow_apply]
  ring

theorem hasDerivAt_powerProductSlope
    (c m : ℕ) (A A₁ A₂ : ℝ → ℝ) (t : ℝ)
    (hA : HasDerivAt A (A₁ t) t) (hA₁ : HasDerivAt A₁ (A₂ t) t) :
    HasDerivAt (powerProductSlope c m A A₁) (powerProductCurvature c m A A₁ A₂ t) t := by
  have hleft := ((hasDerivAt_pow (c - 1) t).const_mul (c : ℝ)).mul (hA.pow m)
  have hright := (((hasDerivAt_pow c t).const_mul (m : ℝ)).mul (hA.pow (m - 1))).mul hA₁
  convert! hleft.add hright using 1
  dsimp only [powerProductCurvature, Pi.pow_apply, Pi.mul_apply, Pi.add_apply]
  simp only [Nat.sub_sub, show 1 + 1 = (2 : ℕ) from rfl]
  ring

end Erdos207
