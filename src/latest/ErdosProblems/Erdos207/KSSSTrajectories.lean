/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic

/-!
# The coupled KSSS trajectories

The index `d` is the source's vertex order minus three.  The coefficient
`a d` specializes to `(d + 1) * |J_(d+3)| / A₀^(d+1)`.  The configuration
trajectory is written polynomially in time, so its derivative at time zero
does not require interpreting a quotient by time.
-/

namespace Erdos207

open Finset
open scoped BigOperators

noncomputable section

def ksssEdgeDensity (E₀ t : ℝ) : ℝ := (E₀ - 3 * t) / E₀

def ksssPoissonExponent (orders : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ orders, a d * t ^ d

def ksssPoissonRate (orders : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) : ℝ :=
  ∑ d ∈ orders, a d * (d : ℝ) * t ^ (d - 1)

def ksssAvailableTrajectory (orders : Finset ℕ) (a : ℕ → ℝ)
    (E₀ A₀ t : ℝ) : ℝ :=
  A₀ * ksssEdgeDensity E₀ t ^ 3 * Real.exp (-ksssPoissonExponent orders a t)

def ksssPairTrajectory (orders : Finset ℕ) (a : ℕ → ℝ)
    (E₀ A₀ t : ℝ) : ℝ :=
  3 * ksssAvailableTrajectory orders a E₀ A₀ t / (E₀ * ksssEdgeDensity E₀ t)

def ksssConfigurationTrajectory (orders : Finset ℕ) (a : ℕ → ℝ)
    (E₀ A₀ : ℝ) (d c : ℕ) (t : ℝ) : ℝ :=
  (d.choose c : ℝ) * a d * t ^ c *
    ksssAvailableTrajectory orders a E₀ A₀ t ^ (d - c)

def ksssThreatTrajectory (orders : Finset ℕ) (a : ℕ → ℝ)
    (E₀ A₀ t : ℝ) : ℝ :=
  3 * ksssPairTrajectory orders a E₀ A₀ t +
    ∑ d ∈ orders, ksssConfigurationTrajectory orders a E₀ A₀ d (d - 1) t

theorem hasDerivAt_ksssEdgeDensity (E₀ t : ℝ) :
    HasDerivAt (ksssEdgeDensity E₀) (-3 / E₀) t := by
  simpa [ksssEdgeDensity] using!
    ((hasDerivAt_const t E₀).sub ((hasDerivAt_id t).const_mul 3)).div_const E₀

theorem hasDerivAt_ksssPoissonExponent
    (orders : Finset ℕ) (a : ℕ → ℝ) (t : ℝ) :
    HasDerivAt (ksssPoissonExponent orders a) (ksssPoissonRate orders a t) t := by
  apply HasDerivAt.fun_sum
  intro d hd
  convert! (hasDerivAt_pow d t).const_mul (a d) using 1 <;> ring

theorem ksssConfigurationTrajectory_last
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    {d : ℕ} (hd : 1 ≤ d) :
    ksssConfigurationTrajectory orders a E₀ A₀ d (d - 1) t =
      a d * d * t ^ (d - 1) * ksssAvailableTrajectory orders a E₀ A₀ t := by
  have hsub : d - (d - 1) = 1 := by omega
  rw [ksssConfigurationTrajectory, hsub, pow_one, Nat.choose_symm (by omega)]
  rw [Nat.choose_one_right]
  ring

theorem ksssThreatTrajectory_eq
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d) :
    ksssThreatTrajectory orders a E₀ A₀ t =
      3 * ksssPairTrajectory orders a E₀ A₀ t +
        ksssAvailableTrajectory orders a E₀ A₀ t * ksssPoissonRate orders a t := by
  unfold ksssThreatTrajectory ksssPoissonRate
  rw [mul_sum]
  congr 1
  apply sum_congr rfl
  intro d hd
  rw [ksssConfigurationTrajectory_last orders a E₀ A₀ t (horders d hd)]
  ring

theorem ksssEdgeDensity_pos {E₀ t : ℝ} (hE : 0 < E₀) (ht : 3 * t < E₀) :
    0 < ksssEdgeDensity E₀ t := div_pos (sub_pos.mpr ht) hE

theorem ksssAvailableTrajectory_pos
    (orders : Finset ℕ) (a : ℕ → ℝ) {E₀ A₀ t : ℝ}
    (hE : 0 < E₀) (hA : 0 < A₀) (ht : 3 * t < E₀) :
    0 < ksssAvailableTrajectory orders a E₀ A₀ t := by
  unfold ksssAvailableTrajectory
  exact mul_pos (mul_pos hA (pow_pos (ksssEdgeDensity_pos hE ht) 3))
    (Real.exp_pos _)

theorem ksssPairTrajectory_pos
    (orders : Finset ℕ) (a : ℕ → ℝ) {E₀ A₀ t : ℝ}
    (hE : 0 < E₀) (hA : 0 < A₀) (ht : 3 * t < E₀) :
    0 < ksssPairTrajectory orders a E₀ A₀ t := by
  unfold ksssPairTrajectory
  exact div_pos (mul_pos (by norm_num)
    (ksssAvailableTrajectory_pos orders a hE hA ht))
      (mul_pos hE (ksssEdgeDensity_pos hE ht))

theorem hasDerivAt_ksssAvailableTrajectory
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0) :
    HasDerivAt (ksssAvailableTrajectory orders a E₀ A₀)
      (-ksssThreatTrajectory orders a E₀ A₀ t) t := by
  have hderiv := (((hasDerivAt_ksssEdgeDensity E₀ t).pow 3).const_mul A₀).mul
    ((hasDerivAt_ksssPoissonExponent orders a t).neg.exp)
  convert! hderiv using 1
  rw [ksssThreatTrajectory_eq orders a E₀ A₀ t horders]
  dsimp only [ksssPairTrajectory, ksssAvailableTrajectory, Pi.pow_apply, Pi.neg_apply]
  field_simp
  <;> ring

theorem hasDerivAt_ksssPairTrajectory
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0) :
    HasDerivAt (ksssPairTrajectory orders a E₀ A₀)
      (-(3 / (E₀ * ksssEdgeDensity E₀ t)) *
        (ksssThreatTrajectory orders a E₀ A₀ t -
          ksssPairTrajectory orders a E₀ A₀ t)) t := by
  have hderiv := ((hasDerivAt_ksssAvailableTrajectory orders a E₀ A₀ t
    horders hE hp).const_mul 3).div
      ((hasDerivAt_ksssEdgeDensity E₀ t).const_mul E₀) (mul_ne_zero hE hp)
  convert! hderiv using 1
  dsimp only [ksssPairTrajectory]
  field_simp
  <;> ring

/-- Gain is absent at zero chosen triangles. -/
theorem hasDerivAt_ksssConfigurationTrajectory_zero
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0)
    (hA : ksssAvailableTrajectory orders a E₀ A₀ t ≠ 0)
    {d : ℕ} (hd : 1 ≤ d) :
    HasDerivAt (ksssConfigurationTrajectory orders a E₀ A₀ d 0)
      (-(d : ℝ) * ksssConfigurationTrajectory orders a E₀ A₀ d 0 t *
        ksssThreatTrajectory orders a E₀ A₀ t /
          ksssAvailableTrajectory orders a E₀ A₀ t) t := by
  have hderiv := ((hasDerivAt_ksssAvailableTrajectory orders a E₀ A₀ t
    horders hE hp).pow d).const_mul (a d)
  convert! hderiv using 1
  · ext x
    simp [ksssConfigurationTrajectory]
  · simp only [ksssConfigurationTrajectory, Nat.choose_zero_right, Nat.cast_one,
      one_mul, pow_zero, mul_one, Nat.sub_zero]
    rw [div_eq_iff hA]
    have hpow : ksssAvailableTrajectory orders a E₀ A₀ t ^ d =
        ksssAvailableTrajectory orders a E₀ A₀ t ^ (d - 1) *
          ksssAvailableTrajectory orders a E₀ A₀ t := by
      rw [← pow_succ, Nat.sub_add_cancel hd]
    rw [hpow]
    ring

/-- The positive-chosen-count equation uses the preceding configuration
class for its gain and the total threat trajectory for its loss. -/
theorem hasDerivAt_ksssConfigurationTrajectory_succ
    (orders : Finset ℕ) (a : ℕ → ℝ) (E₀ A₀ t : ℝ)
    (horders : ∀ d ∈ orders, 1 ≤ d)
    (hE : E₀ ≠ 0) (hp : ksssEdgeDensity E₀ t ≠ 0)
    (hA : ksssAvailableTrajectory orders a E₀ A₀ t ≠ 0)
    {d c : ℕ} (hcd : c + 1 < d) :
    HasDerivAt (ksssConfigurationTrajectory orders a E₀ A₀ d (c + 1))
      ((((d - c : ℕ) : ℝ) * ksssConfigurationTrajectory orders a E₀ A₀ d c t -
        ((d - (c + 1) : ℕ) : ℝ) *
          ksssConfigurationTrajectory orders a E₀ A₀ d (c + 1) t *
            ksssThreatTrajectory orders a E₀ A₀ t) /
              ksssAvailableTrajectory orders a E₀ A₀ t) t := by
  have hderiv := ((hasDerivAt_pow (c + 1) t).const_mul
      ((d.choose (c + 1) : ℝ) * a d)).mul
    ((hasDerivAt_ksssAvailableTrajectory orders a E₀ A₀ t
      horders hE hp).pow (d - (c + 1)))
  have hbinom : (d.choose (c + 1) : ℝ) * (c + 1 : ℕ) =
      (d.choose c : ℝ) * (d - c : ℕ) := by
    exact_mod_cast Nat.choose_succ_right_eq d c
  have hdiff : d - c = (d - (c + 1)) + 1 := by omega
  have hdiff' : d - (c + 1) = (d - (c + 1) - 1) + 1 := by omega
  convert! hderiv using 1
  dsimp only [ksssConfigurationTrajectory, Pi.pow_apply]
  simp only [Nat.add_sub_cancel]
  rw [div_eq_iff hA]
  rw [hdiff, pow_succ]
  have hpower : ksssAvailableTrajectory orders a E₀ A₀ t ^ (d - (c + 1)) =
      ksssAvailableTrajectory orders a E₀ A₀ t ^ (d - (c + 1) - 1) *
        ksssAvailableTrajectory orders a E₀ A₀ t := by
    rw [← pow_succ, ← hdiff']
  rw [hpower]
  rw [hdiff] at hbinom
  linear_combination -a d * t ^ c *
    (ksssAvailableTrajectory orders a E₀ A₀ t ^ (d - (c + 1) - 1)) *
      ksssAvailableTrajectory orders a E₀ A₀ t ^ 2 * hbinom

end

end Erdos207
