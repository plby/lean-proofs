/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.RingTheory.PowerSeries.WellKnown
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring

/-! # Local Euler factors for the rational Artin series -/

namespace Erdos387

namespace RationalWeil

variable {R : Type*} [CommRing R]

/-- The geometric local factor `(1 - z X^e)⁻¹`. -/
noncomputable def localEuler (e : Nat) (z : R) : PowerSeries R :=
  PowerSeries.subst (PowerSeries.X ^ e)
    (PowerSeries.rescale z (PowerSeries.mk 1))

@[simp]
theorem coeff_localEuler (z : R) {e n : Nat} (he : e ≠ 0) :
    PowerSeries.coeff n (localEuler e z) =
      if e ∣ n then z ^ (n / e) else 0 := by
  rw [localEuler, PowerSeries.coeff_subst_X_pow he,
    PowerSeries.coeff_rescale, PowerSeries.coeff_mk]
  simp

theorem localEuler_mul_one_sub (z : R) {e : Nat} (he : e ≠ 0) :
    localEuler e z *
      (1 - PowerSeries.C z * PowerSeries.X ^ e) = 1 := by
  have hbase := PowerSeries.mk_one_mul_one_sub_eq_one R
  have hscale := congrArg (PowerSeries.rescale z) hbase
  simp only [map_mul, map_sub, map_one, PowerSeries.rescale_X] at hscale
  let hs := PowerSeries.HasSubst.X_pow (R := R) he
  let phi : PowerSeries R →ₐ[R] PowerSeries R :=
    PowerSeries.substAlgHom hs
  have hsubst := congrArg phi hscale
  simp only [map_mul, map_sub, map_one, phi,
    PowerSeries.substAlgHom_X] at hsubst
  rw [PowerSeries.coe_substAlgHom hs] at hsubst
  rw [PowerSeries.subst_C] at hsubst
  exact hsubst

private theorem derivative_one_sub_C_mul_X_pow (z : R) (e : Nat) :
    PowerSeries.derivative R
        (1 - PowerSeries.C z * PowerSeries.X ^ e) =
      -PowerSeries.C ((e : R) * z) * PowerSeries.X ^ (e - 1) := by
  change PowerSeries.derivative R
      (1 - PowerSeries.C z * PowerSeries.X ^ e) = _
  rw [map_sub, ← map_one (PowerSeries.C (R := R)),
    PowerSeries.derivative_C, Derivation.leibniz,
    PowerSeries.derivative_C, PowerSeries.derivative_pow,
    PowerSeries.derivative_X]
  simp only [smul_eq_mul, mul_one, zero_sub]
  rw [map_mul]
  simp only [map_natCast]
  ring

theorem X_mul_derivativeFun_localEuler (z : R) {e : Nat} (he : e ≠ 0) :
    PowerSeries.X * PowerSeries.derivative R (localEuler e z) =
      PowerSeries.C (e : R) * localEuler e z * (localEuler e z - 1) := by
  let L : PowerSeries R := localEuler e z
  let Q : PowerSeries R :=
    1 - PowerSeries.C z * PowerSeries.X ^ e
  have hInv : L * Q = 1 := localEuler_mul_one_sub z he
  have hDer :
      L * PowerSeries.derivative R Q +
          Q * PowerSeries.derivative R L = 0 := by
    have h := congrArg (PowerSeries.derivative R) hInv
    rw [Derivation.leibniz,
      Derivation.map_one_eq_zero] at h
    simpa only [smul_eq_mul, add_comm] using h
  have hQDer :
      PowerSeries.derivative R Q =
        -PowerSeries.C ((e : R) * z) *
          PowerSeries.X ^ (e - 1) :=
    derivative_one_sub_C_mul_X_pow z e
  rw [hQDer] at hDer
  have hPow :
      PowerSeries.X * PowerSeries.X ^ (e - 1) =
        (PowerSeries.X : PowerSeries R) ^ e := by
    cases e with
    | zero => exact (he rfl).elim
    | succ e =>
        rw [Nat.succ_sub_one, pow_succ]
        ac_rfl
  rw [map_mul] at hDer
  simp only [map_natCast] at hDer
  rw [map_natCast]
  linear_combination
    (PowerSeries.X * L) * hDer -
      (PowerSeries.X * PowerSeries.derivative R L +
        (e : PowerSeries R) * L) * hInv +
      ((e : PowerSeries R) * PowerSeries.C z * L ^ 2) * hPow

end RationalWeil

end Erdos387
