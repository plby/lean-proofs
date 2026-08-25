import Util.Bernays.RamifiedEulerCorrection
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries
import Mathlib.NumberTheory.LSeries.Nonvanishing

/-!
# The quadratic-character identity for the local Dirichlet series

Squaring the local norm series gives the product of zeta, a quadratic
Dirichlet L-function, and the convergent inert and ramified corrections.
-/

open Filter Topology Real
open scoped Classical

namespace Bernays

theorem quadratic_euler_factor_identity (a r : ℂ) (ha : a = 0 ∨ a = 1 ∨ a = -1) :
    (if a = -1 then (1 - r ^ 2)⁻¹ else (1 - r)⁻¹) ^ 2 =
      (1 - r)⁻¹ * (1 - a * r)⁻¹ *
        (if a = -1 then (1 - r ^ 2)⁻¹ else 1) *
        (if a = 0 then (1 - r)⁻¹ else 1) := by
  rcases ha with rfl | rfl | rfl
  · norm_num
    simp only [← mul_inv, pow_two]
  · norm_num
    simp only [← mul_inv, pow_two]
  · norm_num
    have h : (1 - r)⁻¹ * (1 + r)⁻¹ = (1 - r ^ 2)⁻¹ := by
      rw [← mul_inv]
      congr 1
      ring
    rw [h]
    simp only [← mul_inv, pow_two]

theorem prime_cpow_neg_real (p : Nat.Primes) (s : ℝ) :
    ((p : ℕ) : ℂ) ^ (-(s : ℂ)) = (((((p : ℕ) : ℝ) ^ s)⁻¹ : ℝ) : ℂ) := by
  rw [Complex.cpow_neg, Complex.ofReal_inv,
    Complex.ofReal_cpow (Nat.cast_nonneg (p : ℕ)) s]
  rfl

theorem localParity_dirichlet_square {N : ℕ} [NeZero N]
    (χ : DirichletCharacter ℂ N) (hχ : χ ^ 2 = 1) {s : ℝ} (hs : 1 < s) :
    (realDirichlet (localParity (fun p : ℕ => χ p = -1)) s : ℂ) ^ 2 =
      riemannZeta (s : ℂ) * χ.LFunction (s : ℂ) *
        (squareCorrection (fun p : ℕ => χ p = -1) s : ℂ) *
        (ramifiedCorrection (ramifiedPrimes N) s : ℂ) := by
  let S : ℕ → Prop := fun p => χ p = -1
  let r : Nat.Primes → ℂ := fun p => (((((p : ℕ) : ℝ) ^ s)⁻¹ : ℝ) : ℂ)
  have hsC : 1 < (s : ℂ).re := hs
  have hs' : (3 / 4 : ℝ) ≤ s := by linarith
  have hf : HasProd (fun p : Nat.Primes =>
      if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹)
      (realDirichlet (localParity S) s : ℂ) := by
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (localParity_explicitEulerProduct S hs).map Complex.ofRealHom Complex.continuous_ofReal
  have hg : HasProd (fun p : Nat.Primes => if S p then (1 - r p ^ 2)⁻¹ else 1)
      (squareCorrection S s : ℂ) := by
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_pow] using
      (squareCorrection_hasProd S hs').map Complex.ofRealHom Complex.continuous_ofReal
  have hR : HasProd (fun p : Nat.Primes => if χ p = 0 then (1 - r p)⁻¹ else 1)
      (ramifiedCorrection (ramifiedPrimes N) s : ℂ) := by
    have hz (p : Nat.Primes) : p ∈ ramifiedPrimes N ↔ χ p = 0 :=
      (mem_ramifiedPrimes_iff (NeZero.ne N) p).trans (char_prime_eq_zero_iff χ p).symm
    simpa only [r, Function.comp_def, Complex.ofRealHom_eq_coe, apply_ite,
      Complex.ofReal_inv, Complex.ofReal_sub, Complex.ofReal_one, hz] using
      (ramifiedCorrection_hasProd (ramifiedPrimes N) hs').map
        Complex.ofRealHom Complex.continuous_ofReal
  have hζ : HasProd (fun p : Nat.Primes => (1 - r p)⁻¹) (riemannZeta (s : ℂ)) := by
    apply (riemannZeta_eulerProduct_hasProd hsC).congr_fun
    intro p
    rw [prime_cpow_neg_real]
  have hL : HasProd (fun p : Nat.Primes => (1 - χ p * r p)⁻¹) (χ.LFunction (s : ℂ)) := by
    rw [DirichletCharacter.LFunction_eq_LSeries χ hsC]
    apply (χ.LSeries_eulerProduct_hasProd hsC).congr_fun
    intro p
    rw [prime_cpow_neg_real]
  have hright := ((hζ.mul hL).mul hg).mul hR
  have hright' : HasProd
      (fun p : Nat.Primes => (if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹) ^ 2)
      (riemannZeta (s : ℂ) * χ.LFunction (s : ℂ) *
        (squareCorrection S s : ℂ) * (ramifiedCorrection (ramifiedPrimes N) s : ℂ)) := by
    apply hright.congr_fun
    intro p
    exact quadratic_euler_factor_identity (χ p) (r p)
      (MulChar.isQuadratic_iff_sq_eq_one.mpr hχ p)
  have hleft := hf.mul hf
  have hleft' : HasProd
      (fun p : Nat.Primes => (if S p then (1 - r p ^ 2)⁻¹ else (1 - r p)⁻¹) ^ 2)
      ((realDirichlet (localParity S) s : ℂ) ^ 2) := by
    simpa only [pow_two] using hleft
  exact hleft'.unique hright'

end Bernays
