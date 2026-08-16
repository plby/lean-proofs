import Wikipedia.GreenTao.Sieve.FourierZetaParameters
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-!
# Identifying the zeta-model Euler product

The model local factor attached to one pair of Fourier shifts `u,v` is

`(1 - p^(-1-u)) (1 - p^(-1-v)) / (1 - p^(-1-u-v))`.

Mathlib's Euler product for `riemannZeta` identifies its prime product with

`ζ(1+u+v) / (ζ(1+u) ζ(1+v))`

whenever the real parts of `u` and `v` are positive.  This file proves that
identity first for one pair and then for an arbitrary finite system.  It
then specializes to the exact Mathlib Fourier shifts and splits the answer
into the elementary singular factor and the removable completed factor from
`ZetaNearOne`.
-/

namespace Wikipedia.SzemeredisTheorem

open scoped BigOperators

/-- Direct (rather than inverse) local Euler factor for the zeta function. -/
theorem riemannZeta_directEulerProduct_hasProd
    {s : ℂ} (hs : 1 < s.re) :
    HasProd
      (fun p : Nat.Primes =>
        1 - (p : ℂ) ^ (-s))
      (riemannZeta s)⁻¹ := by
  have hz : riemannZeta s ≠ 0 :=
    riemannZeta_ne_zero_of_one_lt_re hs
  have h := riemannZeta_eulerProduct_hasProd hs
  unfold HasProd at h ⊢
  simpa only [Finset.prod_inv_distrib, inv_inv] using
    h.inv₀ hz

/-- The per-prime zeta model for one pair of shifts. -/
noncomputable def zetaPairEulerLocalFactor
    (u v : ℂ) (p : Nat.Primes) : ℂ :=
  (1 - (p : ℂ) ^ (-(1 + u))) *
    (1 - (p : ℂ) ^ (-(1 + v))) *
      (1 - (p : ℂ) ^ (-(1 + u + v)))⁻¹

/-- Euler-product identification for one pair of positive-real-part shifts.
-/
theorem zetaPairEulerLocalFactor_hasProd
    {u v : ℂ} (hu : 0 < u.re) (hv : 0 < v.re) :
    HasProd
      (zetaPairEulerLocalFactor u v)
      (riemannZeta (1 + u + v) /
        (riemannZeta (1 + u) *
          riemannZeta (1 + v))) := by
  have hu1 : 1 < (1 + u).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hv1 : 1 < (1 + v).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have huv1 : 1 < (1 + u + v).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have h :=
    ((riemannZeta_directEulerProduct_hasProd hu1).mul
      (riemannZeta_directEulerProduct_hasProd hv1)).mul
      (riemannZeta_eulerProduct_hasProd huv1)
  convert h using 1
  · funext p
    simp only [zetaPairEulerLocalFactor]
  · simp only [div_eq_mul_inv, mul_inv_rev]
    ring

/-- Product of all per-pair zeta-model factors at one prime. -/
noncomputable def zetaSystemEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (u v : κ → ℂ) (p : Nat.Primes) : ℂ :=
  ∏ i, zetaPairEulerLocalFactor (u i) (v i) p

/-- The prime product and finite pair product commute. -/
theorem zetaSystemEulerLocalFactor_hasProd
    {κ : Type*} [Fintype κ]
    {u v : κ → ℂ}
    (hu : ∀ i, 0 < (u i).re)
    (hv : ∀ i, 0 < (v i).re) :
    HasProd
      (zetaSystemEulerLocalFactor u v)
      (∏ i,
        riemannZeta (1 + u i + v i) /
          (riemannZeta (1 + u i) *
            riemannZeta (1 + v i))) := by
  classical
  change HasProd
    (fun p : Nat.Primes =>
      ∏ i, zetaPairEulerLocalFactor (u i) (v i) p) _
  simpa only using
    (hasProd_prod
      (s := (Finset.univ : Finset κ))
      (fun i _ =>
        zetaPairEulerLocalFactor_hasProd
          (hu i) (hv i)))

/-- The zeta model specialized to the exact cutoff Fourier shifts. -/
noncomputable def cutoffZetaEulerLocalFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ)
    (p : Nat.Primes) : ℂ :=
  zetaSystemEulerLocalFactor
    (fun i => cutoffZetaShift R (t i))
    (fun i => cutoffZetaShift R (u i)) p

/-- The elementary pole contribution left after completing every zeta
factor. -/
noncomputable def cutoffZetaSingularFactor
    {κ : Type*} [Fintype κ]
    (R : ℕ) (t u : κ → ℝ) : ℂ :=
  ∏ i,
    (cutoffZetaShift R (t i) *
        cutoffZetaShift R (u i)) /
      (cutoffZetaShift R (t i) +
        cutoffZetaShift R (u i))

/-- Exact splitting of the finite zeta quotient into its elementary
singular factor and removable completed factor. -/
theorem cutoffZetaSingularFactor_mul_systemFactor
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    cutoffZetaSingularFactor R t u *
        cutoffZetaSystemFactor R t u =
      ∏ i,
        riemannZeta
              (1 + cutoffZetaShift R (t i) +
                cutoffZetaShift R (u i)) /
          (riemannZeta
                (1 + cutoffZetaShift R (t i)) *
            riemannZeta
                (1 + cutoffZetaShift R (u i))) := by
  classical
  rw [cutoffZetaSingularFactor,
    cutoffZetaSystemFactor_eq_prod hR,
    ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro i _
  have ht :=
    cutoffZetaShift_ne_zero hR (t i)
  have hu :=
    cutoffZetaShift_ne_zero hR (u i)
  have hsum :=
    cutoffZetaShift_add_ne_zero hR (t i) (u i)
  field_simp

/-- Full Euler-product identification at the exact Fourier parameters. -/
theorem cutoffZetaEulerLocalFactor_hasProd
    {κ : Type*} [Fintype κ]
    {R : ℕ} (hR : 1 < R)
    (t u : κ → ℝ) :
    HasProd
      (cutoffZetaEulerLocalFactor R t u)
      (cutoffZetaSingularFactor R t u *
        cutoffZetaSystemFactor R t u) := by
  have h :=
    zetaSystemEulerLocalFactor_hasProd
      (u := fun i => cutoffZetaShift R (t i))
      (v := fun i => cutoffZetaShift R (u i))
      (fun i => cutoffZetaShift_re_pos hR (t i))
      (fun i => cutoffZetaShift_re_pos hR (u i))
  rw [cutoffZetaSingularFactor_mul_systemFactor
    hR t u]
  exact h

end Wikipedia.SzemeredisTheorem
