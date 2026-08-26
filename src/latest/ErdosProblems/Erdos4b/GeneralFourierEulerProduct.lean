/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.GeneralFourierLocalFactor
import ErdosProblems.Erdos4b.GeneralFourierZeta

/-!
# The zeta Euler product of the pair reference factors

These are the actual reference factors of the Fourier comparison, with
their exponential powers identified with Mathlib's complex powers.
-/

namespace Erdos4b

noncomputable section

open scoped BigOperators

theorem primeFourierPower_eq_cpow_neg {p : ℝ} (hp : 0 < p) (s : ℂ) :
    primeFourierPower p s = (p : ℂ) ^ (-s) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [Complex.cpow_def_of_ne_zero hpC, ← Complex.ofReal_log hp.le]
  unfold primeFourierPower
  congr 1
  ring

theorem primeFourierPower_add (p : ℝ) (s t : ℂ) :
    primeFourierPower p (s + t) = primeFourierPower p s * primeFourierPower p t := by
  simp only [primeFourierPower, add_mul, neg_add, Complex.exp_add]

theorem primeFourierPower_div_eq_cpow {p : ℝ} (hp : 0 < p) (s : ℂ) :
    primeFourierPower p s / (p : ℂ) = (p : ℂ) ^ (-(1 + s)) := by
  have hpC : (p : ℂ) ≠ 0 := by exact_mod_cast hp.ne'
  rw [show -(1 + s) = -s + (-1) by ring,
    Complex.cpow_add _ _ hpC, Complex.cpow_neg_one,
    primeFourierPower_eq_cpow_neg hp, div_eq_mul_inv]

theorem selbergPairZetaFactor_eq_eulerQuotient
    {p : ℝ} (hp : 0 < p) (s t : ℂ) :
    selbergPairZetaFactor p (primeFourierPower p s) (primeFourierPower p t) =
      (1 - (p : ℂ) ^ (-(1 + (s + t))))⁻¹ /
        ((1 - (p : ℂ) ^ (-(1 + s)))⁻¹ * (1 - (p : ℂ) ^ (-(1 + t)))⁻¹) := by
  rw [← primeFourierPower_div_eq_cpow hp s, ← primeFourierPower_div_eq_cpow hp t,
    ← primeFourierPower_div_eq_cpow hp (s + t), primeFourierPower_add]
  unfold selbergPairZetaFactor
  simp only [div_eq_mul_inv, mul_inv, inv_inv]
  ring

/-- The reference pair product is exactly the source's zeta quotient,
not merely an asymptotic approximation to it. -/
theorem hasProd_selbergPairZetaFactor {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    HasProd (fun p : Nat.Primes ↦
      selbergPairZetaFactor (p : ℝ)
        (primeFourierPower (p : ℝ) s) (primeFourierPower (p : ℝ) t))
      (riemannZeta (1 + (s + t)) /
        (riemannZeta (1 + s) * riemannZeta (1 + t))) := by
  have hs1 : 1 < (1 + s).re := by simpa using hs
  have ht1 : 1 < (1 + t).re := by simpa using ht
  have hst1 : 1 < (1 + (s + t)).re := by
    simp only [Complex.add_re, Complex.one_re]
    linarith
  have hzs := riemannZeta_eulerProduct_hasProd hs1
  have hzt := riemannZeta_eulerProduct_hasProd ht1
  have hzst := riemannZeta_eulerProduct_hasProd hst1
  have hprod0 := mul_ne_zero (riemannZeta_ne_zero_of_one_le_re hs1.le)
    (riemannZeta_ne_zero_of_one_le_re ht1.le)
  have h := hzst.div₀ (hzs.mul hzt) hprod0
  convert! h using 1
  ext p
  exact selbergPairZetaFactor_eq_eulerQuotient (by exact_mod_cast p.property.pos) s t

theorem tprod_selbergPairZetaFactor {s t : ℂ} (hs : 0 < s.re) (ht : 0 < t.re) :
    (∏' p : Nat.Primes, selbergPairZetaFactor (p : ℝ)
      (primeFourierPower (p : ℝ) s) (primeFourierPower (p : ℝ) t)) =
      riemannZeta (1 + (s + t)) /
        (riemannZeta (1 + s) * riemannZeta (1 + t)) :=
  (hasProd_selbergPairZetaFactor hs ht).tprod_eq

theorem hasProd_finite_pairReferenceProduct
    {ι : Type*} (I : Finset ι) (s t : ι → ℂ)
    (hs : ∀ i ∈ I, 0 < (s i).re) (ht : ∀ i ∈ I, 0 < (t i).re) :
    HasProd (fun p : Nat.Primes ↦ ∏ i ∈ I,
      selbergPairZetaFactor (p : ℝ)
        (primeFourierPower (p : ℝ) (s i)) (primeFourierPower (p : ℝ) (t i)))
      (∏ i ∈ I, riemannZeta (1 + (s i + t i)) /
        (riemannZeta (1 + s i) * riemannZeta (1 + t i))) :=
  hasProd_prod fun i hi ↦ hasProd_selbergPairZetaFactor (hs i hi) (ht i hi)

end

end Erdos4b
