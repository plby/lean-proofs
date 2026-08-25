import ErdosProblems.Erdos157.ProperPrimePowers

/-! Elementary estimates for monic prime polynomials. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial
open ElementaryCharacterBound

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- The polynomial zeta function has weighted prime-power coefficient `q^n`. -/
theorem zeta_primePowerCoefficient (n : ℕ) (hn : 0 < n) :
    primePowerCoefficient (1 : K[X]) 1 n = (Fintype.card K : ℂ) ^ n := by
  let q : ℝ := Fintype.card K
  have hq : 0 < q := by dsimp only [q]; exact_mod_cast Fintype.card_pos (α := K)
  let r : ℝ := 1 / (2 * q)
  have hr : 0 < r := by dsimp only [r]; positivity
  have hqr : q * r < 1 := by
    have heq : q * r = 1 / 2 := by dsimp only [r]; field_simp
    rw [heq]
    norm_num
  let α : Fin 1 → ℂ := fun _ => (Fintype.card K : ℂ)
  let b : ℕ → ℂ := fun n => -rootPowerCoefficient α n
  let f : ℂ → ℂ := fun z => (Fintype.card K : ℂ) * z / (1 - (Fintype.card K : ℂ) * z)
  have ha := summable_norm_primePowerCoefficient (1 : K[X]) monic_one 1 r hr hqr
  have hb : Summable (fun n => ‖b n‖ * r ^ n) := by
    have h := summable_norm_rootPowerCoefficient α r hr.le (fun i => by
      simpa only [α, Complex.norm_natCast, q] using hqr)
    simpa only [b, norm_neg] using h
  have hfb : ∀ z : ℂ, ‖z‖ < r → HasSum (fun n => b n * z ^ n) (f z) := by
    intro z hz
    have hsmall : (Fintype.card K : ℝ) * ‖z‖ < 1 :=
      (mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr
    have h := (hasSum_rootPowerCoefficient α z (fun i => by
      simpa only [α, norm_mul, Complex.norm_natCast] using hsmall)).neg
    have hs : HasSum (fun n => b n * z ^ n) (-(∑ i, contribution (α i * z))) := by
      apply h.congr_fun
      intro d
      exact neg_mul _ _
    simpa only [f, α, Fin.sum_univ_one, contribution, neg_div, neg_neg] using hs
  have heq := scalar_coefficients_eq (primePowerCoefficient (1 : K[X]) 1) b f r hr ha hb
    (fun z hz => hasSum_zeta_primePowerCoefficient r hr hqr z hz) hfb
  simpa only [b, rootPowerCoefficient, if_neg hn.ne', neg_neg, α, Fin.sum_univ_one] using congrFun heq n

theorem zeta_primeCharacterSum (n : ℕ) :
    primeCharacterSum (1 : K[X]) 1 n = Fintype.card (PrimeDegree K n) := by
  simp [primeCharacterSum, trivial_modulus_character]

/-- A coarse explicit prime polynomial theorem, sufficient for the construction. -/
theorem abs_primeDegree_count_error_le (n : ℕ) (hn : 0 < n) :
    |(n : ℝ) * Fintype.card (PrimeDegree K n) - (Fintype.card K : ℝ) ^ n| ≤
      (n : ℝ) * (n / 2 + 1 : ℕ) * (Fintype.card K : ℝ) ^ (n / 2) := by
  have h := primePowerCoefficient_split (1 : K[X]) 1 n
  rw [zeta_primePowerCoefficient n hn, zeta_primeCharacterSum] at h
  have heq : (n : ℂ) * Fintype.card (PrimeDegree K n) - (Fintype.card K : ℂ) ^ n =
      -properPrimePowerSum (1 : K[X]) 1 n := by
    linear_combination -h
  have hnorm := norm_properPrimePowerSum_le (1 : K[X]) monic_one 1 n
  rw [← norm_neg, ← heq] at hnorm
  have hcast : ((n : ℂ) * Fintype.card (PrimeDegree K n) - (Fintype.card K : ℂ) ^ n) =
      (((n : ℝ) * Fintype.card (PrimeDegree K n) - (Fintype.card K : ℝ) ^ n : ℝ) : ℂ) := by
    push_cast
    rfl
  rw [hcast, Complex.norm_real, Real.norm_eq_abs] at hnorm
  exact hnorm

end Erdos157.Elementary.PolynomialCharacters
