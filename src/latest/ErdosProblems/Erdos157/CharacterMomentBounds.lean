import ErdosProblems.Erdos157.CharacterEulerProduct

/-! Summable degree weights for differentiating the Euler logarithmic series. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

omit [DecidableEq K] in
theorem summable_monic_degree_weight (r : ℝ) (hr : 0 ≤ r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun f : AllMonic K => (f.1 : ℝ) * r ^ f.1) := by
  have hgeom : Summable (fun d : ℕ => (d : ℝ) * ((Fintype.card K : ℝ) * r) ^ d) := by
    have hnorm : ‖(Fintype.card K : ℝ) * r‖ < 1 := by
      rwa [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
    simpa only [pow_one] using summable_pow_mul_geometric_of_norm_lt_one 1 hnorm
  apply (summable_sigma_of_nonneg (fun f => by positivity)).mpr
  refine ⟨fun d => (hasSum_fintype _).summable, ?_⟩
  convert hgeom using 1
  funext d
  rw [tsum_fintype]
  simp only [Finset.sum_const, Finset.card_univ, smul_eq_mul, card_monic, Nat.cast_pow, mul_pow]
  ring

/-- Regard a prime polynomial as a monic polynomial with its degree recorded. -/
noncomputable def primeToAllMonic (p : PrimePolynomial K) : AllMonic K :=
  ⟨p.1.natDegree, MonicDegreeEq.mk p.1 p.2.1 rfl⟩

omit [DecidableEq K] [Fintype K] in
theorem primeToAllMonic_injective : Function.Injective (primeToAllMonic (K := K)) := by
  intro p q hpq
  apply Subtype.ext
  exact congrArg (fun f : AllMonic K => f.2.1) hpq

theorem summable_prime_degree_weight (r : ℝ) (hr : 0 ≤ r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun p : PrimePolynomial K => (p.1.natDegree : ℝ) * r ^ p.1.natDegree) := by
  have h := (summable_monic_degree_weight (K := K) r hr hqr).comp_injective
    primeToAllMonic_injective
  simpa only [Function.comp_def, primeToAllMonic] using h

/-- The derivative majorant remains summable on every smaller disk. -/
theorem summable_prime_derivative_weight (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun p : PrimePolynomial K => (p.1.natDegree : ℝ) * r ^ (p.1.natDegree - 1)) := by
  have h := (summable_prime_degree_weight (K := K) r hr.le hqr).div_const r
  apply h.congr
  intro p
  have hd : p.1.natDegree = (p.1.natDegree - 1) + 1 := by
    have := primePolynomial_degree_pos p
    omega
  have hpow : r ^ p.1.natDegree = r ^ (p.1.natDegree - 1) * r := by
    nth_rw 1 [hd]
    rw [pow_succ]
  rw [hpow, mul_div_assoc, mul_div_cancel_right₀ _ hr.ne']

end Erdos157.Elementary.PolynomialCharacters
