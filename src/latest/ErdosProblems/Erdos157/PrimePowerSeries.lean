import ErdosProblems.Erdos157.GradedSeries
import ErdosProblems.Erdos157.EulerPrimeTerms

/-! Weighted prime-power coefficients of the polynomial logarithmic derivative. -/

namespace Erdos157.Elementary.PolynomialCharacters

open Polynomial

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

def primePowerDegree (i : PrimePolynomial K × ℕ) : ℕ := i.1.1.natDegree * (i.2 + 1)

noncomputable def primePowerWeight (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ)
    (i : PrimePolynomial K × ℕ) : ℂ :=
  (i.1.1.natDegree : ℂ) * χ (AdjoinRoot.mk g i.1.1) ^ (i.2 + 1)

noncomputable def primePowerCoefficient (g : K[X]) (χ : MulChar (AdjoinRoot g) ℂ) (n : ℕ) : ℂ :=
  gradedCoefficient primePowerDegree (primePowerWeight g χ) n

theorem hasSum_real_geometric_succ (t : ℝ) (ht : 0 ≤ t) (ht1 : t < 1) :
    HasSum (fun k : ℕ => t ^ (k + 1)) (t / (1 - t)) := by
  have h := (hasSum_geometric_of_lt_one ht ht1).mul_left t
  simpa only [pow_succ', div_eq_mul_inv] using h

theorem summable_primePower_majorant (r : ℝ) (hr : 0 ≤ r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun i : PrimePolynomial K × ℕ =>
      (i.1.1.natDegree : ℝ) * (r ^ i.1.1.natDegree) ^ (i.2 + 1)) := by
  have htwo : (2 : ℝ) ≤ Fintype.card K := by exact_mod_cast Fintype.one_lt_card (α := K)
  have hrhalf : r < 1 / 2 := by
    have := mul_le_mul_of_nonneg_right htwo hr
    linarith
  have hrone : r < 1 := by linarith
  have hp : ∀ p : PrimePolynomial K, r ^ p.1.natDegree ≤ r := by
    intro p
    exact pow_le_of_le_one hr hrone.le (ne_of_gt (primePolynomial_degree_pos p))
  have hp_lt : ∀ p : PrimePolynomial K, r ^ p.1.natDegree < 1 :=
    fun p => (hp p).trans_lt hrone
  apply (summable_prod_of_nonneg (fun i => by positivity)).mpr
  refine ⟨?_, ?_⟩
  · intro p
    have hs : Summable (fun k : ℕ => (r ^ p.1.natDegree) ^ (k + 1)) :=
      (hasSum_real_geometric_succ _ (by positivity) (hp_lt p)).summable
    exact hs.mul_left (p.1.natDegree : ℝ)
  · apply Summable.of_nonneg_of_le (fun p => tsum_nonneg (fun _ => by positivity))
      (f := fun p : PrimePolynomial K => 2 * ((p.1.natDegree : ℝ) * r ^ p.1.natDegree))
    · intro p
      have hgeom : (∑' k : ℕ, (r ^ p.1.natDegree) ^ (k + 1)) =
          r ^ p.1.natDegree / (1 - r ^ p.1.natDegree) :=
        (hasSum_real_geometric_succ _ (by positivity) (hp_lt p)).tsum_eq
      dsimp only at ⊢
      rw [tsum_mul_left, hgeom, ← mul_div_assoc]
      apply (div_le_iff₀ (by linarith [hp_lt p] : 0 < 1 - r ^ p.1.natDegree)).mpr
      have hden : (1 / 2 : ℝ) ≤ 1 - r ^ p.1.natDegree := by linarith [hp p]
      have hmul := mul_le_mul_of_nonneg_left hden
        (by positivity : 0 ≤ 2 * ((p.1.natDegree : ℝ) * r ^ p.1.natDegree))
      nlinarith
    · exact (summable_prime_degree_weight (K := K) r hr hqr).mul_left 2

theorem summable_norm_primePowerWeight (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 ≤ r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun i : PrimePolynomial K × ℕ =>
      ‖primePowerWeight g χ i‖ * r ^ primePowerDegree i) := by
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  apply Summable.of_nonneg_of_le (fun i => by positivity)
    (f := fun i : PrimePolynomial K × ℕ =>
      (i.1.1.natDegree : ℝ) * (r ^ i.1.1.natDegree) ^ (i.2 + 1))
  · intro i
    rw [primePowerWeight, norm_mul, Complex.norm_natCast, norm_pow, primePowerDegree, pow_mul]
    apply mul_le_mul_of_nonneg_right
    · exact mul_le_of_le_one_right (by positivity)
        (pow_le_one₀ (norm_nonneg _) (character_norm_le_one χ _))
    · positivity
  · exact summable_primePower_majorant r hr hqr

theorem summable_norm_primePowerCoefficient (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) :
    Summable (fun n => ‖primePowerCoefficient g χ n‖ * r ^ n) :=
  summable_gradedCoefficient primePowerDegree (primePowerWeight g χ) r hr
    (summable_norm_primePowerWeight g hg χ r hr.le hqr)

theorem hasSum_primePowerTerm (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (p : PrimePolynomial K) (z : ℂ)
    (hz : (Fintype.card K : ℝ) * ‖z‖ < 1) :
    HasSum (fun k : ℕ => primePowerWeight g χ (p, k) * z ^ primePowerDegree (p, k))
      (primeEulerTerm g χ p z) := by
  have h := (ElementaryCharacterBound.hasSum_geometric_succ
    (primeWeight_norm_lt_one g hg χ z hz p)).mul_left (p.1.natDegree : ℂ)
  apply h.congr_fun
  intro k
  simp only [primePowerWeight, primePowerDegree, primeWeight, mul_pow, pow_mul]
  ring

theorem hasSum_primePowerCoefficient (g : K[X]) (hg : g.Monic)
    (χ : MulChar (AdjoinRoot g) ℂ) (hχ : χ ≠ 1) (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    HasSum (fun n => primePowerCoefficient g χ n * z ^ n)
      (z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z)) := by
  have hsmall : (Fintype.card K : ℝ) * ‖z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr
  have habs := summable_norm_primePowerWeight g hg χ ‖z‖ (norm_nonneg z) hsmall
  have hs : Summable (fun i : PrimePolynomial K × ℕ => primePowerWeight g χ i * z ^ primePowerDegree i) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow] using habs
  have htotal : (∑' i : PrimePolynomial K × ℕ, primePowerWeight g χ i * z ^ primePowerDegree i) =
      z * ((lPolynomial g χ).derivative.eval z / (lPolynomial g χ).eval z) := by
    rw [hs.tsum_prod]
    simp_rw [(hasSum_primePowerTerm g hg χ _ z hsmall).tsum_eq]
    exact sum_primeEulerTerm g hg χ hχ r hr hqr z hz
  have h := hasSum_gradedCoefficient primePowerDegree (primePowerWeight g χ) r hr
    (summable_norm_primePowerWeight g hg χ r hr.le hqr) z hz.le
  rwa [htotal] at h

/-- The principal zeta specialization, whose logarithmic derivative is rational. -/
theorem hasSum_zeta_primePowerCoefficient (r : ℝ) (hr : 0 < r)
    (hqr : (Fintype.card K : ℝ) * r < 1) (z : ℂ) (hz : ‖z‖ < r) :
    HasSum (fun n => primePowerCoefficient (1 : K[X]) 1 n * z ^ n)
      ((Fintype.card K : ℂ) * z / (1 - (Fintype.card K : ℂ) * z)) := by
  have hsmall : (Fintype.card K : ℝ) * ‖z‖ < 1 :=
    (mul_le_mul_of_nonneg_left hz.le (by positivity)).trans_lt hqr
  have habs := summable_norm_primePowerWeight (1 : K[X]) monic_one 1 ‖z‖ (norm_nonneg z) hsmall
  have hs : Summable (fun i : PrimePolynomial K × ℕ => primePowerWeight 1 1 i * z ^ primePowerDegree i) := by
    apply Summable.of_norm
    simpa only [norm_mul, norm_pow] using habs
  have htotal : (∑' i : PrimePolynomial K × ℕ, primePowerWeight 1 1 i * z ^ primePowerDegree i) =
      (Fintype.card K : ℂ) * z / (1 - (Fintype.card K : ℂ) * z) := by
    rw [hs.tsum_prod]
    simp_rw [(hasSum_primePowerTerm (1 : K[X]) monic_one 1 _ z hsmall).tsum_eq]
    exact sum_zeta_primeEulerTerm r hr hqr z hz
  have h := hasSum_gradedCoefficient primePowerDegree (primePowerWeight (1 : K[X]) 1) r hr
    (summable_norm_primePowerWeight (1 : K[X]) monic_one 1 r hr.le hqr) z hz.le
  rwa [htotal] at h

end Erdos157.Elementary.PolynomialCharacters
