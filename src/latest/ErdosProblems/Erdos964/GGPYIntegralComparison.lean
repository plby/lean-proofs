import ErdosProblems.Erdos964.SievePolynomial

/-!
# Matching the verified integral certificate to the GGPY paper

The polynomial in the proof of Theorem 2 of arXiv:math/0609615 is
`P(x)=1+6x`. Under `x=1-s` it is our radial candidate. These identities
match its three face integrals and its first moment to the certificate.
-/

namespace Erdos964

def ggpyPolynomial (x : ℝ) : ℝ := 1 + 6 * x

def ggpyPolynomialPrimitive (x : ℝ) : ℝ := x + 3 * x ^ 2

theorem ggpyPolynomial_reflection (s : ℝ) :
    ggpyPolynomial (1 - s) = linearSieveWeight s := by
  dsimp [ggpyPolynomial, linearSieveWeight]
  ring

theorem ggpyPolynomialPrimitive_integral (x : ℝ) :
    (∫ t in (0 : ℝ)..x, ggpyPolynomial t) = ggpyPolynomialPrimitive x := by
  have hpoly : ggpyPolynomial = (fun t : ℝ => 1 + 6 * t ^ 1) := by
    funext t
    simp only [ggpyPolynomial, pow_one]
  rw [hpoly]
  simp (disch := (apply Continuous.intervalIntegrable; fun_prop)) only
    [intervalIntegral.integral_add, intervalIntegral.integral_const_mul,
      intervalIntegral.integral_const, integral_pow]
  dsimp [ggpyPolynomialPrimitive]
  ring

theorem ggpy_first_moment_eq :
    (∫ x in (0 : ℝ)..1, ggpyPolynomial (1 - x) ^ 2 * x ^ 2) = 38 / 15 := by
  have hfun : (fun x : ℝ => ggpyPolynomial (1 - x) ^ 2 * x ^ 2) =
      (fun x => 2 * (x ^ 2 / 2 * linearSieveWeight x ^ 2)) := by
    funext x
    rw [ggpyPolynomial_reflection]
    ring
  rw [hfun, intervalIntegral.integral_const_mul]
  change 2 * linearSieveMass = _
  rw [linearSieveMass_eq]
  norm_num

theorem truncatedSieveFace_eq_ggpy (z : ℝ) :
    truncatedSieveFace z =
      (∫ x in (0 : ℝ)..(1 - z),
        (ggpyPolynomialPrimitive (1 - x) - ggpyPolynomialPrimitive (1 - x - z)) ^ 2 * x) +
      ∫ x in (1 - z)..1, ggpyPolynomialPrimitive (1 - x) ^ 2 * x := by
  unfold truncatedSieveFace
  congr 1 <;> apply intervalIntegral.integral_congr <;> intro x _ <;>
    dsimp [ggpyPolynomialPrimitive] <;> ring

theorem ggpy_face_integrand_eq (a z : ℝ) :
    truncatedSieveFace z / (z * (1 - a * z)) = sieveFaceKernel z / (1 - a * z) := by
  rw [truncatedSieveFace_eq]
  by_cases hz : z = 0
  · simp [hz, sieveFaceKernel]
  · exact mul_div_mul_left _ _ hz

/-- The positive certificate in the normalization used in GGPY's proof
of Theorem 2, with our smaller cutoff and strictly subcritical radius. -/
theorem ggpy_integral_positive_margin :
    (∫ x in (0 : ℝ)..1, ggpyPolynomial (1 - x) ^ 2 * x ^ 2) + 1 / 5000 <
      6 * sieveRadiusExponent *
        ((∫ z in (1 / 100 : ℝ)..1,
          truncatedSieveFace z / (z * (1 - sieveRadiusExponent * z))) +
          Real.log ((1 - sieveRadiusExponent) / sieveRadiusExponent) * truncatedSieveFace 1) := by
  simp_rw [ggpy_face_integrand_eq]
  rw [ggpy_first_moment_eq]
  have h := subcritical_sieve_integral_positive_margin
  rw [linearSieveMass_eq] at h
  change 38 / 15 + 1 / 5000 < 6 * sieveRadiusExponent *
    (subcriticalSemiprimeIntegral +
      Real.log ((1 - sieveRadiusExponent) / sieveRadiusExponent) * truncatedSieveFace 1)
  linarith

end Erdos964
