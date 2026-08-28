import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalarPolynomial
import Mathlib.FieldTheory.RatFunc.AsPolynomial
import Mathlib.Topology.Separation.Basic

/-!
# Rational functions representing scalar polynomial-quotient germs

`RatFunc.eval` evaluates a reduced fraction. Consequently it need not equal
an unreduced polynomial quotient at a canceled root. Here the comparison
is made away from the denominator's finite root set and hence in every
punctured-neighborhood germ.
-/

noncomputable section

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar

open Filter
open scoped Topology Polynomial

/-- The actual rational-function field element represented by `P / Q`. -/
def polynomialQuotientRatFunc (P Q : Polynomial ℂ) : RatFunc ℂ :=
  algebraMap (Polynomial ℂ) (RatFunc ℂ) P /
    algebraMap (Polynomial ℂ) (RatFunc ℂ) Q

/-- A nonzero polynomial is nonvanishing in every punctured-neighborhood
germ, since its set of roots is finite. -/
theorem polynomial_eval_eventually_ne_zero
    (Q : Polynomial ℂ) (hQ : Q ≠ 0) (z : ℂ) :
    ∀ᶠ w in 𝓝[≠] z, Q.eval w ≠ 0 := by
  have h := (Polynomial.finite_setOfPred_isRoot hQ).eventually_cofinite_notMem
  simpa only [Set.mem_ofPred_eq, Polynomial.IsRoot] using
    h.filter_mono (nhdsNE_le_cofinite z)

/-- Reduction of the fraction does not change its value where the original
denominator is nonzero. -/
theorem polynomialQuotientRatFunc_eval_of_denominator_ne_zero
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (z : ℂ) (hz : Q.eval z ≠ 0) :
    RatFunc.eval (RingHom.id ℂ) z (polynomialQuotientRatFunc P Q) =
      P.eval z / Q.eval z := by
  let r := polynomialQuotientRatFunc P Q
  have hdenom : r.denom ∣ Q := RatFunc.denom_div_dvd P Q
  have hrz : r.denom.eval z ≠ 0 := by
    intro hzero
    exact hz (Polynomial.eval_eq_zero_of_dvd_of_eval_eq_zero hdenom hzero)
  have hcross : r.num * Q = P * r.denom :=
    (RatFunc.num_mul_eq_mul_denom_iff hQ).mpr rfl
  change r.num.eval z / r.denom.eval z = P.eval z / Q.eval z
  apply (div_eq_div_iff hrz hz).mpr
  simpa only [Polynomial.eval_mul] using congrArg (Polynomial.eval z) hcross

/-- The unreduced quotient and the canonical evaluation of its rational
function represent the same germ at every finite point, including poles
and canceled roots. -/
theorem polynomialQuotient_eventuallyEq_ratFunc
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) (z : ℂ) :
    (fun w => P.eval w / Q.eval w) =ᶠ[𝓝[≠] z]
      (fun w => RatFunc.eval (RingHom.id ℂ) w (polynomialQuotientRatFunc P Q)) := by
  filter_upwards [polynomial_eval_eventually_ne_zero Q hQ z] with w hw
  exact (polynomialQuotientRatFunc_eval_of_denominator_ne_zero P Q hQ w hw).symm

/-- Every quotient with a nonzero denominator polynomial is represented
by one actual `RatFunc ℂ`, simultaneously in all finite punctured germs. -/
theorem exists_ratFunc_polynomial_quotient
    (P Q : Polynomial ℂ) (hQ : Q ≠ 0) :
    ∃ r : RatFunc ℂ, ∀ z : ℂ,
      (fun w => P.eval w / Q.eval w) =ᶠ[𝓝[≠] z]
        (fun w => RatFunc.eval (RingHom.id ℂ) w r) :=
  ⟨polynomialQuotientRatFunc P Q, polynomialQuotient_eventuallyEq_ratFunc P Q hQ⟩

/-- The finite-divisor construction, with an arbitrary scalar multiplier,
defines an actual rational function with the same finite meromorphic germs. -/
theorem exists_ratFunc_const_mul_factorizedRational
    (c : ℂ) (d : ℂ → ℤ) (hd : d.HasFiniteSupport) :
    ∃ r : RatFunc ℂ, ∀ z : ℂ,
      (fun w => c * (∏ᶠ u, (· - u) ^ d u) w) =ᶠ[𝓝[≠] z]
        (fun w => RatFunc.eval (RingHom.id ℂ) w r) := by
  obtain ⟨P, Q, hQ, heval⟩ :=
    exists_polynomial_quotient_const_mul_factorizedRational c d hd
  obtain ⟨r, hr⟩ := exists_ratFunc_polynomial_quotient P Q hQ
  refine ⟨r, fun z => ?_⟩
  filter_upwards [hr z] with w hw
  exact (heval w).trans hw

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar
