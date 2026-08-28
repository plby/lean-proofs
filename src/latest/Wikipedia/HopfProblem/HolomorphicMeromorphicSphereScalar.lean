import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalarFactorization
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalarPolynomial
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereScalarRatFunc

/-!
# Scalar meromorphic functions on the sphere are rational

The two assumptions are meromorphicity in the finite coordinate and at the
origin of the reciprocal coordinate.  Both use Mathlib's analytic definition
of meromorphicity.  The conclusion supplies actual complex polynomials with
nonzero denominator and equality of germs in both charts.  It deliberately
does not assert equality of the arbitrarily assigned values at poles.
-/

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar

open Filter Set Function
open scoped Topology

/-- If two functions meromorphic at infinity have the same finite germs,
their infinity germs also agree.  Meromorphicity at infinity is necessary:
arbitrary isolated changes on an unbounded discrete set would otherwise
invalidate this assertion. -/
theorem eventuallyEq_at_infinity_of_finite_germs {f g : ℂ → ℂ}
    (hf : MeromorphicAt (fun z => f z⁻¹) 0)
    (hg : MeromorphicAt (fun z => g z⁻¹) 0)
    (hfg : ∀ z : ℂ, f =ᶠ[𝓝[≠] z] g) :
    (fun z => f z⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)] (fun z => g z⁻¹) := by
  filter_upwards [hf.eventually_analyticAt, hg.eventually_analyticAt,
    self_mem_nhdsWithin] with z hfz hgz hz0
  have hz0' : z ≠ 0 := hz0
  have hfa : AnalyticAt ℂ f z⁻¹ := by
    have h : AnalyticAt ℂ (fun w => f w⁻¹) (z⁻¹)⁻¹ := by
      simpa only [inv_inv] using hfz
    simpa only [Function.comp_def, inv_inv] using
      h.comp (analyticAt_id.inv (inv_ne_zero hz0'))
  have hga : AnalyticAt ℂ g z⁻¹ := by
    have h : AnalyticAt ℂ (fun w => g w⁻¹) (z⁻¹)⁻¹ := by
      simpa only [inv_inv] using hgz
    simpa only [Function.comp_def, inv_inv] using
      h.comp (analyticAt_id.inv (inv_ne_zero hz0'))
  exact ((hfa.continuousAt.eventuallyEq_nhds_iff_eventuallyEq_nhdsNE hga.continuousAt).1
    (hfg z⁻¹)).eq_of_nhds

/-- Rationality of scalar meromorphic functions on the Riemann sphere,
including agreement of the reciprocal-coordinate germs. -/
theorem exists_polynomial_quotient_in_both_charts {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      (∀ z : ℂ, f =ᶠ[𝓝[≠] z] (fun w => P.eval w / Q.eval w)) ∧
      (fun z => f z⁻¹) =ᶠ[𝓝[≠] (0 : ℂ)]
        (fun z => P.eval z⁻¹ / Q.eval z⁻¹) := by
  obtain ⟨c, hc⟩ := exists_const_mul_factorizedRational hf hinf
  let d : ℂ → ℤ := MeromorphicOn.divisor f univ
  have hd : d.HasFiniteSupport := divisor_support_finite hf hinf
  obtain ⟨P, Q, hQ, hPQ⟩ :=
    exists_polynomial_quotient_const_mul_factorizedRational c d hd
  have hfinite : ∀ z : ℂ, f =ᶠ[𝓝[≠] z] (fun w => P.eval w / Q.eval w) := by
    intro z
    filter_upwards [hc z] with w hw
    exact hw.trans (hPQ w)
  refine ⟨P, Q, hQ, hfinite, ?_⟩
  apply eventuallyEq_at_infinity_of_finite_germs hinf _ hfinite
  have hmer : MeromorphicAt
      (fun z => c * (∏ᶠ u, (· - u) ^ d u) z⁻¹) 0 :=
    (MeromorphicAt.const c 0).mul (factorizedRational_meromorphicAt_infinity d hd)
  exact hmer.congr (Eventually.of_forall fun z => hPQ z⁻¹)

/-- The finite-germ formulation of sphere rationality, convenient for mapping
the polynomial quotient into a field of meromorphic sections. -/
theorem exists_polynomial_quotient {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    ∃ P Q : Polynomial ℂ, Q ≠ 0 ∧
      ∀ z : ℂ, f =ᶠ[𝓝[≠] z] (fun w => P.eval w / Q.eval w) := by
  obtain ⟨P, Q, hQ, hfinite, _⟩ := exists_polynomial_quotient_in_both_charts hf hinf
  exact ⟨P, Q, hQ, hfinite⟩

/-- The same rationality assertion with an actual Mathlib rational-function
witness.  Evaluation uses the reduced numerator and denominator, so equality
is again asserted for germs rather than potentially canceled point values. -/
theorem exists_ratFunc {f : ℂ → ℂ}
    (hf : MeromorphicOn f univ) (hinf : MeromorphicAt (fun z => f z⁻¹) 0) :
    ∃ r : RatFunc ℂ, ∀ z : ℂ, f =ᶠ[𝓝[≠] z]
      (fun w => RatFunc.eval (RingHom.id ℂ) w r) := by
  obtain ⟨P, Q, hQ, hfinite⟩ := exists_polynomial_quotient hf hinf
  obtain ⟨r, hr⟩ := exists_ratFunc_polynomial_quotient P Q hQ
  exact ⟨r, fun z => (hfinite z).trans (hr z)⟩

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereScalar
