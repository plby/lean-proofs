import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluationGerm
import Mathlib.Algebra.Polynomial.Eval.Defs

/-!
# Polynomial and rational expressions in native sphere functions

Evaluating a complex polynomial in an actual native meromorphic
function agrees, as a punctured scalar germ, with evaluating it in the
ordinary representative.  Quotients satisfy the same comparison,
including zero polynomial denominators under total field division.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation

open SphereRepresentative

attribute [local instance] sphereDomain_connected

/-- Polynomial evaluation in the original native meromorphic section
ring agrees with scalar polynomial evaluation on every punctured germ. -/
theorem finiteValue_polynomial_eval_eventuallyEq (p : Polynomial ℂ)
    (s : SphereFunction) (z : ℂ) :
    finiteValue (p.eval₂ (algebraMap ℂ SphereFunction) s) =ᶠ[𝓝[≠] z]
      (fun w => p.eval (finiteValue s w)) := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq =>
    filter_upwards [finiteValue_add_eventuallyEq
      (p.eval₂ (algebraMap ℂ SphereFunction) s)
      (q.eval₂ (algebraMap ℂ SphereFunction) s) z, hp, hq] with w hadd hpw hqw
    rw [Polynomial.eval₂_add, hadd, hpw, hqw, Polynomial.eval_add]
  | monomial k c =>
    filter_upwards [finiteValue_mul_eventuallyEq (algebraMap ℂ SphereFunction c) (s ^ k) z,
      finiteValue_pow_eventuallyEq s k z] with w hmul hpow
    rw [Polynomial.eval₂_monomial, hmul, finiteValue_algebraMap, hpow,
      Polynomial.eval_monomial]

/-- Quotients of polynomial expressions in a native function have the
literal scalar quotient as their punctured representative. -/
theorem finiteValue_polynomial_div_eventuallyEq (p q : Polynomial ℂ)
    (s : SphereFunction) (z : ℂ) :
    finiteValue (p.eval₂ (algebraMap ℂ SphereFunction) s /
        q.eval₂ (algebraMap ℂ SphereFunction) s) =ᶠ[𝓝[≠] z]
      (fun w => p.eval (finiteValue s w) / q.eval (finiteValue s w)) := by
  filter_upwards [finiteValue_div_eventuallyEq
    (p.eval₂ (algebraMap ℂ SphereFunction) s) (q.eval₂ (algebraMap ℂ SphereFunction) s) z,
    finiteValue_polynomial_eval_eventuallyEq p s z,
    finiteValue_polynomial_eval_eventuallyEq q s z] with w hdiv hp hq
  rw [hdiv, hp, hq]

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation
