import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluationArithmetic
import Mathlib.Order.Filter.Germ.Basic

/-!
# The genuine scalar punctured-germ evaluation homomorphism

The forward map sends a native meromorphic sphere function to the
punctured germ of its already defined finite ordinary representative.
The native arithmetic identities prove it is a ring homomorphism, and
the proved native identity theorem proves injectivity.  It also respects
total inverse and division on its image.  The ambient ring of all scalar
punctured germs is not asserted to be a field.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation

open SphereRepresentative

attribute [local instance] sphereDomain_connected

/-- The ordinary finite representative, in the actual ring of punctured scalar germs. -/
def finiteGermRingHom (z : ℂ) : SphereFunction →+* Filter.Germ (𝓝[≠] z) ℂ where
  toFun s := (finiteValue s : Filter.Germ (𝓝[≠] z) ℂ)
  map_zero' := Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall finiteValue_zero)
  map_one' := Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall finiteValue_one)
  map_add' s t := Filter.Germ.coe_eq.mpr (finiteValue_add_eventuallyEq s t z)
  map_mul' s t := Filter.Germ.coe_eq.mpr (finiteValue_mul_eventuallyEq s t z)

@[simp] theorem finiteGermRingHom_apply (z : ℂ) (s : SphereFunction) :
    finiteGermRingHom z s = (finiteValue s : Filter.Germ (𝓝[≠] z) ℂ) := rfl

/-- One scalar punctured germ detects the entire original native section. -/
theorem finiteGermRingHom_injective (z : ℂ) : _root_.Function.Injective (finiteGermRingHom z) := by
  intro s t h
  exact eq_of_finiteValue_eventuallyEq s t z (Filter.Germ.coe_eq.mp h)

/-- Complex constants retain their actual constant scalar germ. -/
@[simp] theorem finiteGermRingHom_algebraMap (z c : ℂ) :
    finiteGermRingHom z (algebraMap ℂ SphereFunction c) =
      ((fun _ : ℂ => c) : Filter.Germ (𝓝[≠] z) ℂ) :=
  Filter.Germ.coe_eq.mpr (Filter.Eventually.of_forall (finiteValue_algebraMap c))

/-- Although all scalar germs do not form a field, native total inverse
is carried to the genuine pointwise inverse operation on those germs. -/
@[simp] theorem finiteGermRingHom_inv (z : ℂ) (s : SphereFunction) :
    finiteGermRingHom z s⁻¹ = (finiteGermRingHom z s)⁻¹ :=
  Filter.Germ.coe_eq.mpr (finiteValue_inv_eventuallyEq s z)

/-- Native total division is carried to scalar germ division, including zero denominators. -/
@[simp] theorem finiteGermRingHom_div (z : ℂ) (s t : SphereFunction) :
    finiteGermRingHom z (s / t) = finiteGermRingHom z s / finiteGermRingHom z t :=
  Filter.Germ.coe_eq.mpr (finiteValue_div_eventuallyEq s t z)

/-- All nonnegative powers also agree as actual punctured scalar germs. -/
theorem finiteValue_pow_eventuallyEq (s : SphereFunction) (k : ℕ) (z : ℂ) :
    finiteValue (s ^ k) =ᶠ[𝓝[≠] z] (fun w => finiteValue s w ^ k) := by
  apply Filter.Germ.coe_eq.mp
  change finiteGermRingHom z (s ^ k) = (finiteGermRingHom z s) ^ k
  exact map_pow (finiteGermRingHom z) s k

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation
