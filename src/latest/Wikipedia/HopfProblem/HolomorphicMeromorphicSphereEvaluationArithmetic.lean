import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluationBasic
import Wikipedia.HopfProblem.HolomorphicMeromorphicSphereEvaluationRegular

/-!
# Native field arithmetic on punctured scalar representatives

The canonical ordinary values of native sphere functions need not
preserve sums or products at poles.  They do preserve the actual field
operations on every sufficiently small punctured neighborhood.  For
inversion, a nonzero native section is nonzero there; the zero section
is treated using the native field's total inverse.
-/

noncomputable section

open Set Filter Topology TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation

open SphereRepresentative

local instance sphereDomain_connected : ConnectedSpace (⊤ : Opens RiemannSphere) :=
  Subtype.connectedSpace isConnected_univ

@[simp] theorem finiteValue_zero (z : ℂ) : finiteValue (0 : SphereFunction) z = 0 :=
  value_zero 𝓘(ℂ) RiemannSphere ⊤ ⟨(z : RiemannSphere), by trivial⟩

@[simp] theorem finiteValue_one (z : ℂ) : finiteValue (1 : SphereFunction) z = 1 :=
  value_one 𝓘(ℂ) RiemannSphere ⊤ ⟨(z : RiemannSphere), by trivial⟩

/-- Complex constants have their exact original value, with no exceptional points. -/
@[simp] theorem finiteValue_algebraMap (c z : ℂ) :
    finiteValue (algebraMap ℂ SphereFunction c) z = c :=
  value_algebraMap 𝓘(ℂ) RiemannSphere ⊤ c ⟨(z : RiemannSphere), by trivial⟩

/-- Native addition is ordinary addition on every punctured scalar germ. -/
theorem finiteValue_add_eventuallyEq (s t : SphereFunction) (z : ℂ) :
    finiteValue (s + t) =ᶠ[𝓝[≠] z] (fun w => finiteValue s w + finiteValue t w) := by
  filter_upwards [finiteValue_eventually_regularAt s z,
    finiteValue_eventually_regularAt t z] with w hs ht
  exact value_add_of_regularAt 𝓘(ℂ) RiemannSphere ⊤ s t
    ⟨(w : RiemannSphere), by trivial⟩ hs ht

/-- Native multiplication is ordinary multiplication on every punctured scalar germ. -/
theorem finiteValue_mul_eventuallyEq (s t : SphereFunction) (z : ℂ) :
    finiteValue (s * t) =ᶠ[𝓝[≠] z] (fun w => finiteValue s w * finiteValue t w) := by
  filter_upwards [finiteValue_eventually_regularAt s z,
    finiteValue_eventually_regularAt t z] with w hs ht
  exact value_mul_of_regularAt 𝓘(ℂ) RiemannSphere ⊤ s t
    ⟨(w : RiemannSphere), by trivial⟩ hs ht

/-- Native negation is ordinary negation on every punctured scalar germ. -/
theorem finiteValue_neg_eventuallyEq (s : SphereFunction) (z : ℂ) :
    finiteValue (-s) =ᶠ[𝓝[≠] z] (fun w => -finiteValue s w) := by
  filter_upwards [finiteValue_eventually_regularAt s z] with w hs
  exact value_neg_of_regularAt 𝓘(ℂ) RiemannSphere ⊤ s
    ⟨(w : RiemannSphere), by trivial⟩ hs

/-- Native subtraction is ordinary subtraction on every punctured scalar germ. -/
theorem finiteValue_sub_eventuallyEq (s t : SphereFunction) (z : ℂ) :
    finiteValue (s - t) =ᶠ[𝓝[≠] z] (fun w => finiteValue s w - finiteValue t w) := by
  filter_upwards [finiteValue_add_eventuallyEq s (-t) z,
    finiteValue_neg_eventuallyEq t z] with w hadd hneg
  rw [sub_eq_add_neg, hadd, hneg, sub_eq_add_neg]

/-- Total native inversion agrees with total scalar inversion as a punctured germ,
including for the zero meromorphic section. -/
theorem finiteValue_inv_eventuallyEq (s : SphereFunction) (z : ℂ) :
    finiteValue s⁻¹ =ᶠ[𝓝[≠] z] (fun w => (finiteValue s w)⁻¹) := by
  by_cases hs : s = 0
  · subst s
    exact Filter.Eventually.of_forall fun w => by simp
  · filter_upwards [finiteValue_eventually_regularAt s z,
      finiteValue_eventually_ne_zero s hs z] with w hreg hne
    exact value_inv_of_regularAt_ne_zero 𝓘(ℂ) RiemannSphere ⊤ s
      ⟨(w : RiemannSphere), by trivial⟩ hreg hne

/-- Division is preserved as a punctured germ even if the denominator section is zero. -/
theorem finiteValue_div_eventuallyEq (s t : SphereFunction) (z : ℂ) :
    finiteValue (s / t) =ᶠ[𝓝[≠] z] (fun w => finiteValue s w / finiteValue t w) := by
  filter_upwards [finiteValue_mul_eventuallyEq s t⁻¹ z,
    finiteValue_inv_eventuallyEq t z] with w hmul hinv
  calc
    finiteValue (s / t) w = finiteValue (s * t⁻¹) w := by rw [div_eq_mul_inv]
    _ = finiteValue s w * finiteValue t⁻¹ w := hmul
    _ = finiteValue s w * (finiteValue t w)⁻¹ := congrArg (finiteValue s w * ·) hinv
    _ = finiteValue s w / finiteValue t w := (div_eq_mul_inv _ _).symm

end Wikipedia.HopfProblem.HolomorphicMeromorphic.SphereEvaluation
