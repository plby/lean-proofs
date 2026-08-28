import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalGlobalBaseTwist

/-!
# The genuine simple pole of the sphere base-twist section

The infinity-chart coefficient of the actual Cartier section is `1 / w`
on the punctured coordinate chart. Its meromorphic order at infinity is
therefore exactly `-1`. The finite-chart coefficient is the unit `1`.
These statements use the fixed sphere's actual infinity parametrization
and the native bundle local trivialization.
-/

noncomputable section

open Set Topology Bundle
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist

open RiemannSphere

/-- The local Cartier fraction in the actual coordinate at infinity. -/
def infinityFraction (u : ℂ) : ℂ := cartier.localFraction true (infinityParametrization u)

theorem infinityFraction_eq_inv : infinityFraction = fun u : ℂ => u⁻¹ :=
  funext localFraction_infinityParametrization

theorem infinityFraction_meromorphicAt : MeromorphicAt infinityFraction 0 := by
  rw [infinityFraction_eq_inv]
  exact (show MeromorphicAt (id : ℂ → ℂ) 0 from analyticAt_id.meromorphicAt).inv

/-- The actual local fraction has a simple pole, not merely a declared
divisor multiplicity. -/
theorem infinityFraction_meromorphicOrderAt :
    meromorphicOrderAt infinityFraction 0 = (-1 : ℤ) := by
  rw [infinityFraction_eq_inv]
  change meromorphicOrderAt ((id : ℂ → ℂ)⁻¹) 0 = (-1 : ℤ)
  rw [meromorphicOrderAt_inv, meromorphicOrderAt_id]
  rfl

/-- The native infinity-chart coefficient of the actual Cartier section. -/
def actualInfinityCoefficient (u : ℂ) : ℂ :=
  data.localCoefficient cartier.rawSection true (infinityParametrization u)

theorem actualInfinityCoefficient_eq_fraction {u : ℂ} (hu : u ≠ 0) :
    actualInfinityCoefficient u = infinityFraction u :=
  (rawSection_infinity_coordinate u hu).trans (localFraction_infinityParametrization u).symm

theorem actualInfinityCoefficient_eventuallyEq :
    actualInfinityCoefficient =ᶠ[𝓝[≠] (0 : ℂ)] infinityFraction := by
  filter_upwards [self_mem_nhdsWithin] with u hu
  exact actualInfinityCoefficient_eq_fraction hu

theorem actualInfinityCoefficient_meromorphicAt :
    MeromorphicAt actualInfinityCoefficient 0 :=
  infinityFraction_meromorphicAt.congr actualInfinityCoefficient_eventuallyEq.symm

/-- The genuine native-bundle coefficient also has meromorphic order
`-1`; its arbitrary assigned value at the pole does not affect the order. -/
theorem actualInfinityCoefficient_meromorphicOrderAt :
    meromorphicOrderAt actualInfinityCoefficient 0 = (-1 : ℤ) :=
  (meromorphicOrderAt_congr actualInfinityCoefficient_eventuallyEq).trans
    infinityFraction_meromorphicOrderAt

@[simp] theorem infinity_denominator_at_infty :
    cartier.denominator true (∞ : RiemannSphere) = 0 := by
  rw [cartier_denominator_true, infinityCoordinate_infty]

@[simp] theorem infinity_denominator_parametrization (u : ℂ) :
    cartier.denominator true (infinityParametrization u) = u := by
  rw [cartier_denominator_true, infinityCoordinate_infinityParametrization]

/-- The denominator has a simple zero in the actual infinity coordinate. -/
theorem infinity_denominator_analyticOrderAt :
    analyticOrderAt (fun u : ℂ => cartier.denominator true (infinityParametrization u)) 0 = 1 := by
  simp only [infinity_denominator_parametrization]
  exact analyticOrderAt_id

/-- In the finite coordinate, the same meromorphic section is the unit
coefficient and has no zeros or poles anywhere on that chart. -/
theorem finiteFraction_meromorphicOrderAt (z : ℂ) :
    meromorphicOrderAt (fun u : ℂ => cartier.localFraction false (u : RiemannSphere)) z = 0 := by
  simp only [localFraction_false]
  simp [meromorphicOrderAt_const]

end Wikipedia.HopfProblem.CanonicalGlobal.BaseTwist
