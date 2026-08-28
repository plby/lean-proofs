import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsNormalForms
import Wikipedia.HopfProblem.HolomorphicDifferentialFormsCoordinateEvaluation

/-!
# Full native-covector evaluations in the normal forms

The coefficient normal forms determine the entire genuine derivative
pullback. These identities hold for arbitrary original tangent vectors,
in the base-first ordering used in the source.
-/

noncomputable section

open scoped ContDiff Manifold Matrix

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

attribute [local instance] chartedSpace coverChartedSpace cover_isManifold space_isManifold

theorem oneForm_evaluation (θ : Form Model Threefold.Space 1)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) (u : Model) :
    globalCoverPullback θ (z, ζ) ![u] =
      baseOne θ z * u.1 + dotProduct (fibreOne θ z) u.2 := by
  have h := HolomorphicDifferentialForms.Coordinates.one_evaluation
    (nativeCoefficients θ (z, ζ)) u
  rw [nativeCoefficients_apply] at h
  change globalCoverPullback θ (z, ζ) ![u] =
    oneBase θ (z, ζ) * u.1 + dotProduct (oneFibre θ (z, ζ)) u.2 at h
  rw [oneBase_eq_baseOne, oneFibre_eq_fibreOne] at h
  exact h

theorem twoForm_evaluation (θ : Form Model Threefold.Space 2)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) (u v : Model) :
    globalCoverPullback θ (z, ζ) ![u, v] =
      u.1 * dotProduct (mixedTwo θ z) v.2 - v.1 * dotProduct (mixedTwo θ z) u.2 := by
  have h := HolomorphicDifferentialForms.Coordinates.two_evaluation
    (nativeCoefficients θ (z, ζ)) u v
  rw [nativeCoefficients_apply] at h
  change globalCoverPullback θ (z, ζ) ![u, v] =
    twoVertical θ (z, ζ) * (u.2 0 * v.2 1 - u.2 1 * v.2 0) +
      u.1 * dotProduct (twoMixed θ (z, ζ)) v.2 -
      v.1 * dotProduct (twoMixed θ (z, ζ)) u.2 at h
  rw [twoVertical_eq_zero, zero_mul, zero_add, twoMixed_eq_mixedTwo] at h
  exact h

theorem threeForm_evaluation (θ : Form Model Threefold.Space 3)
    (z : TriangleRegularPoint) (ζ : ComplexPlane₂) (u v w : Model) :
    globalCoverPullback θ (z, ζ) ![u, v, w] =
      baseTop θ z * PeriodFamilyHolomorphicForms.coordinateVolume u v w := by
  have h := HolomorphicDifferentialForms.Coordinates.top_evaluation
    (nativeCoefficients θ (z, ζ)) u v w
  rw [nativeCoefficients_apply] at h
  change globalCoverPullback θ (z, ζ) ![u, v, w] =
    top θ (z, ζ) * PeriodFamilyHolomorphicForms.coordinateVolume u v w at h
  rw [top_eq_baseTop] at h
  exact h

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
