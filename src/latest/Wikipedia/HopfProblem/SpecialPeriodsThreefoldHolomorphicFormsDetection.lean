import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionCover
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldHolomorphicFormsDetectionDensity

/-!
# Global native forms are detected by the actual regular vector cover

The source is the original regular upper-half-plane locus times the two
complex period-vector coordinates.  Its image is the actual dense regular
locus of the glued threefold, and its actual tangent derivatives are
invertible.  Continuity of native alternating covectors therefore detects
global zero and equality, in every exterior degree.
-/

noncomputable section

open Set Topology
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover

open HolomorphicDifferentialForms (Form)

local notation "IF" => modelWithCornersSelf ℂ Model

attribute [local instance] chartedSpace specialRegularFamilyChartedSpace
  coverChartedSpace cover_isManifold space_isManifold

/-- Density holds for this literal map into the actual glued space. -/
theorem globalCover_denseRange : DenseRange globalCover := by
  change Dense (range globalCover)
  rw [range_globalCover]
  exact regularLocus_dense

/-- The genuine derivative pullback detects zero of global holomorphic
forms in every degree.  Density and tangent invertibility are proved for
the actual cover, and are not hypotheses of this theorem. -/
theorem globalCoverPullback_eq_zero_iff {p : ℕ}
    (θ : Form Model Threefold.Space p) :
    globalCoverPullback θ = 0 ↔ θ = 0 := by
  constructor
  · intro hθ
    exact HolomorphicDifferentialForms.eq_zero_of_dense regularLocus_dense θ
      ((globalCoverPullback_eq_zero_iff_regular θ).mp hθ)
  · rintro rfl
    exact map_zero (HolomorphicDifferentialForms.pullback
      globalCover globalCover_holomorphic)

/-- No global form is lost when passing to the original regular
period-vector covering coordinates. -/
theorem globalCoverPullback_injective (p : ℕ) :
    Function.Injective (globalCoverPullback (p := p)) := by
  intro θ η hθη
  apply sub_eq_zero.mp
  apply (globalCoverPullback_eq_zero_iff (θ - η)).mp
  change HolomorphicDifferentialForms.pullback globalCover globalCover_holomorphic
    (θ - η) = 0
  rw [map_sub]
  change globalCoverPullback θ - globalCoverPullback η = 0
  rw [hθη, sub_self]

/-- Equality of the actual pulled-back native forms is equivalent to
equality of the original global forms. -/
theorem globalCoverPullback_eq_iff {p : ℕ}
    (θ η : Form Model Threefold.Space p) :
    globalCoverPullback θ = globalCoverPullback η ↔ θ = η :=
  (globalCoverPullback_injective p).eq_iff

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.HolomorphicForms.RegularCover
