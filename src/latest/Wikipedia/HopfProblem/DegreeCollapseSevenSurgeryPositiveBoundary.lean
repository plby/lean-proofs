import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryZeroDiffeomorph
import Wikipedia.NoExoticSixSphere.ModelAtlasTransport
import Wikipedia.NoExoticSixSphere.SuperlevelInclusion

/-!
# The actual positive-half boundary carries the ambient regular-fiber atlas

The boundary is determined by the previously constructed half-space atlas.
Its literal identification with the regular zero fiber supplies its induced
six-dimensional charts. The inclusion into the original half-space atlas is
proved smooth. No original manifold atlas is replaced by this construction.
-/

noncomputable section

open Function Set
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

abbrev PositiveBoundary := letI := targetChartedSpace A hR;
  letI := positiveHalfChartedSpace A hR T;
  {p : PositiveHalf A hR T // (ProductHalfSpace.model (Vector 6)).IsBoundaryPoint p}

def positiveBoundaryHomeomorph : PositiveBoundary A hR T ≃ₜ ResultZero A hR T := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  exact
    { toFun := fun p ↦ ⟨p.val.val, (positiveHalf_boundary_iff A hR T p.val).mp p.property⟩
      invFun := fun p ↦ ⟨⟨p.val, p.property.symm.le⟩,
        (positiveHalf_boundary_iff A hR T _).mpr p.property⟩
      left_inv := fun p ↦ Subtype.ext (Subtype.ext rfl)
      right_inv := fun p ↦ Subtype.ext rfl
      continuous_toFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _
      continuous_invFun := (continuous_subtype_val.subtype_mk _).subtype_mk _ }

@[instance_reducible]
def positiveBoundaryAtlas : letI := targetChartedSpace A hR;
    ChartedSpace (Vector 6) (PositiveBoundary A hR T) := by
  let := targetChartedSpace A hR
  let := resultZeroAtlas A hR T
  exact ModelAtlasTransport.atlas (positiveBoundaryHomeomorph A hR T)

theorem positiveBoundary_isManifold : letI := targetChartedSpace A hR;
    letI := positiveBoundaryAtlas A hR T;
    IsManifold (𝓡 6) ∞ (PositiveBoundary A hR T) := by
  let := targetChartedSpace A hR
  let := resultZeroAtlas A hR T
  let := resultZero_isManifold A hR T
  exact ModelAtlasTransport.isManifold (positiveBoundaryHomeomorph A hR T) (𝓡 6)

def positiveBoundaryDiffeomorph : letI := targetChartedSpace A hR;
    letI := positiveBoundaryAtlas A hR T; letI := resultZeroAtlas A hR T;
    PositiveBoundary A hR T ≃ₘ⟮𝓡 6, 𝓡 6⟯ ResultZero A hR T := by
  let := targetChartedSpace A hR
  let := resultZeroAtlas A hR T
  exact ModelAtlasTransport.diffeomorph (positiveBoundaryHomeomorph A hR T) (𝓡 6)

theorem positiveBoundaryDiffeomorph_point (p : PositiveBoundary A hR T) :
    letI := targetChartedSpace A hR;
    letI := positiveBoundaryAtlas A hR T; letI := resultZeroAtlas A hR T;
    (positiveBoundaryDiffeomorph A hR T p).val = p.val.val := rfl

theorem contMDiff_positiveBoundaryInclusion : letI := targetChartedSpace A hR;
    letI := positiveHalfChartedSpace A hR T; letI := positiveBoundaryAtlas A hR T;
    ContMDiff (𝓡 6) (ProductHalfSpace.model (Vector 6)) ∞
      (Subtype.val : PositiveBoundary A hR T → PositiveHalf A hR T) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := positiveHalfChartedSpace A hR T
  let := positiveBoundaryAtlas A hR T
  let := resultZeroAtlas A hR T
  apply ((positiveHalfAtlas A hR T).contMDiff_iff_ambient Subtype.val).mpr
  have hz : ContMDiff (𝓡 6) (𝓡 7) ∞ (Subtype.val : ResultZero A hR T → Target A hR) :=
    regularFiber_contMDiff_subtype_val (resultTimeMap A hR T)
      (contMDiff_timeFunction A hR T) 0 (regular_timeFunction_zero A hR T) 6 (by simp)
  exact hz.comp (positiveBoundaryDiffeomorph A hR T).contMDiff

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
