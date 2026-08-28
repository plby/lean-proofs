import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfFraming

/-!
# The native boundary includes immersively into the actual surgery half

Its inclusion into the closed target factors through the genuine regular
zero fiber and the checked boundary diffeomorphism. Injectivity of that
derivative forces injectivity of the boundary-to-half derivative as well.
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

def boundaryTargetInclusion (p : PositiveBoundary A hR T) : Target A hR := p.val.val

theorem contMDiff_boundaryTargetInclusion : letI := targetChartedSpace A hR;
    letI := positiveBoundaryAtlas A hR T;
    ContMDiff (𝓡 6) (𝓡 7) ∞ (boundaryTargetInclusion A hR T) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  let := positiveBoundaryAtlas A hR T
  exact (contMDiff_positiveHalfInclusion A hR T).comp (contMDiff_positiveBoundaryInclusion A hR T)

theorem injective_mfderiv_boundaryTargetInclusion (p : PositiveBoundary A hR T) :
    letI := targetChartedSpace A hR; letI := positiveBoundaryAtlas A hR T;
    Injective (mfderiv (𝓡 6) (𝓡 7) (boundaryTargetInclusion A hR T) p) := by
  let := targetChartedSpace A hR
  let := target_isManifold A hR
  let := positiveBoundaryAtlas A hR T
  let := resultZeroAtlas A hR T
  let D := positiveBoundaryDiffeomorph A hR T
  have hz : ContMDiff (𝓡 6) (𝓡 7) ∞ (Subtype.val : ResultZero A hR T → Target A hR) :=
    regularFiber_contMDiff_subtype_val (resultTimeMap A hR T)
      (contMDiff_timeFunction A hR T) 0 (regular_timeFunction_zero A hR T) 6 (by simp)
  have hi : Injective (mfderiv (𝓡 6) (𝓡 7)
      (Subtype.val : ResultZero A hR T → Target A hR) (D p)) :=
    regularFiber_injective_mfderiv_subtype_val (resultTimeMap A hR T)
      (contMDiff_timeFunction A hR T) 0 (regular_timeFunction_zero A hR T) 6 (by simp) (D p)
  change Injective (mfderiv (𝓡 6) (𝓡 7)
    ((Subtype.val : ResultZero A hR T → Target A hR) ∘ D) p)
  rw [mfderiv_comp p (hz.mdifferentiableAt (by simp)) (D.contMDiff.mdifferentiableAt (by simp))]
  exact hi.comp ((D.isLocalDiffeomorph p).mfderivToContinuousLinearEquiv (by simp)).injective

theorem injective_mfderiv_positiveBoundaryInclusion (p : PositiveBoundary A hR T) :
    letI := targetChartedSpace A hR; letI := positiveHalfChartedSpace A hR T;
    letI := positiveBoundaryAtlas A hR T;
    Injective (mfderiv (𝓡 6) (ProductHalfSpace.model (Vector 6))
      (Subtype.val : PositiveBoundary A hR T → PositiveHalf A hR T) p) := by
  let := targetChartedSpace A hR
  let := positiveHalfChartedSpace A hR T
  let := positiveBoundaryAtlas A hR T
  have hc := mfderiv_comp p ((contMDiff_positiveHalfInclusion A hR T).mdifferentiableAt (by simp))
    ((contMDiff_positiveBoundaryInclusion A hR T).mdifferentiableAt (by simp))
  intro u v he
  apply injective_mfderiv_boundaryTargetInclusion A hR T p
  change (mfderiv (𝓡 6) (𝓡 7)
    ((Subtype.val : PositiveHalf A hR T → Target A hR) ∘
      (Subtype.val : PositiveBoundary A hR T → PositiveHalf A hR T)) p) u =
    (mfderiv (𝓡 6) (𝓡 7)
    ((Subtype.val : PositiveHalf A hR T → Target A hR) ∘
      (Subtype.val : PositiveBoundary A hR T → PositiveHalf A hR T)) p) v
  rw [hc]
  exact congrArg (mfderiv (ProductHalfSpace.model (Vector 6)) (𝓡 7)
    (Subtype.val : PositiveHalf A hR T → Target A hR) p.val) he

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
