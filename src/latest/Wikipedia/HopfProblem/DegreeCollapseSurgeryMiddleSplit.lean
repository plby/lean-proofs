import Wikipedia.HopfProblem.DegreeCollapseSurgeryDualConnectivity
import Wikipedia.HopfProblem.DegreeCollapseIntegerSplit
import Wikipedia.NoExoticSixSphere.IntegralSplitting

/-!
# The exact integral middle-homology splitting after belt vanishing

Vanishing of the actual belt class is equivalent to surjectivity of the
genuine reverse connecting map. Mark its sphere target by the previously
proved integral top class. The exact sequence then splits, retaining
the actual native end inclusion as the first summand. Composing with the
original-end quotient computes that quotient as new H3 plus one integer.
No primitivity of the original attaching class, rank drop, or existence
of a geometric dual is inferred from this splitting alone.
-/

noncomputable section

open Set Function Metric Topology ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.TraceBody

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization EuclideanEmbedding
open EuclideanEmbedding.FramedAttachingProduct
open EuclideanEmbedding.FramedAttachingProduct.RoundedTrace
open SingularMayerVietoris PeriodTorusHigherHomology SphereHomology

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M] [CompactSpace M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] {e : EuclideanEmbedding 6 M}
  {a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel}
  (f : C(Sphere 3, M)) (A : FramedAttachingProduct e a f) (hR : A.radius = 2)

theorem nativeBelt_homology_zero_iff_class_zero :
    singularHomologyMap (nativeBeltMap A hR) 2 = 0 ↔ nativeBeltClass f A hR = 0 := by
  constructor
  · intro h
    change singularHomologyMap (nativeBeltMap A hR) 2 (unitSphereTopClass 1) = 0
    rw [h, LinearMap.zero_apply]
  · intro h
    apply LinearMap.ext
    intro x
    obtain ⟨k, rfl⟩ := unitSphereTopClass_generates 1 x
    rw [map_zsmul]
    change k • nativeBeltClass f A hR = 0
    rw [h, zsmul_zero]

theorem nativeConnecting_surjective_iff_belt_zero :
    Surjective (nativeConnecting A hR 2) ↔ nativeBeltClass f A hR = 0 := by
  constructor
  · intro h
    have hx : unitSphereTopClass 1 ∈ LinearMap.range (nativeConnecting A hR 2) := h _
    rw [native_end_exact_at_belt A hR 2 (by decide)] at hx
    exact hx
  · intro h
    have hz := (nativeBelt_homology_zero_iff_class_zero f A hR).mpr h
    apply LinearMap.range_eq_top.mp
    rw [native_end_exact_at_belt A hR 2 (by decide), hz, LinearMap.ker_zero]

def nativeMiddleCoordinate : SingularHomology (ambientSet A) 3 →ₗ[ℤ] ℤ :=
  (unitSphereHomologyTopEquiv 1).toLinearMap.comp (nativeConnecting A hR 2)

theorem nativeMiddleCoordinate_exact :
    LinearMap.range (singularHomologyMap (nativeTargetInclusion A hR) 3) =
      LinearMap.ker (nativeMiddleCoordinate f A hR) := by
  rw [native_end_exact_at_trace A hR 2]
  ext x
  change nativeConnecting A hR 2 x = 0 ↔
    unitSphereHomologyTopEquiv 1 (nativeConnecting A hR 2 x) = 0
  constructor
  · intro h
    rw [h, map_zero]
  · intro h
    exact (unitSphereHomologyTopEquiv 1).injective (h.trans (map_zero _).symm)

theorem nativeMiddleCoordinate_surjective (hz : nativeBeltClass f A hR = 0) :
    Surjective (nativeMiddleCoordinate f A hR) :=
  (unitSphereHomologyTopEquiv 1).surjective.comp
    ((nativeConnecting_surjective_iff_belt_zero f A hR).mpr hz)

def nativeMiddleHomologySplit (hz : nativeBeltClass f A hR = 0) :
    SingularHomology (ambientSet A) 3 ≃ₗ[ℤ]
      SingularHomology (UnitSurgery.Target A hR) 3 × ℤ :=
  IntegralSplitting.splitEquiv (singularHomologyMap (nativeTargetInclusion A hR) 3)
    (nativeMiddleCoordinate f A hR) (nativeTarget_homology_injective_three A hR)
    (nativeMiddleCoordinate_exact f A hR) (nativeMiddleCoordinate_surjective f A hR hz)

theorem nativeMiddleHomologySplit_symm_inl (hz : nativeBeltClass f A hR = 0)
    (x : SingularHomology (UnitSurgery.Target A hR) 3) :
    (nativeMiddleHomologySplit f A hR hz).symm (x, 0) =
      singularHomologyMap (nativeTargetInclusion A hR) 3 x :=
  IntegralSplitting.splitEquiv_symm_inl _ _ _ _ _ x

def reducedMiddleHomologyEquiv (hz : nativeBeltClass f A hR = 0) :
    (SingularHomology M 3 ⧸ Submodule.span ℤ {TraceCoreAttachment.originalSphereClass f}) ≃ₗ[ℤ]
      SingularHomology (UnitSurgery.Target A hR) 3 × ℤ :=
  (TraceCoreAttachment.traceMiddleHomologyEquiv f A hR).trans
    (nativeMiddleHomologySplit f A hR hz)

theorem reducedMiddleHomologyEquiv_mk (hz : nativeBeltClass f A hR = 0)
    (x : SingularHomology M 3) :
    reducedMiddleHomologyEquiv f A hR hz (Submodule.Quotient.mk x) =
      nativeMiddleHomologySplit f A hR hz (singularHomologyMap (topMap A) 3 x) := by
  change nativeMiddleHomologySplit f A hR hz
    (TraceCoreAttachment.traceMiddleHomologyEquiv f A hR (Submodule.Quotient.mk x)) = _
  rw [TraceCoreAttachment.traceMiddleHomologyEquiv_mk]

end Wikipedia.HopfProblem.DegreeCollapse.TraceBody
