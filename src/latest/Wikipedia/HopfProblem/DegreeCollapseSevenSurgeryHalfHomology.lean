import Wikipedia.HopfProblem.DegreeCollapseSevenSurgeryHalfClosedPresentation
import Wikipedia.HopfProblem.DegreeCollapseSurgeryPairHomology
import Wikipedia.HopfProblem.SphereHomologyVanishing

/-!
# The actual relative seven-dimensional surgery homology sequences

Apply both constructed endpoint sequences to the original compact
nonnegative half and the native positive surgery half. Both attaching
spheres are three-spheres. The common body here is the explicit compact
whole-handle quotient; no identification with a smooth rounded trace is
needed or asserted for this homology calculation.
-/

noncomputable section

open Set Function Topology Metric ContinuousMap
open scoped Manifold ContDiff

namespace Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery

open NoExoticSixSphere GLOrthonormalization
open Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 7) M] [CompactSpace M]
  [IsManifold (𝓡 7) ∞ M] [T2Space M] {e : EuclideanEmbedding 7 M}
  {a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel} {f : Sphere 3 → M}
  (A : FramedAttachingProduct e a f) (hR : A.radius = 2) (T : TimeData A)

instance compactSpace_oldPositiveHalf : CompactSpace (OldPositiveHalf A T) :=
  isCompact_iff_compactSpace.mp (isClosed_le continuous_const T.smooth.continuous).isCompact

local instance : CompactSpace (PositiveHalf A hR T) := compactSpace_positiveHalf A hR T

abbrev HalfBody := SurgeryPairBody.Space (halfBoundaryPair A hR T)

def oldHalfInclusion : C(OldPositiveHalf A T, HalfBody A hR T) :=
  SurgeryPairBody.oldMap (halfBoundaryPair A hR T)

def newHalfInclusion : C(PositiveHalf A hR T, HalfBody A hR T) :=
  SurgeryPairBody.newMap (halfBoundaryPair A hR T)

def halfAttachingSphere : C(Sphere 3, OldPositiveHalf A T) :=
  (halfBoundaryPair A hR T).attachingSphere

def halfBeltSphere : C(Sphere 3, PositiveHalf A hR T) :=
  (halfBoundaryPair A hR T).beltSphere

theorem halfAttachingSphere_val (s : Sphere 3) : (halfAttachingSphere A hR T s).val = f s :=
  halfBoundaryPair_attachingSphere A hR T s

theorem halfBeltSphere_val (s : Sphere 3) :
    (halfBeltSphere A hR T s).val =
      FramedSurgery.closedNewMap (E := Vector 4) (face A hR) 3 (⟨0, by simp⟩, s) :=
  halfBoundaryPair_beltSphere A hR T s

def oldHalfConnecting (k : ℕ) :
    SingularHomology (HalfBody A hR T) (k + 1) →ₗ[ℤ] SingularHomology (Sphere 3) k :=
  SurgeryPairBody.oldConnecting (halfBoundaryPair A hR T) k

def newHalfConnecting (k : ℕ) :
    SingularHomology (HalfBody A hR T) (k + 1) →ₗ[ℤ] SingularHomology (Sphere 3) k :=
  SurgeryPairBody.newConnecting (halfBoundaryPair A hR T) k

theorem half_exact_at_old (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (singularHomologyMap (halfAttachingSphere A hR T) k) =
      LinearMap.ker (singularHomologyMap (oldHalfInclusion A hR T) k) :=
  SurgeryPairBody.exact_at_old (halfBoundaryPair A hR T) k hk

theorem half_exact_at_body_old (k : ℕ) :
    LinearMap.range (singularHomologyMap (oldHalfInclusion A hR T) (k + 1)) =
      LinearMap.ker (oldHalfConnecting A hR T k) :=
  SurgeryPairBody.exact_at_body_old (halfBoundaryPair A hR T) k

theorem half_exact_at_attaching (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (oldHalfConnecting A hR T k) =
      LinearMap.ker (singularHomologyMap (halfAttachingSphere A hR T) k) :=
  SurgeryPairBody.exact_at_attaching (halfBoundaryPair A hR T) k hk

theorem half_exact_at_new (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (singularHomologyMap (halfBeltSphere A hR T) k) =
      LinearMap.ker (singularHomologyMap (newHalfInclusion A hR T) k) :=
  SurgeryPairBody.exact_at_new (halfBoundaryPair A hR T) k hk

theorem half_exact_at_body_new (k : ℕ) :
    LinearMap.range (singularHomologyMap (newHalfInclusion A hR T) (k + 1)) =
      LinearMap.ker (newHalfConnecting A hR T k) :=
  SurgeryPairBody.exact_at_body_new (halfBoundaryPair A hR T) k

theorem half_exact_at_belt (k : ℕ) (hk : k ≠ 0) :
    LinearMap.range (newHalfConnecting A hR T k) =
      LinearMap.ker (singularHomologyMap (halfBeltSphere A hR T) k) :=
  SurgeryPairBody.exact_at_belt (halfBoundaryPair A hR T) k hk

theorem oldHalf_surjective_three :
    Surjective (singularHomologyMap (oldHalfInclusion A hR T) 3) := by
  let : Subsingleton (SingularHomology (Sphere 3) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 2 2 (by decide) (by decide)
  exact (SurgeryPairBody.oldHandleData (halfBoundaryPair A hR T)).old_surjective 2

theorem newHalf_surjective_three :
    Surjective (singularHomologyMap (newHalfInclusion A hR T) 3) := by
  let : Subsingleton (SingularHomology (Sphere 3) 2) :=
    SphereHomology.unitSphere_homology_subsingleton 2 2 (by decide) (by decide)
  exact (SurgeryPairBody.newHandleData (halfBoundaryPair A hR T)).old_surjective 2

theorem oldHalf_injective_four :
    Injective (singularHomologyMap (oldHalfInclusion A hR T) 4) := by
  let : Subsingleton (SingularHomology (Sphere 3) 4) :=
    SphereHomology.unitSphere_homology_subsingleton 2 4 (by decide) (by decide)
  exact (SurgeryPairBody.oldHandleData (halfBoundaryPair A hR T)).old_injective 4 (by decide)

theorem newHalf_injective_four :
    Injective (singularHomologyMap (newHalfInclusion A hR T) 4) := by
  let : Subsingleton (SingularHomology (Sphere 3) 4) :=
    SphereHomology.unitSphere_homology_subsingleton 2 4 (by decide) (by decide)
  exact (SurgeryPairBody.newHandleData (halfBoundaryPair A hR T)).old_injective 4 (by decide)

end Wikipedia.HopfProblem.DegreeCollapse.SevenSurgery.FramedAttachingProduct.UnitSurgery
