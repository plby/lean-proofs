import Wikipedia.NoExoticSixSphere.FourDiskBoundaryParity
import Wikipedia.NoExoticSixSphere.ManifoldFourDiskLinkParity

/-!
# The original normal-plus-derivative boundary operator extends

For an even native singular set, the actual constructed punctured-disk
frame has zero outer obstruction. Its exact boundary operator therefore
extends over a four-disk through injective operators. The extension is not
claimed to be the derivative of the original map at interior singularities.
-/

noncomputable section

open Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization Stiefel DiskBoundary
open Wikipedia.HopfProblem.DegreeCollapse

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  (e : EuclideanEmbedding 7 M)
  (a : SmoothRangeFrame (𝓡 7) e.normalProjection e.NormalModel)
  (g : Vector 4 → M)
  (hg : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x)
  (P : GenericFourDisk.ParityBallSystem g)
  (heven : Even (DiskDoublePoints.singularSet g).ncard)

include heven in
theorem fourDiskOuterObstruction_zero : e.fourDiskOuterObstruction a g hg P = 0 :=
  P.outer_frame_obstruction_zero_of_even_links ((e.ambientDimension - 7) + 2)
    (e.puncturedFourDiskGlobalFrameMap a g hg P) heven
    (e.fourDiskLinkObstruction_one a g hg P)

include heven in
theorem fourDiskOuterFrame_extends :
    Extends ((e.puncturedFourDiskFrameMap a g hg P).comp P.outerBoundary) := by
  have h := (sphereThirdObstruction_zero_iff_extension _ _).mp
    (e.fourDiskOuterObstruction_zero a g hg P heven)
  exact (e.puncturedFourDiskGlobalFrameMap_extends_iff a g hg P P.outerBoundary).mp h

include heven in
theorem fourDiskOuterOperator_extends :
    Extends ((e.puncturedFourDiskOperatorMap a g hg P).comp P.outerBoundary) :=
  (extends_normalize_iff _).mp (e.fourDiskOuterFrame_extends a g hg P heven)

include hg P heven in
theorem exists_fourDiskOperator_extension :
    ∃ F : C(DiskCylinder.Disk (E := Vector 4),
        Monomorphism.Space e.ambientDimension ((e.ambientDimension - 7) + 4)),
      ∀ s : Sphere 3, (F (DiskCylinder.boundaryToDisk s)).val =
        e.normalFourDiskOperator a g s.val := by
  obtain ⟨F, hF⟩ := e.fourDiskOuterOperator_extends a g hg P heven
  exact ⟨F, fun s ↦ congrArg Subtype.val (hF s)⟩

end NoExoticSixSphere.EuclideanEmbedding
