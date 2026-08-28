import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereFace
import Wikipedia.HopfProblem.DegreeCollapseEmbeddedSphereRepresentative
import Wikipedia.NoExoticSixSphere.IntegralSphereHomotopyClass

/-!
# Full framed sphere representatives of the actual third homology

Every sphere map has a homotopic embedded immersive representative. The
constructed internal normal frame and full native tube turn it into a
framed closed face with that literal core. Third Hurewicz then represents
every integral H3 class by such a face in a two-connected target. The
fundamental class used here is the actual cubical sphere class throughout.
No unit intersection value or spanning framed disk is inferred.
-/

noncomputable section

open Set Function Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative

open NoExoticSixSphere NoExoticSixSphere.GLOrthonormalization
open EuclideanEmbedding SmoothCube Wikipedia.SmoothSixDPoincare
open SingularMayerVietoris

local instance : Fact (Module.finrank ℝ (Vector 4) = 3 + 1) :=
  ⟨finrank_euclideanSpace_fin⟩

variable {M : Type} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M] [T2Space M] [SimplyConnectedSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel)

include e a in
theorem exists_framed_representative (f : C(Sphere 3, M)) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      f.Homotopic (FramedSurgery.coreMap (E := Vector 4) B) := by
  let : Nonempty M := ⟨f (Stiefel.pole 3)⟩
  obtain ⟨r⟩ := e.nonempty_tubularRetraction a
  obtain ⟨g, hg, H, hgd, hge⟩ := TripleParameters.exists_embedded_sphere_representative e r f
  obtain ⟨B, hB⟩ := exists_framed_face_of_embedding e a r g hg hge.injective hgd
  exact ⟨B, hB.symm ▸ H⟩

include e a in
theorem exists_homology_framed_representative (m : M) [Subsingleton (π_ 2 M m)]
    (c : SingularHomology M 3) :
    ∃ B : SmoothClosedFace (𝓡 3) (𝓡 6) (Sphere 3) (Vector 3) M,
      integralSphereClass (FramedSurgery.coreMap (E := Vector 4) B) = c := by
  let f := (integralClassRepresentative m c).val
  obtain ⟨B, H⟩ := exists_framed_representative e a f
  refine ⟨B, ?_⟩
  exact (integralSphereClass_homotopic H).symm.trans (integralSphereClass_representative m c)

end Wikipedia.HopfProblem.DegreeCollapse.FramedRepresentative
