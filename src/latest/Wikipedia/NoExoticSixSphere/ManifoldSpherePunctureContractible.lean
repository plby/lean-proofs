import Wikipedia.NoExoticSixSphere.ManifoldSpherePunctureCover
import Wikipedia.NoExoticSixSphere.SphereCylinderCapsContractible
import Wikipedia.NoExoticSixSphere.ManifoldOpenBallContractible

/-!
# Contractible pieces of the actual sphere-puncture covers

Every neighborhood piece is contractible in its original topology. Each
one-point complement is homeomorphic to the ordinary Euclidean four-space by
the stereographic chart at that actual point.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereFamily

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]

def singlePunctureCoordinates (g : ℝ → Sphere 3 → M) (i : ParityBallSystem.BoundaryIndex g) :
    singlePunctureRegularSet g i ≃ₜ Vector 4 := by
  let : Fact (Module.finrank ℝ (Vector 5) = 4 + 1) := ⟨finrank_euclideanSpace_fin⟩
  let e := stereographic' 4 (spherePuncture g i)
  have hs : e.source = singlePunctureRegularSet g i := stereographic'_source _
  have ht : e.target = univ := stereographic'_target _
  exact (Homeomorph.setCongr hs.symm).trans (e.toHomeomorphSourceTarget.trans
    ((Homeomorph.setCongr ht).trans (Homeomorph.Set.univ (Vector 4))))

theorem singlePunctureRegularSet_contractible (g : ℝ → Sphere 3 → M)
    (i : ParityBallSystem.BoundaryIndex g) : ContractibleSpace (singlePunctureRegularSet g i) :=
  (singlePunctureCoordinates g i).contractibleSpace

namespace ParityBallSystem

variable {g : ℝ → Sphere 3 → M} (P : ParityBallSystem g)

theorem coverPiece_contractible (i : BoundaryIndex g) : ContractibleSpace (P.coverPiece i) := by
  rcases i with b | q
  · exact SphereCylinder.capRegion_contractible 3 b
  · let := (P.ball q).openRegion_contractible
    exact ((SphereCylinder.isOpenEmbedding_point 3).isEmbedding.homeomorphImage
      (P.ball q).openRegion).symm.contractibleSpace

end ParityBallSystem
end NoExoticSixSphere.SphereFamily
