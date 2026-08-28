import Wikipedia.NoExoticSixSphere.HomologyRangeConnectivity
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientSimplyConnected
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientNativeHopf

/-!
# The bottom-sphere native comparison reduced to its actual homology maps

Simple connectivity of both actual spaces is discharged. Finite-range
homology comparison therefore gives bijectivity of the original based
bottom-sphere native map. The homology hypothesis is explicit and is not
proved in this file; in particular this is not yet the metastable theorem.
-/

noncomputable section

open CategoryTheory
open scoped Topology
open Wikipedia.HopfProblem SingularMayerVietoris

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem bottomSphere_pi_bijective_of_homology (n D : ℕ) (hD : 0 < D)
    (hH : ∀ k, 2 ≤ k → k ≤ D + 1 →
      Function.Bijective (singularHomologyMap (bottomSphere (n + 2)) k))
    (d : ℕ) (hd : 0 < d) (hdD : d ≤ D) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (bottomSphere (n + 2))
      (bottomSphere_pole (n + 2))) := by
  let : SimplyConnectedSpace (Space (n + 2)) := simplyConnectedSpace n
  let : SimplyConnectedSpace (Sphere (n + 2 + (n + 2))) := by
    have he : n + 2 + (n + 2) = (n + n + 2) + 2 := by omega
    rw [he]
    infer_instance
  have hb := HomologyRangeConnectivity.map_pi_bijective
    (TopCat.ofHom (bottomSphere (n + 2))) D hD hH d hd hdD
    (spherePole (n + 2 + (n + 2)))
  exact MappingCylinderNativeHomotopy.map_bijective_of_eq_target d (bottomSphere (n + 2))
    (bottomSphere_pole (n + 2)) hb

end NoExoticSixSphere.JamesSphere.FirstStageQuotient
