import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageHomologyRange
import Wikipedia.NoExoticSixSphere.JamesSphereSimplyConnected
import Wikipedia.NoExoticSixSphere.JamesSphereSecondStageNativeHopf
import Wikipedia.NoExoticSixSphere.HomologyRangeConnectivity

/-!
# The original second-stage inclusion on native homotopy groups

Both actual James spaces are simply connected. The proved integral
homology comparison, including the upper edge, therefore supplies the
native homotopy comparison through degree `3n - 2`, at every original
second-stage basepoint.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere.SecondStage

theorem wordInclusion_pi_bijective (n : ℕ) (hn : 2 ≤ n)
    (d : ℕ) (hd : 0 < d) (hdn : d ≤ 3 * n - 2) (x : Space n) :
    Function.Bijective (HigherHomotopy.map (N := Fin d) (wordInclusion n) (y := x) rfl) := by
  have he : n = (n - 2) + 2 := by omega
  let : SimplyConnectedSpace (Space n) := by
    change SimplyConnectedSpace (James.stage (spherePole n) 2)
    rw [he]
    exact JamesSphere.stage_simplyConnected (n - 2) 2
  let : SimplyConnectedSpace (WordHomology.Words n) := by
    change SimplyConnectedSpace (James.Space (Sphere n) (spherePole n))
    rw [he]
    exact JamesSphere.simplyConnectedSpace (n - 2)
  apply HomologyRangeConnectivity.map_pi_bijective (TopCat.ofHom (wordInclusion n))
    (3 * n - 2) (by omega) ?_ d hd hdn x
  intro k hk hkD
  exact SecondStageHomologyRange.fullMap_bijective n hn k hk (by omega)

end NoExoticSixSphere.JamesSphere.SecondStage
