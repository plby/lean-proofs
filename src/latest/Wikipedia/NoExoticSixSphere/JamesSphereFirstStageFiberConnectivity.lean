import Wikipedia.NoExoticSixSphere.JamesSphereFirstStageHomologyRange
import Wikipedia.NoExoticSixSphere.HomologyRangeConnectivity
import Wikipedia.NoExoticSixSphere.JamesSphereQuotientConnectivity
import Wikipedia.NoExoticSixSphere.PointInclusionFiber

/-!
# Connectivity at every basepoint of the actual first-stage pair

The checked homology range gives connectivity for all fibers of the
literal subtype inclusion, not only the fiber over the sphere pole.
The corresponding singleton fibers of the quotient are identified with
their genuine loop spaces. Both statements retain every fiber basepoint.
-/

noncomputable section

open scoped Topology

namespace NoExoticSixSphere.JamesSphere

namespace FirstStage

theorem fiber_pi (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) (hdn : d + 2 ≤ 2 * n)
    (a : James.stage (spherePole n) 1)
    (p : RelativeFiberHomology.Fiber (James.stage (spherePole n) 1) a) :
    Subsingleton (π_ d (RelativeFiberHomology.Fiber (James.stage (spherePole n) 1) a) p) := by
  let : SimplyConnectedSpace (James.Space (Sphere n) (spherePole n)) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    exact JamesSphere.simplyConnectedSpace (n - 2)
  let : SimplyConnectedSpace (James.stage (spherePole n) 1) := by
    have he : n = (n - 2) + 2 := by omega
    rw [he]
    exact JamesSphere.stage_simplyConnected (n - 2) 1
  exact HomologyRangeConnectivity.fiber_pi (James.stage (spherePole n) 1)
    (2 * n - 2) (by omega)
    (fun k hk hkn ↦ inclusion_homology_bijective n k hn hk (by omega))
    d hd (by omega) a p

end FirstStage

namespace FirstStageQuotient

theorem point_fiber_pi (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) (hdn : d + 2 ≤ 2 * n)
    (a : ({basepoint n} : Set (Space n)))
    (p : RelativeFiberHomology.Fiber ({basepoint n} : Set (Space n)) a) :
    Subsingleton (π_ d (RelativeFiberHomology.Fiber ({basepoint n} : Set (Space n)) a) p) := by
  let := simplyConnected_of_two_le n hn
  let := pi_below_bottom n (d + 1) hn (by omega) (by omega) a.val
  exact PointInclusionFiber.pi_subsingleton (basepoint n) a d hd p

end FirstStageQuotient

end NoExoticSixSphere.JamesSphere
