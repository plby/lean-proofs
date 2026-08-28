import Wikipedia.NoExoticSixSphere.JamesSphereBottomHomotopy
import Wikipedia.NoExoticSixSphere.JamesSphereInclusionFiberConnectivity
import Wikipedia.NoExoticSixSphere.SphereGenLoopConnectivity

/-!
# Actual quotient-loop connectivity below the bottom cell

The proved bottom-sphere isomorphism gives the full quotient's native
vanishing below dimension `2 * n`, at every basepoint. Native currying
then gives the corresponding vanishing and simple connectivity of its
original compact-open loop space. Together with the actual inclusion
fiber, this starts the comparison below its first potentially nonzero group.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem.OrbitPair

namespace NoExoticSixSphere.JamesSphere.FirstStageQuotient

theorem simplyConnected_of_two_le (n : ℕ) (hn : 2 ≤ n) : SimplyConnectedSpace (Space n) := by
  have he : n = (n - 2) + 2 := by omega
  rw [he]
  exact simplyConnectedSpace (n - 2)

theorem pi_below_bottom (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d) (hdn : d < 2 * n)
    (p : Space n) : Subsingleton (π_ d (Space n) p) := by
  let : NeZero d := ⟨by omega⟩
  let := simplyConnected_of_two_le n hn
  let : Subsingleton (π_ d (Sphere (n + n)) (spherePole (n + n))) :=
    subsingleton_sphereHomotopyGroup_of_pos hd (by omega) _
  let : Subsingleton (π_ d (Space n) (basepoint n)) :=
    (bottomSpherePiEquiv n d hn (by omega)).symm.injective.subsingleton
  exact NativeHomotopyBasepointVanishing.subsingleton d hd (basepoint n) p

theorem loops_pi_below_bottom (n d : ℕ) (hn : 2 ≤ n) (hd : 0 < d)
    (hdn : d + 2 ≤ 2 * n) (p : Path (basepoint n) (basepoint n)) :
    Subsingleton (π_ d (Path (basepoint n) (basepoint n)) p) := by
  let := simplyConnected_of_two_le n hn
  let := pi_below_bottom n (d + 1) hn (by omega) (by omega) (basepoint n)
  exact NativeHomotopyBasepointVanishing.loops_subsingleton d hd (basepoint n) p

theorem loops_simplyConnected (n : ℕ) (hn : 2 ≤ n) :
    SimplyConnectedSpace (Path (basepoint n) (basepoint n)) := by
  let := simplyConnected_of_two_le n hn
  exact loopSpace_simplyConnected (basepoint n)
    (pi_below_bottom n 2 hn (by omega) (by omega) _)

end NoExoticSixSphere.JamesSphere.FirstStageQuotient

namespace NoExoticSixSphere.JamesSphere.FiberQuotient

theorem hom_bijective_below_bottom (n d : ℕ) [NeZero d] (hn : 2 ≤ n)
    (hdn : d + 2 ≤ 2 * n) : Function.Bijective (hom n d) := by
  let := fiber_pi_basepoint n d hn (Nat.pos_of_ne_zero (NeZero.ne d)) hdn
  let := FirstStageQuotient.pi_below_bottom n (d + 1) hn (by omega) (by omega)
    (FirstStageQuotient.basepoint n)
  exact ⟨fun _ _ _ ↦ Subsingleton.elim _ _, fun c ↦ ⟨1, Subsingleton.elim _ c⟩⟩

end NoExoticSixSphere.JamesSphere.FiberQuotient
