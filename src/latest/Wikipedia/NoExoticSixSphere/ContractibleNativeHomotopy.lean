import Wikipedia.HopfProblem.OrbitPairSphereNullhomotopyCriterion
import Mathlib.Topology.Homotopy.Contractible

/-!
# Native homotopy vanishes at every point of a contractible space

The actual contraction gives ordinary sphere nullhomotopies. The checked
disk-extension argument fixes their basepoints and returns genuine native
cube homotopies relative to the whole boundary. Degree zero uses actual
path components. No basepoint-change equivalence is assumed.
-/

noncomputable section

open scoped Topology
open Wikipedia.HopfProblem OrbitPair

namespace NoExoticSixSphere.ContractibleNativeHomotopy

variable {X : Type} [TopologicalSpace X] [ContractibleSpace X]

theorem subsingleton (n : ℕ) (x : X) : Subsingleton (π_ n X x) := by
  cases n with
  | zero =>
    let : Subsingleton (ZerothHomotopy X) :=
      (pathConnectedSpace_iff_zerothHomotopy.mp (inferInstanceAs (PathConnectedSpace X))).2
    exact HomotopyGroup.pi0EquivZerothHomotopy.injective.subsingleton
  | succ n =>
    apply SphereNullhomotopy.pi_subsingleton_of_sphere_nullhomotopies (Nat.zero_lt_succ n)
    intro f
    obtain ⟨c, hc⟩ := id_nullhomotopic X
    exact ⟨c, hc.comp (ContinuousMap.Homotopic.refl f)⟩

end NoExoticSixSphere.ContractibleNativeHomotopy
