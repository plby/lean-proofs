import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicStabilization
import Wikipedia.NoExoticSixSphere.SphereHomotopyGroups

/-!
# The full stable range for the native homotopy groups of quaternionic unitary groups

The repository's general lower-sphere contraction theorem supplies vanishing
in every needed dimension. Thus the actual matrix inclusion induces an
isomorphism for each positive `k ≤ 4n+1`, including degree seven from rank two.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

theorem unitColumn_homotopy_subsingleton (n k : ℕ) (hk : k < 4 * n + 3)
    (x : UnitColumn (Fin (n + 1))) :
    Subsingleton (π_ k (UnitColumn (Fin (n + 1))) x) :=
  NoExoticSixSphere.subsingleton_homotopyGroup_of_homeomorph_sphere hk
    (columnSphereHomeomorph n) x

/-- The standard inclusion is a native group isomorphism throughout the stable range. -/
def stabilizationInRange (n k : ℕ) [NeZero k] (hk : k ≤ 4 * n + 1) :
    π_ k (SpGroup (Fin n)) 1 ≃* π_ k (SpGroup (Fin (n + 1))) 1 := by
  let := unitColumn_homotopy_subsingleton n k (by omega) (axisColumn 0)
  let := unitColumn_homotopy_subsingleton n (k + 1) (by omega) (axisColumn 0)
  exact stabilizationMulEquiv n k

theorem stabilizationInRange_apply (n k : ℕ) [NeZero k] (hk : k ≤ 4 * n + 1)
    (a : π_ k (SpGroup (Fin n)) 1) :
    stabilizationInRange n k hk a = stabilizationMap n k a := by
  let := unitColumn_homotopy_subsingleton n k (by omega) (axisColumn 0)
  let := unitColumn_homotopy_subsingleton n (k + 1) (by omega) (axisColumn 0)
  exact stabilizationMulEquiv_apply n k a

/-- In particular, the degree-seven groups are already stable at quaternionic rank two. -/
def stabilizationPiSevenMulEquiv (n : ℕ) (hn : 2 ≤ n) :
    π_ 7 (SpGroup (Fin n)) 1 ≃* π_ 7 (SpGroup (Fin (n + 1))) 1 :=
  stabilizationInRange n 7 (by omega)

theorem stabilizationPiSevenMulEquiv_apply (n : ℕ) (hn : 2 ≤ n)
    (a : π_ 7 (SpGroup (Fin n)) 1) :
    stabilizationPiSevenMulEquiv n hn a = stabilizationMap n 7 a :=
  stabilizationInRange_apply n 7 (by omega) a

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
