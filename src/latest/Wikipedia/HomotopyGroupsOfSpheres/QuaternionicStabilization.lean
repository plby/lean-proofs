import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnComparison
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnFiber
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumnSphere
import Wikipedia.HomotopyGroupsOfSpheres.HighSphereConnectivity
import Wikipedia.HomotopyGroupsOfSpheres.PointedMaps

/-!
# Stabilization of the sixth native homotopy group of quaternionic unitary groups

The standard inclusion `A ↦ diag(1,A)` induces an isomorphism on `π₆`
in every rank at least two. This follows from the proved compact lifting,
the actual fiber identification, and vanishing of `π₆` and `π₇` of the
column sphere. No value of a symplectic homotopy group is assumed.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open HopfProblem.SecondHurewicz

/-- The same fiber homeomorphism, expressed with the actual subgroup type. -/
def fiberGroupHomeomorph (n : ℕ) : SpGroup (Fin n) ≃ₜ axisSubgroup (0 : Fin (n + 1)) :=
  fiberHomeomorph n

theorem fiberGroupHomeomorph_one (n : ℕ) : fiberGroupHomeomorph n 1 = 1 :=
  Subtype.ext ((stabilization n).map_one)

def fiberPiEquiv (n k : ℕ) [NeZero k] :
    π_ k (SpGroup (Fin n)) 1 ≃* π_ k (axisSubgroup (0 : Fin (n + 1))) 1 :=
  pointedHomeomorphMulEquiv (fiberGroupHomeomorph n) 1 1 (fiberGroupHomeomorph_one n)

/-- The native homotopy homomorphism induced by the bordered matrix inclusion. -/
def stabilizationMap (n k : ℕ) [NeZero k] :
    π_ k (SpGroup (Fin n)) 1 →* π_ k (SpGroup (Fin (n + 1))) 1 :=
  pointedMap ⟨stabilization n, continuous_stabilization n⟩ 1 1 (stabilization n).map_one

theorem stabilizationMap_eq (n k : ℕ) [NeZero k] :
    stabilizationMap n k =
      (inclusionMap (j := (0 : Fin (n + 1))) k).comp (fiberPiEquiv n k).toMonoidHom := by
  apply MonoidHom.ext
  intro a
  refine Quotient.inductionOn a fun p => ?_
  change pointedMap _ 1 1 _ (⟦p⟧ : π_ k (SpGroup (Fin n)) 1) =
    inclusionMap k (pointedHomeomorphMulEquiv (fiberGroupHomeomorph n) 1 1 _
      (⟦p⟧ : π_ k (SpGroup (Fin n)) 1))
  rw [pointedMap_mk, pointedHomeomorphMulEquiv_mk]
  rfl

def stabilizationMulEquiv (n k : ℕ) [NeZero k]
    [Subsingleton (π_ k (UnitColumn (Fin (n + 1))) (axisColumn 0))]
    [Subsingleton (π_ (k + 1) (UnitColumn (Fin (n + 1))) (axisColumn 0))] :
    π_ k (SpGroup (Fin n)) 1 ≃* π_ k (SpGroup (Fin (n + 1))) 1 :=
  (fiberPiEquiv n k).trans (inclusionMulEquiv 0 k)

theorem stabilizationMulEquiv_apply (n k : ℕ) [NeZero k]
    [Subsingleton (π_ k (UnitColumn (Fin (n + 1))) (axisColumn 0))]
    [Subsingleton (π_ (k + 1) (UnitColumn (Fin (n + 1))) (axisColumn 0))]
    (a : π_ k (SpGroup (Fin n)) 1) :
    stabilizationMulEquiv n k a = stabilizationMap n k a := by
  rw [stabilizationMap_eq]
  rfl

theorem unitColumn_piSix_subsingleton (n : ℕ) (hn : 2 ≤ n)
    (x : UnitColumn (Fin (n + 1))) :
    Subsingleton (π_ 6 (UnitColumn (Fin (n + 1))) x) := by
  let e := columnSphereHomeomorph n
  let := sphere_piSix_subsingleton (4 * n + 3) (by omega) (e x)
  exact (homeomorphMulEquiv e x).injective.subsingleton

theorem unitColumn_piSeven_subsingleton (n : ℕ) (hn : 2 ≤ n)
    (x : UnitColumn (Fin (n + 1))) :
    Subsingleton (π_ 7 (UnitColumn (Fin (n + 1))) x) := by
  let e := columnSphereHomeomorph n
  let := sphere_piSeven_subsingleton (4 * n + 3) (by omega) (e x)
  exact (homeomorphMulEquiv e x).injective.subsingleton

/-- Unconditional rank stability of the sixth native homotopy group, starting at `Sp(2)`. -/
def stabilizationPiSixMulEquiv (n : ℕ) (hn : 2 ≤ n) :
    π_ 6 (SpGroup (Fin n)) 1 ≃* π_ 6 (SpGroup (Fin (n + 1))) 1 := by
  let := unitColumn_piSix_subsingleton n hn (axisColumn 0)
  let := unitColumn_piSeven_subsingleton n hn (axisColumn 0)
  exact stabilizationMulEquiv n 6

theorem stabilizationPiSixMulEquiv_apply (n : ℕ) (hn : 2 ≤ n)
    (a : π_ 6 (SpGroup (Fin n)) 1) :
    stabilizationPiSixMulEquiv n hn a = stabilizationMap n 6 a := by
  let := unitColumn_piSix_subsingleton n hn (axisColumn 0)
  let := unitColumn_piSeven_subsingleton n hn (axisColumn 0)
  exact stabilizationMulEquiv_apply n 6 a

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
