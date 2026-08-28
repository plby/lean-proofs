import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicFirstBottReduction
import Wikipedia.HomotopyGroupsOfSpheres.PointedMapHomotopies

/-! # Iterated matrix inclusions realize the existing stable homotopy isomorphisms -/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

def stabilizationIterate (n : ℕ) :
    (r : ℕ) → SpGroup (Fin n) →* SpGroup (Fin (n + r))
  | 0 => MonoidHom.id _
  | r + 1 => (stabilization (n + r)).comp (stabilizationIterate n r)

theorem continuous_stabilizationIterate (n r : ℕ) : Continuous (stabilizationIterate n r) := by
  induction r with
  | zero => exact continuous_id
  | succ r ih => exact (continuous_stabilization (n + r)).comp ih

def stabilizationIterateMap (n r : ℕ) : C(SpGroup (Fin n), SpGroup (Fin (n + r))) :=
  ⟨stabilizationIterate n r, continuous_stabilizationIterate n r⟩

theorem stabilizationInRangeIterate_apply (n k : ℕ) [NeZero k]
    (hk : k ≤ 4 * n + 1) (r : ℕ) (x : π_ k (SpGroup (Fin n)) 1) :
    stabilizationInRangeIterate n k hk r x =
      pointedMap (stabilizationIterateMap n r) 1 1 (stabilizationIterate n r).map_one x := by
  induction r with
  | zero =>
    refine Quotient.inductionOn x fun p ↦ ?_
    change (⟦p⟧ : π_ k (SpGroup (Fin n)) 1) =
      pointedMap (stabilizationIterateMap n 0) 1 1 _ (⟦p⟧ : π_ k (SpGroup (Fin n)) 1)
    exact (pointedMap_mk (stabilizationIterateMap n 0) 1 1
      (stabilizationIterate n 0).map_one p).symm
  | succ r ih =>
    rw [stabilizationInRangeIterate_succ, ih]
    have h := pointedMap_comp (N := Fin k) (stabilizationIterateMap n r)
      (⟨stabilization (n + r), continuous_stabilization (n + r)⟩ :
        C(SpGroup (Fin (n + r)), SpGroup (Fin (n + r + 1))))
      1 1 1 (stabilizationIterate n r).map_one (stabilization (n + r)).map_one
    exact (congrArg (fun f : π_ k (SpGroup (Fin n)) 1 →*
      π_ k (SpGroup (Fin (n + (r + 1)))) 1 ↦ f x) h).symm

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
