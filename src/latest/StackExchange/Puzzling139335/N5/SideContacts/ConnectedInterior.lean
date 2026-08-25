import StackExchange.Puzzling139335.JordanRegion
import Mathlib.Topology.Connected.LocallyConnected

/-!
# A genuine interior contact connects a two-region union

If a point common to two Jordan regions is interior to their union, its
open interior component meets both connected tile interiors.  Regular
closedness then makes that component dense in the whole union.  No Jordan
property of the union or assumed shape of the common set is used.
-/

open Set

namespace Puzzling139335.N5.SideContacts

theorem isConnected_interior_union_of_common_interior_point
    {A B : Set Plane} {p : Plane}
    (hA : IsJordanRegion A) (hB : IsJordanRegion B)
    (hp : p ∈ interior (A ∪ B)) (hpA : p ∈ A) (hpB : p ∈ B) :
    IsConnected (interior (A ∪ B)) := by
  let V := interior (A ∪ B)
  let W := connectedComponentIn V p
  have hpW : p ∈ W := mem_connectedComponentIn hp
  have hWV : W ⊆ V := connectedComponentIn_subset V p
  have hWopen : IsOpen W := isOpen_interior.connectedComponentIn
  have hWconn : IsConnected W := isConnected_connectedComponentIn_iff.mpr hp
  have hAclosure : p ∈ closure (interior A) := by
    rwa [hA.closure_interior]
  have hBclosure : p ∈ closure (interior B) := by
    rwa [hB.closure_interior]
  obtain ⟨a, haW, haA⟩ := mem_closure_iff.mp hAclosure W hWopen hpW
  obtain ⟨b, hbW, hbB⟩ := mem_closure_iff.mp hBclosure W hWopen hpW
  have hAW : interior A ⊆ W := by
    have hsub := hA.isConnected_interior.isPreconnected.subset_connectedComponentIn
      haA (show interior A ⊆ V from interior_mono subset_union_left)
    have heq : W = connectedComponentIn V a := connectedComponentIn_eq haW
    exact heq.symm ▸ hsub
  have hBW : interior B ⊆ W := by
    have hsub := hB.isConnected_interior.isPreconnected.subset_connectedComponentIn
      hbB (show interior B ⊆ V from interior_mono subset_union_right)
    have heq : W = connectedComponentIn V b := connectedComponentIn_eq hbW
    exact heq.symm ▸ hsub
  have hdense : A ∪ B ⊆ closure W := by
    apply union_subset
    · rw [← hA.closure_interior]
      exact closure_mono hAW
    · rw [← hB.closure_interior]
      exact closure_mono hBW
  exact hWconn.subset_closure hWV (fun x hx => hdense (interior_subset hx))

end Puzzling139335.N5.SideContacts
