import StackExchange.Puzzling139335.HalfTurnRemainder.Symmetry
import Mathlib.Topology.Connected.LocallyConnected

/-!
# A fixed interior component of a two-piece remainder

A homeomorphism preserving a union of two Jordan regions and fixing an
interior point of the first region either preserves each region separately,
or the union has connected interior.  Preservation of the separate pieces is
a conclusion of the component argument, not an assumed permutation property.
-/

open Set

namespace Puzzling139335.N4Remainder

private theorem connected_or_component_eq_left {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D) (hc : c ∈ interior A) :
    IsConnected (interior (A ∪ D)) ∨
      connectedComponentIn (interior (A ∪ D)) c = interior A := by
  let V := interior (A ∪ D)
  let W := connectedComponentIn V c
  have hAV : interior A ⊆ V := interior_mono subset_union_left
  have hDV : interior D ⊆ V := interior_mono subset_union_right
  have hcV : c ∈ V := hAV hc
  have hWV : W ⊆ V := connectedComponentIn_subset V c
  have hWopen : IsOpen W := isOpen_interior.connectedComponentIn
  have hWconn : IsConnected W := isConnected_connectedComponentIn_iff.mpr hcV
  have hAW : interior A ⊆ W :=
    hA.isConnected_interior.isPreconnected.subset_connectedComponentIn hc hAV
  by_cases hinter : (W ∩ interior D).Nonempty
  · left
    obtain ⟨x, hxW, hxD⟩ := hinter
    have hDW : interior D ⊆ W := by
      have hsub := hD.isConnected_interior.isPreconnected.subset_connectedComponentIn hxD hDV
      have hcomp : W = connectedComponentIn V x := connectedComponentIn_eq hxW
      exact hcomp.symm ▸ hsub
    have hUclosure : A ∪ D ⊆ closure W := by
      apply union_subset
      · rw [← hA.closure_interior]
        exact closure_mono hAW
      · rw [← hD.closure_interior]
        exact closure_mono hDW
    exact hWconn.subset_closure hWV (fun x hx => hUclosure (interior_subset hx))
  · right
    have hWDint : Disjoint W (interior D) :=
      Set.disjoint_left.mpr (fun x hxW hxD => hinter ⟨x, hxW, hxD⟩)
    have hWD : Disjoint W D := by
      rw [← hD.closure_interior]
      exact hWDint.closure_right hWopen
    have hWA : W ⊆ A := by
      intro x hxW
      have hxU : x ∈ A ∪ D := interior_subset (hWV hxW)
      exact hxU.resolve_right (fun hxD => Set.disjoint_left.mp hWD hxW hxD)
    exact Subset.antisymm (interior_maximal hWA hWopen) hAW

/-- If the union's interior is disconnected, a homeomorphism preserving that
union and fixing an interior point of the first piece preserves both pieces.
No Jordan property of the union is required. -/
theorem isConnected_interior_union_or_both_invariant {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hc : c ∈ interior A)
    (e : Plane ≃ₜ Plane) (hec : e c = c) (hsym : e '' (A ∪ D) = A ∪ D) :
    IsConnected (interior (A ∪ D)) ∨ (e '' A = A ∧ e '' D = D) := by
  rcases connected_or_component_eq_left hA hD hc with hconn | hcomponent
  · exact Or.inl hconn
  · right
    have hcV : c ∈ interior (A ∪ D) := interior_mono subset_union_left hc
    have hVimage : e '' interior (A ∪ D) = interior (A ∪ D) := by
      rw [e.image_interior, hsym]
    have hWimage : e '' connectedComponentIn (interior (A ∪ D)) c =
        connectedComponentIn (interior (A ∪ D)) c := by
      rw [e.image_connectedComponentIn hcV, hVimage, hec]
    have hAintimage : e '' interior A = interior A := by
      rw [← hcomponent]
      exact hWimage
    have hAimage : e '' A = A := by
      calc
        e '' A = e '' closure (interior A) :=
          congrArg (fun S => e '' S) hA.closure_interior.symm
        _ = closure (e '' interior A) := e.image_closure _
        _ = closure (interior A) := congrArg closure hAintimage
        _ = A := hA.closure_interior
    have hDrec := HalfTurnRemainder.right_eq_closure_union_sdiff
      hD.isClosed hD.closure_interior (hA.disjoint_interior_left hdis.symm)
    have hDimage : e '' D = D := by
      rw [hDrec, e.image_closure, Set.image_sdiff e.injective, hsym, hAimage]
    exact ⟨hAimage, hDimage⟩

/-- The one-piece invariance alternative, convenient when a separate
geometric argument rules out that invariance. -/
theorem isConnected_interior_union_or_image_eq {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hc : c ∈ interior A)
    (e : Plane ≃ₜ Plane) (hec : e c = c) (hsym : e '' (A ∪ D) = A ∪ D) :
    IsConnected (interior (A ∪ D)) ∨ e '' A = A := by
  rcases isConnected_interior_union_or_both_invariant hA hD hdis hc e hec hsym with
    hconn | hboth
  · exact Or.inl hconn
  · exact Or.inr hboth.1

/-- Excluding individual invariance forces the actual union's interior to
be connected. -/
theorem isConnected_interior_union_of_not_invariant {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hc : c ∈ interior A)
    (e : Plane ≃ₜ Plane) (hec : e c = c) (hsym : e '' (A ∪ D) = A ∪ D)
    (hnot : e '' A ≠ A) : IsConnected (interior (A ∪ D)) :=
  (isConnected_interior_union_or_image_eq hA hD hdis hc e hec hsym).resolve_right hnot

end Puzzling139335.N4Remainder
