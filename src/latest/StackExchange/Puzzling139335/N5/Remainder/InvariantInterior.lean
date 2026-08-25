import StackExchange.Puzzling139335.HalfTurnRemainder.ConnectedInterior

/-!
# Connected interior of an invariant two-region union

If a homeomorphism fixes an interior point of a Jordan region and preserves
its union with a second Jordan region, then either the first region is
preserved or the union has connected interior. Disjointness of the two
interiors is not needed.
-/

open Set

namespace Puzzling139335.N5.Remainder

/-- A homeomorphism which fixes an interior point of the first Jordan region,
preserves the two-region union, and does not preserve the first region forces
the union to have connected interior. -/
theorem isConnected_interior_union_of_invariant_homeomorph
    {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (e : Plane ≃ₜ Plane) (hc : c ∈ interior A) (hec : e c = c)
    (hUimage : e '' (A ∪ D) = A ∪ D) (hAnot : e '' A ≠ A) :
    IsConnected (interior (A ∪ D)) := by
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
  · obtain ⟨x, hxW, hxD⟩ := hinter
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
  · have hWDint : Disjoint W (interior D) :=
      Set.disjoint_left.mpr (fun x hxW hxD => hinter ⟨x, hxW, hxD⟩)
    have hWD : Disjoint W D := by
      rw [← hD.closure_interior]
      exact hWDint.closure_right hWopen
    have hWA : W ⊆ A := by
      intro x hxW
      have hxU : x ∈ A ∪ D := interior_subset (hWV hxW)
      exact hxU.resolve_right (fun hxD => Set.disjoint_left.mp hWD hxW hxD)
    have hWeq : W = interior A :=
      Subset.antisymm (interior_maximal hWA hWopen) hAW
    have hVimage : e '' V = V := by
      dsimp only [V]
      rw [e.image_interior, hUimage]
    have hWimage : e '' W = W := by
      dsimp only [W]
      rw [e.image_connectedComponentIn hcV, hVimage, hec]
    have hAintimage : e '' interior A = interior A := by
      rw [← hWeq]
      exact hWimage
    apply False.elim
    apply hAnot
    calc
      e '' A = e '' closure (interior A) :=
        congrArg (fun S => e '' S) hA.closure_interior.symm
      _ = closure (e '' interior A) := e.image_closure _
      _ = closure (interior A) := congrArg closure hAintimage
      _ = A := hA.closure_interior

/-- The same hypotheses also make the closed union connected. -/
theorem isConnected_union_of_invariant_homeomorph
    {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (e : Plane ≃ₜ Plane) (hc : c ∈ interior A) (hec : e c = c)
    (hUimage : e '' (A ∪ D) = A ∪ D) (hAnot : e '' A ≠ A) :
    IsConnected (A ∪ D) := by
  rw [← HalfTurnRemainder.closure_interior_union hA.isClosed hD.isClosed
    hA.closure_interior hD.closure_interior]
  exact (isConnected_interior_union_of_invariant_homeomorph
    hA hD e hc hec hUimage hAnot).closure

end Puzzling139335.N5.Remainder
