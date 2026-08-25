import StackExchange.Puzzling139335.HalfTurnRemainder.Symmetry
import StackExchange.Puzzling139335.JordanFixedPoint
import Mathlib.Topology.Connected.LocallyConnected

/-!
# Connected interior of the actual two-tile remainder

Take the interior component containing the center. It contains the whole
interior of the first tile. If it meets the other interior, their closures
make it dense in the whole remainder and connectedness follows. Otherwise it
equals the first tile's interior and is invariant under the half-turn. The
other tile is then invariant too, contradicting Brouwer and the protected
center. This argument does not assume a Jordan boundary for the union.
-/

open Set

namespace Puzzling139335.HalfTurnRemainder

/-- A finite union of regular closed sets is regular closed. -/
theorem closure_interior_union {X : Type*} [TopologicalSpace X] {A D : Set X}
    (hAc : IsClosed A) (hDc : IsClosed D)
    (hA : closure (interior A) = A) (hD : closure (interior D) = D) :
    closure (interior (A ∪ D)) = A ∪ D := by
  apply Subset.antisymm (closure_minimal interior_subset (hAc.union hDc))
  apply union_subset
  · calc
      A = closure (interior A) := hA.symm
      _ ⊆ closure (interior (A ∪ D)) := closure_mono (interior_mono subset_union_left)
  · calc
      D = closure (interior D) := hD.symm
      _ ⊆ closure (interior (A ∪ D)) := closure_mono (interior_mono subset_union_right)

/-- A centrally symmetric union of two Jordan regions with disjoint interiors
and the center strictly inside the first region has connected interior. -/
theorem isConnected_interior_union_of_pointReflection {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hc : c ∈ interior A)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (A ∪ D) = A ∪ D) :
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
    let e := (AffineIsometryEquiv.pointReflection ℝ c).toHomeomorph
    have hec : e c = c := AffineIsometryEquiv.pointReflection_self (𝕜 := ℝ) c
    have hUimage : e '' (A ∪ D) = A ∪ D := hsym
    have hVimage : e '' V = V := by
      dsimp only [V]
      rw [e.image_interior, hUimage]
    have hWimage : e '' W = W := by
      dsimp only [W]
      rw [e.image_connectedComponentIn hcV, hVimage, hec]
    have hAintimage : e '' interior A = interior A := by
      rw [← hWeq]
      exact hWimage
    have hAimage : e '' A = A := by
      calc
        e '' A = e '' closure (interior A) := congrArg (fun S => e '' S) hA.closure_interior.symm
        _ = closure (e '' interior A) := e.image_closure _
        _ = closure (interior A) := congrArg closure hAintimage
        _ = A := hA.closure_interior
    have hDrec := right_eq_closure_union_sdiff hD.isClosed hD.closure_interior
      (hA.disjoint_interior_left hdis.symm)
    have hDimage : e '' D = D := by
      rw [hDrec, e.image_closure, Set.image_sdiff e.injective, hUimage, hAimage]
    have hDmaps : MapsTo e D D := by
      intro x hx
      rw [← hDimage]
      exact mem_image_of_mem e hx
    obtain ⟨x, hxD, hxe⟩ := hD.exists_fixedPoint e.continuous hDmaps
    have hxc : x = c := AffineIsometryEquiv.pointReflection_fixed_iff.mp hxe
    exact False.elim (Set.disjoint_left.mp (hD.disjoint_interior_left hdis) hc (hxc ▸ hxD))

/-- Connectedness of the closed union follows from the connected interior and
regular closedness of the two original Jordan regions. -/
theorem isConnected_union_of_pointReflection {A D : Set Plane} {c : Plane}
    (hA : IsJordanRegion A) (hD : IsJordanRegion D)
    (hdis : Disjoint (interior A) (interior D)) (hc : c ∈ interior A)
    (hsym : AffineIsometryEquiv.pointReflection ℝ c '' (A ∪ D) = A ∪ D) :
    IsConnected (A ∪ D) := by
  rw [← closure_interior_union hA.isClosed hD.isClosed hA.closure_interior hD.closure_interior]
  exact (isConnected_interior_union_of_pointReflection hA hD hdis hc hsym).closure

end Puzzling139335.HalfTurnRemainder

namespace Puzzling139335.SquareDissection

open HalfTurnRemainder

/-- The actual two-piece remainder of a half-turn pair has connected interior. -/
theorem pair_remainder_isConnected_interior (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    IsConnected (interior (d.piece 0 ∪ d.piece 1)) :=
  isConnected_interior_union_of_pointReflection (d.jordan 0) (d.jordan 1)
    (d.disjoint_interiors (by decide)) hc (d.pair_remainder_pointReflection hpair)

/-- The actual closed two-piece remainder is connected. -/
theorem pair_remainder_isConnected (d : SquareDissection)
    (hpair : AffineIsometryEquiv.pointReflection ℝ squareCenter '' d.piece 2 = d.piece 3)
    (hc : squareCenter ∈ interior (d.piece 0)) :
    IsConnected (d.piece 0 ∪ d.piece 1) :=
  isConnected_union_of_pointReflection (d.jordan 0) (d.jordan 1)
    (d.disjoint_interiors (by decide)) hc (d.pair_remainder_pointReflection hpair)

end Puzzling139335.SquareDissection
