import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.Inversion.Connected
import StackExchange.Puzzling139335.HalfTurnRemainder.JordanUnion.Inversion.Region

/-!
# Inverting a two-region remainder into a Jordan disk

Inversion at an interior point of one Jordan region changes its exterior,
with the center adjoined, into a Jordan interior.  Removing a second set
commutes with this operation provided the second set avoids the center.
This gives the connected remainder needed by the crosscut argument.
-/

open Set Schoenflies

namespace Puzzling139335.HalfTurnRemainder

theorem invert_union_compl_union_singleton_eq {A D : Set Plane} {a : Plane}
    (hA : IsJordanRegion A) (ha : a ∈ interior A) (haD : a ∉ D) :
    invert a '' (A ∪ D)ᶜ ∪ {a} =
      inside (invert a '' frontier A) \ (invert a '' D) := by
  have hain : a ∈ inside (frontier A) := hA.interior_eq_inside_frontier ▸ ha
  rw [← invert_image_outside_union_singleton (fun _ h => arc_complement h)
    hA.frontier_isJordanCurve hain, ← hA.compl_eq_outside_frontier]
  ext z
  by_cases hza : z = a
  · subst z
    simp only [invert_image_eq_preimage, mem_union, mem_preimage, invert_center,
      mem_compl_iff, mem_singleton_iff, mem_sdiff]
    tauto
  · simp only [invert_image_eq_preimage, mem_union, mem_preimage, mem_compl_iff,
      mem_singleton_iff, mem_sdiff]
    tauto

theorem isCompact_invert_image {D : Set Plane} {a : Plane}
    (hD : IsCompact D) (haD : a ∉ D) : IsCompact (invert a '' D) := by
  apply hD.image_of_continuousOn ((continuousOn_invert a).mono ?_)
  intro x hx
  simp only [mem_compl_iff, mem_singleton_iff]
  rintro rfl
  exact haD hx

theorem isConnected_inside_invert_frontier_sdiff_image {A D : Set Plane} {a : Plane}
    (hA : IsJordanRegion A) (hD : IsCompact D) (ha : a ∈ interior A)
    (haD : a ∉ D) (hconn : IsConnected (A ∪ D)ᶜ) :
    IsConnected (inside (invert a '' frontier A) \ (invert a '' D)) := by
  rw [← invert_union_compl_union_singleton_eq hA ha haD]
  exact isConnected_invert_compl_union_singleton (hA.isCompact.union hD)
    (Or.inl (interior_subset ha)) hconn

theorem invert_interior_subset_inside_of_disjoint {A D : Set Plane} {a : Plane}
    (hA : IsJordanRegion A) (hdis : Disjoint (interior A) (interior D))
    (ha : a ∈ interior A) :
    invert a '' interior D ⊆ inside (invert a '' frontier A) := by
  have hain : a ∈ inside (frontier A) := hA.interior_eq_inside_frontier ▸ ha
  rw [← invert_image_outside_union_singleton (fun _ h => arc_complement h)
    hA.frontier_isJordanCurve hain, ← hA.compl_eq_outside_frontier]
  apply subset_trans (image_mono ?_) subset_union_left
  intro x hx hxA
  exact Set.disjoint_left.mp (hA.disjoint_interior_left hdis.symm) hx hxA

end Puzzling139335.HalfTurnRemainder
