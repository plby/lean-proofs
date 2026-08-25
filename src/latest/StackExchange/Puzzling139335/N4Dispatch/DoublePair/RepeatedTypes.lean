import StackExchange.Puzzling139335.GeometricReduction
import StackExchange.Puzzling139335.N8.Pairs.Local

/-!
# The repeated intrinsic pair in the `2200` case

The two double-corner tiles each use two distinct intrinsic points.  The
three-type bound makes the two sets intersect.  Since four incidences give
unique ownership of every physical corner, even one shared intrinsic point
forces their actual relative placement to preserve the square.
-/

open Set

namespace Puzzling139335.N4Dispatch.DoublePair

noncomputable section

private theorem two_pairs_intersect {α : Type*}
    {A B S : Finset α} (hA : A.card = 2) (hB : B.card = 2)
    (hAS : A ⊆ S) (hBS : B ⊆ S) (hS : S.card ≤ 3) :
    ∃ p, p ∈ A ∧ p ∈ B := by
  classical
  have hU : (A ∪ B).card ≤ 3 :=
    (Finset.card_le_card (Finset.union_subset hAS hBS)).trans hS
  have hsum := Finset.card_union_add_card_inter A B
  have hpos : 0 < (A ∩ B).card := by omega
  obtain ⟨p, hp⟩ := Finset.card_pos.mp hpos
  exact ⟨p, (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩

/-- The actual intrinsic corner sets of two double-corner tiles have a
common point in every putative counterexample. -/
theorem exists_shared_type (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2) :
    ∃ a b : Fin 4, corner a ∈ d.piece i ∧ corner b ∈ d.piece j ∧
      d.intrinsicCorner i a = d.intrinsicCorner j b := by
  classical
  obtain ⟨p, hpi, hpj⟩ := two_pairs_intersect
    ((N8.intrinsicPair_card d i).trans hi)
    ((N8.intrinsicPair_card d j).trans hj)
    (N8.intrinsicPair_subset_usedCornerTypes d i)
    (N8.intrinsicPair_subset_usedCornerTypes d j)
    (d.usedCornerTypes_card_le_three hc)
  obtain ⟨a, ha, hpa⟩ := (N8.mem_intrinsicPair d i p).mp hpi
  obtain ⟨b, hb, hpb⟩ := (N8.mem_intrinsicPair d j p).mp hpj
  exact ⟨a, b, ha, hb, hpa.trans hpb.symm⟩

/-- In the four-incidence case the two actual double-corner placements
are related by a symmetry of the whole square. -/
theorem relativePlacement_preserves_square (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    {i j : Fin 4} (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2) :
    d.relativePlacement i j '' unitSquare = unitSquare := by
  obtain ⟨a, b, ha, _, hab⟩ := exists_shared_type d hc hi hj
  exact d.relativePlacement_preserves_square_of_unique_corner
    (d.unique_corner_owner_of_four_incidences hN ha) hab

private theorem intrinsicPair_subset_of_relativePlacement_preserves_square
    (d : SquareDissection) (i j : Fin 4)
    (hS : d.relativePlacement i j '' unitSquare = unitSquare) :
    N8.intrinsicPair d i ⊆ N8.intrinsicPair d j := by
  intro p hp
  obtain ⟨a, ha, hpa⟩ := (N8.mem_intrinsicPair d i p).mp hp
  let e := d.relativePlacement i j
  let σ := SquareSymmetry.cornerPermutation e hS.subset
  have hcorner : e (corner a) = corner (σ a) :=
    SquareSymmetry.cornerPermutation_apply e hS.subset a
  have hb : corner (σ a) ∈ d.piece j := by
    rw [← hcorner, ← d.relativePlacement_image i j]
    exact mem_image_of_mem e ha
  apply (N8.mem_intrinsicPair d j p).mpr
  refine ⟨σ a, hb, ?_⟩
  apply (d.placement j).injective
  rw [d.placement_intrinsicCorner, ← hcorner, ← hpa]
  rfl

/-- Equality of the two intrinsic endpoint pairs is a consequence of the
actual relative square symmetry; no choice-transport premise is needed. -/
theorem intrinsicPair_eq (d : SquareDissection)
    (hc : d.HasProtectedCenter) (hN : d.cornerIncidenceCount = 4)
    {i j : Fin 4} (hi : d.tileCornerCount i = 2) (hj : d.tileCornerCount j = 2) :
    N8.intrinsicPair d i = N8.intrinsicPair d j := by
  apply Finset.eq_of_subset_of_card_le
    (intrinsicPair_subset_of_relativePlacement_preserves_square d i j
      (relativePlacement_preserves_square d hc hN hi hj))
  rw [N8.intrinsicPair_card, N8.intrinsicPair_card, hi, hj]

end

end Puzzling139335.N4Dispatch.DoublePair
