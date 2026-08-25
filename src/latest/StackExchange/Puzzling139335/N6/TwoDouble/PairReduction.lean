import StackExchange.Puzzling139335.N8.Pairs.Local
import StackExchange.Puzzling139335.N5.Incidence

/-!
# Two-corner pieces without an all-pieces side assignment

Here only the two pieces being compared need to contain two corners. The
local side-pair API supplies the actual chosen placements, and uniqueness
of the unit partner at a full corner identifies their endpoint pairs.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

noncomputable section

/-- Transport an actual unit-side placement together with its endpoints. -/
theorem unitSidePair_image {P : Set Plane} {a b : Plane}
    (h : UnitPairs.IsUnitSidePair P a b) (g : Plane ≃ᵃⁱ[ℝ] Plane) :
    UnitPairs.IsUnitSidePair (g '' P) (g a) (g b) := by
  obtain ⟨ha, hb, hab, e, i, j, he, hei, hej⟩ := h
  refine ⟨mem_image_of_mem g ha, mem_image_of_mem g hb,
    (g.isometry.dist_eq a b).trans hab, g.symm.trans e, i, j, ?_, ?_, ?_⟩
  · rintro _ ⟨_, ⟨p, hp, rfl⟩, rfl⟩
    change e (g.symm (g p)) ∈ unitSquare
    rw [g.symm_apply_apply]
    exact he (mem_image_of_mem e hp)
  · change e (g.symm (g a)) = corner i
    rw [g.symm_apply_apply, hei]
  · change e (g.symm (g b)) = corner j
    rw [g.symm_apply_apply, hej]

/-- Equal intrinsic endpoint pairs determine an actual symmetry of the
square, even when other pieces have only one or no square corner. -/
theorem preserves_square_of_pair_eq (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hi : d.tileCornerCount i = 2)
    (hpair : N8.intrinsicPair d i = N8.intrinsicPair d j) :
    d.relativePlacement i j '' unitSquare = unitSquare := by
  have hj : d.tileCornerCount j = 2 := by
    rw [← N8.intrinsicPair_card, ← hpair, N8.intrinsicPair_card, hi]
  obtain ⟨a, ha⟩ := N8.exists_local_side_of_count_two d hc i hi
  obtain ⟨b, hb⟩ := N8.exists_local_side_of_count_two d hc j hj
  exact N8.local_relativePlacement_preserves_square_of_pair_eq d ha hb hpair

theorem center_not_mem_of_pair_eq (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} (hij : i ≠ j) (hi : d.tileCornerCount i = 2)
    (hpair : N8.intrinsicPair d i = N8.intrinsicPair d j) :
    squareCenter ∉ interior (d.piece i) ∧ squareCenter ∉ interior (d.piece j) :=
  d.center_not_mem_fixed_pair hij (d.relativePlacement i j)
    (d.relativePlacement_image i j)
    (SquareSymmetry.center_fixed_of_preserves_square _
      (preserves_square_of_pair_eq d hc hi hpair))

theorem unitSidePair_of_pair_eq (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i : Fin 4} {a b : Plane} (hab : a ≠ b)
    (hpair : N8.intrinsicPair d i = {a, b}) :
    UnitPairs.IsUnitSidePair (d.piece 0) a b := by
  classical
  have hi : d.tileCornerCount i = 2 := by
    rw [← N8.intrinsicPair_card, hpair]
    simp [hab]
  obtain ⟨j, hj⟩ := N8.exists_local_side_of_count_two d hc i hi
  exact N8.local_isUnitSidePair_of_pair_eq d hj hab hpair

/-- A specified member of a two-element finite set has a unique other
member. This is used to identify the actual unit partner of a full corner. -/
theorem exists_partner {α : Type*} [DecidableEq α] {s : Finset α} {a : α}
    (hcard : s.card = 2) (ha : a ∈ s) : ∃ b, a ≠ b ∧ s = {a, b} := by
  obtain ⟨u, v, huv, hset⟩ := Finset.card_eq_two.mp hcard
  rw [hset] at ha
  rcases Finset.mem_insert.mp ha with rfl | ha
  · exact ⟨v, huv, hset⟩
  · have hav : a = v := Finset.mem_singleton.mp ha
    subst a
    exact ⟨u, Ne.symm huv, hset.trans (Finset.pair_comm _ _)⟩

/-- All two-corner copies using a given full corner have the same actual
intrinsic endpoint pair. Distinct possible partners would form a diameter. -/
theorem pair_eq_of_common_full_type (d : SquareDissection) (hc : d.HasProtectedCenter)
    {i j : Fin 4} {r : Plane} (hi : d.tileCornerCount i = 2)
    (hj : d.tileCornerCount j = 2) (hfull : UnitPairs.IsFullSquareCorner (d.piece 0) r)
    (hri : r ∈ N8.intrinsicPair d i) (hrj : r ∈ N8.intrinsicPair d j) :
    N8.intrinsicPair d i = N8.intrinsicPair d j := by
  classical
  obtain ⟨a, hra, ha⟩ := exists_partner ((N8.intrinsicPair_card d i).trans hi) hri
  obtain ⟨b, hrb, hb⟩ := exists_partner ((N8.intrinsicPair_card d j).trans hj) hrj
  have hab := UnitPairs.unit_partners_eq_of_protected_center d hc 0 hfull
    (unitSidePair_of_pair_eq d hc hra ha) (unitSidePair_of_pair_eq d hc hrb hb)
  rw [ha, hb, hab]

end

end Puzzling139335.N6.TwoDouble
