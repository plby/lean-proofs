import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Normalize
import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Source
import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.UpperCoordinate
import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Crossing
import StackExchange.Puzzling139335.N4MiddleInvolutions.HalfTurn.Fit

/-!
# The intrinsic-coordinate contradiction for an actual half-turn pair

The source and its placement are constructed from the actual dissection.
The only intermediate interface hypothesis is the containing-segment bound,
which the final theorem derives from the finite boundary-arc balance.
-/

open Set

namespace Puzzling139335.N4MiddleInvolutions.HalfTurn

theorem false_of_left_source {d : SquareDissection}
    (h : N4OuterPair.Configuration d) (hc : d.HasProtectedCenter) {C : Plane}
    (hpair : AffineIsometryEquiv.pointReflection ℝ C '' d.piece 2 = d.piece 3)
    (S : LeftSource d)
    (hlarge : ∀ a b : Plane, dist a b ≤ 1 →
      ¬ (d.piece 2 ∩ d.piece 3 ⊆ segment ℝ a b)) : False := by
  let q := S.placement.symm C
  have heq : S.placement q = C := S.placement.apply_symm_apply C
  have hq : q ∈ S.carrier := by
    have hC := (center_mem_common h hc hpair).1
    rw [← S.image] at hC
    obtain ⟨p, hp, hpC⟩ := hC
    have hpq : p = q := S.placement.injective (hpC.trans heq.symm)
    exact hpq ▸ hp
  have hqbox := S.band hq
  have hsourceLarge := source_common_not_in_unit_segment S.placement S.image heq hpair hlarge
  have hpos := source_coordinates_pos_of_large_common S.band hq hsourceLarge
  have hU := image_source_union S.placement S.image heq hpair
  have hquarter : q 1 < (1 / 4 : ℝ) := by
    apply upper_coordinate_lt_quarter S.band S.base S.placement S.oblique.1 S.oblique.2
    · rw [hU]
      exact middleUnion_subset_square d
    · rw [hU]
      exact middleUnion_vertical h hpair
    · rw [hU]
      exact middleUnion_horizontal h
  have hhalf : (1 / 2 : ℝ) ≤ q 0 :=
    half_le_first_coordinate_of_disjoint S.jordan S.band S.base S.arm hpos.1
      ⟨hpos.2, hquarter⟩ (source_interiors_disjoint S.placement S.image heq hpair)
  have hA : S.placement (Schoenflies.Plane.mk 0 0) ∈ middleUnion d := by
    apply Or.inl
    rw [← S.image]
    exact mem_image_of_mem S.placement (S.base (left_mem_segment ℝ _ _))
  have hM : S.placement (Schoenflies.Plane.mk 0 (1 / 2)) ∈ middleUnion d := by
    apply Or.inl
    rw [← S.image]
    exact mem_image_of_mem S.placement (S.arm (right_mem_segment ℝ _ _))
  apply oblique_base_arm_fit_impossible S.placement q hhalf hqbox.2
    S.oblique.1 S.oblique.2
  · rw [heq]
    exact middleUnion_horizontal_displacement_lt_half h hc hpair hA
  · rw [heq]
    exact middleUnion_vertical_displacement_lt_half h hc hpair hA
  · rw [heq]
    exact middleUnion_horizontal_displacement_lt_half h hc hpair hM
  · rw [heq]
    exact middleUnion_vertical_displacement_lt_half h hc hpair hM

end Puzzling139335.N4MiddleInvolutions.HalfTurn
