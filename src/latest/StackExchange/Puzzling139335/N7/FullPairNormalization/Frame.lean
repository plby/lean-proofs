import StackExchange.Puzzling139335.N7.RepeatedSide
import StackExchange.Puzzling139335.N8.Pairs.Local

/-!
# Ordered normalization of an intrinsic corner pair

A piece containing exactly two square corners occupies the endpoints of
a square side.  A square symmetry puts its specified first intrinsic
endpoint at the bottom-left corner and its second at the bottom-right.
The order is corrected by a vertical reflection when necessary.
-/

open Set

namespace Puzzling139335.N7.FullPairNormalization

open ReflectionSeparation

noncomputable section

/-- Normalize the two actual square-corner images of an ordered intrinsic
pair, preserving the whole square. -/
theorem exists_ordered_pair_frame (d : SquareDissection)
    (hc : d.HasProtectedCenter) (i : Fin 4) (hcount : d.tileCornerCount i = 2)
    (a b : Plane) (_hab : a ≠ b) (hpair : N8.intrinsicPair d i = {a, b}) :
    ∃ f : Plane ≃ᵃⁱ[ℝ] Plane, f '' unitSquare = unitSquare ∧
      f (d.placement i a) = corner 0 ∧ f (d.placement i b) = corner 1 := by
  classical
  obtain ⟨s, hs⟩ := N8.exists_local_side_of_count_two d hc i hcount
  have hends : ({d.placement i a, d.placement i b} : Set Plane) =
      {corner s, corner (s + 1)} := by
    simpa only [hpair, Finset.coe_insert, Finset.coe_singleton, image_pair] using
      N8.local_placement_image_intrinsicPair d hs
  rcases Set.pair_eq_pair_iff.mp hends with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · refine ⟨sideFrame s, sideFrame_image_square s, ?_, ?_⟩
    · rw [ha, sideFrame_first]
    · rw [hb, sideFrame_second]
  · refine ⟨(sideFrame s).trans vertical, ?_, ?_, ?_⟩
    · calc
        ((sideFrame s).trans vertical) '' unitSquare =
            vertical '' (sideFrame s '' unitSquare) := by
          simp only [image_image, AffineIsometryEquiv.coe_trans, Function.comp_def]
        _ = unitSquare := by rw [sideFrame_image_square, vertical_image_unitSquare]
    · change vertical (sideFrame s (d.placement i a)) = corner 0
      rw [ha, sideFrame_second]
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]
    · change vertical (sideFrame s (d.placement i b)) = corner 1
      rw [hb, sideFrame_first]
      ext k
      fin_cases k <;> norm_num [corner, Fin.ext_iff]

end

end Puzzling139335.N7.FullPairNormalization
