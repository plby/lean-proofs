import StackExchange.Puzzling139335.N6.TwoDouble.MixedScalar
import StackExchange.Puzzling139335.ReflectionSeparation

/-!
# The normalized mixed singleton placement cannot tile the square

Coverage and the two explicit square fits force the left midpoint into
the lower outer piece. Reflection separation gives its lower half-square
containment, after which the actual affine placement contradiction applies.
No tangent, angle, or actual-boundary-segment hypothesis is used here.
-/

open Set

namespace Puzzling139335.N6.TwoDouble

open MixedScalar

theorem leftMidpoint_mem_of_mixed_pair (d : SquareDissection)
    {s c : ℝ} (hs : 0 < s) (hc : 0 ≤ c) (hcircle : s ^ 2 + c ^ 2 = 1)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hrotate : rotation s c '' d.piece 2 = d.piece 3) :
    leftMidpoint ∈ d.piece 0 := by
  have hfix : ReflectionSeparation.horizontal leftMidpoint = leftMidpoint :=
    ReflectionSeparation.horizontal_fixed (by rfl)
  have hnot2 : leftMidpoint ∉ d.piece 2 := by
    intro hM
    have hrot : rotation s c leftMidpoint ∈ d.piece 3 := by
      rw [← hrotate]
      exact mem_image_of_mem _ hM
    have hpos := rotation_fit_first_pos hs hc hcircle (d.piece_subset 3 hrot)
    norm_num at hpos
  have hnot3 : leftMidpoint ∉ d.piece 3 := by
    rw [← hrotate]
    rintro ⟨p, hp, hpM⟩
    have hpos := rotation_image_first_pos hs hc hcircle (d.piece_subset 2 hp)
    rw [hpM, leftMidpoint_zero] at hpos
    exact (lt_irrefl (0 : ℝ)) hpos
  have hM : leftMidpoint ∈ unitSquare := by
    norm_num [leftMidpoint, unitSquare]
  obtain ⟨i, hi⟩ := d.exists_piece_mem hM
  fin_cases i
  · exact hi
  · change leftMidpoint ∈ d.piece 1 at hi
    rw [← hreflect] at hi
    obtain ⟨p, hp, hpM⟩ := hi
    have hpEq : p = leftMidpoint :=
      ReflectionSeparation.horizontal.injective (hpM.trans hfix.symm)
    exact hpEq ▸ hp
  · exact (hnot2 hi).elim
  · exact (hnot3 hi).elim

/-- The actual normalized mixed-singleton branch is impossible. Its two
outer pieces are horizontally reflected copies, and its two remaining
pieces have the displayed rotation relation. The source corner mapping
is an actual congruence between pieces. -/
theorem mixed_rotation_placement_impossible (d : SquareDissection)
    {s c : ℝ} (hs : 0 < s) (hc : 0 < c) (hcircle : s ^ 2 + c ^ 2 = 1)
    (hBL : corner 0 ∈ d.piece 0) (hBR : corner 1 ∈ d.piece 0)
    (hreflect : ReflectionSeparation.horizontal '' d.piece 0 = d.piece 1)
    (hrotate : rotation s c '' d.piece 2 = d.piece 3)
    {b : Plane} (hb : b ∈ d.piece 0) (hbne : b ≠ corner 1)
    (e : Plane ≃ᵃⁱ[ℝ] Plane) (he : e '' d.piece 0 = d.piece 2)
    (heb : e b = corner 1) : False := by
  have hhalf := (d.horizontal_pair_halves_of_bottom_left
    (by decide : (0 : Fin 4) ≠ 1) hreflect hBL).1
  have hzero : corner 0 = (0 : Plane) := by
    ext i
    fin_cases i <;> rfl
  apply no_normalized_mixed_placement hs hc hcircle (d.piece_subset 0)
    (fun p hp => hhalf hp) (hzero ▸ hBL) hBR
    (leftMidpoint_mem_of_mixed_pair d hs hc.le hcircle hreflect hrotate)
    hb hbne e heb
  · rw [he]
    exact d.piece_subset 2
  · rw [he, hrotate]
    exact d.piece_subset 3

end Puzzling139335.N6.TwoDouble
