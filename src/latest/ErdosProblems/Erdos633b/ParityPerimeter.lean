import ErdosProblems.Erdos633b.ColorTurnShifts
import ErdosProblems.Erdos633b.GroupOneSignedPerimeter

/-! A reusable integer perimeter identity from a direction parity character
on actual tilings. No regularity of the character is required. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem paritySign_add (x y : ZMod 2) : paritySign (x + y) = paritySign x * paritySign y := by
  revert x y
  decide

namespace Triangle

theorem positive_edge_two_zero_shift (S : Triangle) (o : Orientation ℝ Plane (Fin 2))
    {u : Plane} (hu : u ≠ 0) (f : Real.Angle → ZMod 2) (δ : ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (S.angle 1 : Real.Angle)) = f x + δ) :
    f (S.positiveEdgeDirection o u 2) = f (S.positiveEdgeDirection o u 0) + (δ + 1) := by
  have h := S.positive_edge_zero_two_shift o hu f δ hp ht
  rw [h, add_assoc, show (δ + 1) + (δ + 1) = 0 from
    (by decide : ∀ d : ZMod 2, (d + 1) + (d + 1) = 0) δ, add_zero]

end Triangle
namespace Tiling

theorem groupTwo_parity_perimeter {T : Triangle} {n : ℕ} (d : Tiling T n)
    (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (hb : ∀ x, f (x + (d.tile.angle 1 : Real.Angle)) = f x + 1)
    (hc : ∀ x, f (x + (d.tile.angle 2 : Real.Angle)) = f x)
    (δ₁ δ₂ : ZMod 2)
    (h1 : ∀ x, f (x + (T.angle 1 : Real.Angle)) = f x + δ₁)
    (h2 : ∀ x, f (x + (T.angle 2 : Real.Angle)) = f x + δ₂) :
    ∃ M : ℤ, (M : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      T.side 0 + (paritySign (δ₂ + 1) : ℝ) * T.side 1 +
        (paritySign (δ₁ + 1) : ℝ) * T.side 2 := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  let w : Real.Angle → ℝ := fun x => paritySign (f x)
  let c (a : Fin n) : ℤ := paritySign
    (f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0))
  let ε : ℤ := paritySign (f (T.positiveEdgeDirection o u 0))
  let G := T.side 0 + (paritySign (δ₂ + 1) : ℝ) * T.side 1 +
    (paritySign (δ₁ + 1) : ℝ) * T.side 2
  have hodd (x : Real.Angle) : w (x + (Real.pi : Real.Angle)) = -w x := by
    simp only [w, hp, paritySign_add_one, Int.cast_neg]
  have hInner (a : Fin n) : (∑ j : Fin 3, d.tile.side j *
      w ((d.tile.move (d.place a)).positiveEdgeDirection o u j)) =
        (c a : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) := by
    have hpat := (d.tile.move (d.place a)).positive_color_pattern_odd_even o hu f hp
      (fun x => by simpa only [Triangle.angle_move] using hb x)
      (fun x => by simpa only [Triangle.angle_move] using hc x)
    simp only [Fin.sum_univ_three, w, hpat.1, hpat.2, paritySign_add_one, Int.cast_neg, c]
    ring
  have hO1 := T.positive_edge_one_zero_shift o hu f δ₂ hp h2
  have hO2 := T.positive_edge_two_zero_shift o hu f δ₁ hp h1
  have hOuter : (∑ j : Fin 3, T.side j * w (T.positiveEdgeDirection o u j)) = (ε : ℝ) * G := by
    simp only [Fin.sum_univ_three, w, hO1, hO2, paritySign_add, Int.cast_mul, ε, G]
    ring
  have he := d.oriented_edge_length_cancellation o hu w hodd
  simp_rw [hInner] at he
  rw [← Finset.sum_mul, hOuter] at he
  have heq : ((∑ a, c a : ℤ) : ℝ) * (d.tile.side 0 - d.tile.side 1 + d.tile.side 2) =
      (ε : ℝ) * G := by simpa only [Int.cast_sum] using he
  have hε : (ε : ℝ) ^ 2 = 1 := by
    rcases paritySign_unit (f (T.positiveEdgeDirection o u 0)) with h | h <;>
      simp only [ε, h, Int.cast_one, Int.cast_neg] <;> norm_num
  refine ⟨ε * ∑ a, c a, ?_⟩
  change _ = G
  rw [Int.cast_mul, mul_assoc, heq, ← mul_assoc, ← pow_two, hε, one_mul]

end Tiling
end Erdos633b
