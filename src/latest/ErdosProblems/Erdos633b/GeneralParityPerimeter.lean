import ErdosProblems.Erdos633b.ParityPerimeter

/-! Arbitrary tile and outer parity patterns in the actual signed-length
identity, and the alternate character needed for the case-(6) shape. -/

namespace Erdos633b

local instance : Fact (Module.finrank ℝ Plane = 2) := ⟨by simp [Plane]⟩

theorem parity_double_shift (f : Real.Angle → ZMod 2) (a : ℝ) (δ : ZMod 2)
    (h : ∀ x, f (x + (a : Real.Angle)) = f x + δ) (x : Real.Angle) :
    f (x + ((2 * a : ℝ) : Real.Angle)) = f x := by
  rw [show 2 * a = a + a by ring, Real.Angle.coe_add, ← add_assoc, h, h, add_assoc,
    show δ + δ = 0 from (by decide : ∀ d : ZMod 2, d + d = 0) δ, add_zero]

namespace Triangle

theorem exists_groupOne_alternate_direction_color (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (hirr : Irrational (S.angle 0 / Real.pi)) :
    ∃ f : Real.Angle → ZMod 2,
      (∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1) ∧
      (∀ x, f (x + (S.angle 0 : Real.Angle)) = f x + 1) ∧
      (∀ x, f (x + (S.angle 1 : Real.Angle)) = f x) ∧
      (∀ x, f (x + (S.angle 2 : Real.Angle)) = f x) := by
  obtain ⟨f, hf⟩ := exists_direction_parity 3 2 (by decide) hrel hirr 1 0
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := hf x 3 2
    simp only [Int.cast_ofNat, mul_one, mul_zero, add_zero] at h
    rw [hrel, hthree] at h
    exact h
  · intro x
    simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, mul_zero, add_zero] using hf x 1 0
  · intro x
    simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, mul_zero, zero_add, add_zero] using
      hf x 0 1
  · intro x
    have he : 2 * S.angle 0 + S.angle 1 = S.angle 2 := by linarith [S.angle_sum]
    have h := hf x 2 1
    simp only [Int.cast_ofNat, Int.cast_one, mul_one, mul_zero, add_zero, one_mul] at h
    rw [he, htwo, add_zero] at h
    exact h

end Triangle
namespace Tiling

theorem parity_perimeter {T : Triangle} {n : ℕ} (d : Tiling T n)
    (f : Real.Angle → ZMod 2)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (τ₁ τ₂ δ₁ δ₂ : ZMod 2)
    (ht1 : ∀ x, f (x + (d.tile.angle 1 : Real.Angle)) = f x + τ₁)
    (ht2 : ∀ x, f (x + (d.tile.angle 2 : Real.Angle)) = f x + τ₂)
    (h1 : ∀ x, f (x + (T.angle 1 : Real.Angle)) = f x + δ₁)
    (h2 : ∀ x, f (x + (T.angle 2 : Real.Angle)) = f x + δ₂) :
    ∃ M : ℤ, (M : ℝ) * (d.tile.side 0 + (paritySign (τ₂ + 1) : ℝ) * d.tile.side 1 +
      (paritySign (τ₁ + 1) : ℝ) * d.tile.side 2) =
        T.side 0 + (paritySign (δ₂ + 1) : ℝ) * T.side 1 +
          (paritySign (δ₁ + 1) : ℝ) * T.side 2 := by
  let o : Orientation ℝ Plane (Fin 2) := (EuclideanSpace.basisFun (Fin 2) ℝ).toBasis.orientation
  let u : Plane := d.tile.points 1 - d.tile.points 0
  have hu : u ≠ 0 := sub_ne_zero.mpr (d.tile.independent.injective.ne (by decide))
  let w : Real.Angle → ℝ := fun x => paritySign (f x)
  let c (a : Fin n) : ℤ := paritySign
    (f ((d.tile.move (d.place a)).positiveEdgeDirection o u 0))
  let ε : ℤ := paritySign (f (T.positiveEdgeDirection o u 0))
  let F := d.tile.side 0 + (paritySign (τ₂ + 1) : ℝ) * d.tile.side 1 +
    (paritySign (τ₁ + 1) : ℝ) * d.tile.side 2
  let G := T.side 0 + (paritySign (δ₂ + 1) : ℝ) * T.side 1 +
    (paritySign (δ₁ + 1) : ℝ) * T.side 2
  have hodd (x : Real.Angle) : w (x + (Real.pi : Real.Angle)) = -w x := by
    simp only [w, hp, paritySign_add_one, Int.cast_neg]
  have hInner (a : Fin n) : (∑ j : Fin 3, d.tile.side j *
      w ((d.tile.move (d.place a)).positiveEdgeDirection o u j)) = (c a : ℝ) * F := by
    have hA := (d.tile.move (d.place a)).positive_edge_one_zero_shift o hu f τ₂ hp
      (fun x => by simpa only [Triangle.angle_move] using ht2 x)
    have hB := (d.tile.move (d.place a)).positive_edge_two_zero_shift o hu f τ₁ hp
      (fun x => by simpa only [Triangle.angle_move] using ht1 x)
    simp only [Fin.sum_univ_three, w, hA, hB, paritySign_add, Int.cast_mul, c, F]
    ring
  have hO1 := T.positive_edge_one_zero_shift o hu f δ₂ hp h2
  have hO2 := T.positive_edge_two_zero_shift o hu f δ₁ hp h1
  have hOuter : (∑ j : Fin 3, T.side j * w (T.positiveEdgeDirection o u j)) = (ε : ℝ) * G := by
    simp only [Fin.sum_univ_three, w, hO1, hO2, paritySign_add, Int.cast_mul, ε, G]
    ring
  have he := d.oriented_edge_length_cancellation o hu w hodd
  simp_rw [hInner] at he
  rw [← Finset.sum_mul, hOuter] at he
  have heq : ((∑ a, c a : ℤ) : ℝ) * F = (ε : ℝ) * G := by simpa only [Int.cast_sum] using he
  have hε : (ε : ℝ) ^ 2 = 1 := by
    rcases paritySign_unit (f (T.positiveEdgeDirection o u 0)) with h | h <;>
      simp only [ε, h, Int.cast_one, Int.cast_neg] <;> norm_num
  refine ⟨ε * ∑ a, c a, ?_⟩
  change _ * F = G
  rw [Int.cast_mul, mul_assoc, heq, ← mul_assoc, ← pow_two, hε, one_mul]

end Tiling
end Erdos633b
