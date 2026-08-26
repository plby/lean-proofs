import ErdosProblems.Erdos633b.DirectionParity

/-! Direction-character rules for the two tiling groups. The group-1
function is unchanged by every exterior turn and flips on reversal. -/

namespace Erdos633b

theorem parity_exterior_turn (f : Real.Angle → ZMod 2) (t : ℝ)
    (hp : ∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1)
    (ht : ∀ x, f (x + (t : Real.Angle)) = f x + 1) (x : Real.Angle) :
    f (x + ((Real.pi - t : ℝ) : Real.Angle)) = f x := by
  apply add_right_cancel (b := (1 : ZMod 2))
  have he : (x + ((Real.pi - t : ℝ) : Real.Angle)) + (t : Real.Angle) =
      x + (Real.pi : Real.Angle) := by
    rw [Real.Angle.coe_sub]
    abel
  have h := ht (x + ((Real.pi - t : ℝ) : Real.Angle))
  rw [he, hp x] at h
  exact h.symm

namespace Triangle

theorem exists_groupOne_direction_color (S : Triangle)
    (hrel : 3 * S.angle 0 + 2 * S.angle 1 = Real.pi)
    (hirr : Irrational (S.angle 0 / Real.pi)) :
    ∃ f : Real.Angle → ZMod 2,
      (∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1) ∧
      (∀ x j, f (x + (S.angle j : Real.Angle)) = f x + 1) ∧
      (∀ x j, f (x + ((Real.pi - S.angle j : ℝ) : Real.Angle)) = f x) := by
  obtain ⟨f, hf⟩ := exists_direction_parity 3 2 (by decide) hrel hirr 1 1
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  have hp (x : Real.Angle) : f (x + (Real.pi : Real.Angle)) = f x + 1 := by
    have h := hf x 3 2
    simp only [Int.cast_ofNat, mul_one] at h
    rw [hrel, hthree, htwo, add_zero] at h
    exact h
  have hg : 2 * S.angle 0 + S.angle 1 = S.angle 2 := by linarith [S.angle_sum]
  have ht (x : Real.Angle) (j : Fin 3) : f (x + (S.angle j : Real.Angle)) = f x + 1 := by
    fin_cases j
    · change f (x + (S.angle 0 : Real.Angle)) = f x + 1
      simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, add_zero] using hf x 1 0
    · change f (x + (S.angle 1 : Real.Angle)) = f x + 1
      simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, zero_add, add_zero] using hf x 0 1
    · have h := hf x 2 1
      simp only [Int.cast_ofNat, Int.cast_one, one_mul, mul_one] at h
      rw [hg, htwo, add_zero] at h
      exact h
  exact ⟨f, hp, ht, fun x j => parity_exterior_turn f (S.angle j) hp (fun y => ht y j) x⟩

theorem exists_groupTwo_direction_parity (S : Triangle) (hg : S.angle 2 = 2 * Real.pi / 3)
    (hirr : Irrational (S.angle 0 / Real.pi)) :
    ∃ f : Real.Angle → ZMod 2,
      (∀ x, f (x + (Real.pi : Real.Angle)) = f x + 1) ∧
      (∀ x, f (x + (S.angle 0 : Real.Angle)) = f x) ∧
      (∀ x, f (x + (S.angle 1 : Real.Angle)) = f x + 1) ∧
      (∀ x, f (x + (S.angle 2 : Real.Angle)) = f x) := by
  have hrel : 3 * S.angle 0 + 3 * S.angle 1 = Real.pi := by linarith [S.angle_sum]
  obtain ⟨f, hf⟩ := exists_direction_parity 3 3 (by decide) hrel hirr 0 1
  have htwo : (2 : ZMod 2) = 0 := by decide
  have hthree : (3 : ZMod 2) = 1 := by decide
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro x
    have h := hf x 3 3
    simp only [Int.cast_ofNat, mul_zero, mul_one, add_zero] at h
    rw [hrel, hthree] at h
    exact h
  · intro x
    simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, mul_zero, add_zero] using hf x 1 0
  · intro x
    simpa only [Int.cast_one, Int.cast_zero, one_mul, zero_mul, zero_add, add_zero] using hf x 0 1
  · intro x
    have he : 2 * S.angle 0 + 2 * S.angle 1 = S.angle 2 := by linarith [S.angle_sum]
    have h := hf x 2 2
    simp only [Int.cast_ofNat, mul_zero, mul_one, add_zero] at h
    rw [he, htwo, add_zero] at h
    exact h

end Triangle
end Erdos633b
