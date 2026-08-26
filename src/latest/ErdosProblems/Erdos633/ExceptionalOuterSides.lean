import ErdosProblems.Erdos633.ExceptionalRealParameters

/-!
# Side normalization for the remaining four exceptional outer triangles

The scale and all side equations are obtained from the actual sine rule.
No rationality of a reference side or scale is assumed.
-/

namespace Erdos633

theorem Triangle.groupOne_U_normalized_outer_sides (P R : Triangle) (s : ℝ)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hs : s = 2 * Real.sin (R.angleA / 2))
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 2 * R.angleB) :
    ∃ L : ℝ, 0 < L ∧ P.sideLength 0 / R.sideLength 2 = L ∧
      P.sideLength 1 / R.sideLength 2 = L * (2 - s ^ 2) ∧
      P.sideLength 2 / R.sideLength 2 = L * ((1 - s ^ 2) * (3 - s ^ 2)) := by
  have hsinC : Real.sin P.angleC =
      Real.sin R.angleA * ((1 - s ^ 2) * (3 - s ^ 2)) := by
    rw [hC, show 2 * R.angleB = Real.pi - 3 * R.angleA by linarith, Real.sin_pi_sub]
    exact groupOne_sin_three R.angleA s hs
  have h := P.normalized_outer_sides_of_sines R (Real.sin R.angleA)
    1 (2 - s ^ 2) ((1 - s ^ 2) * (3 - s ^ 2)) R.sin_angleA_pos
    (by rw [hA, mul_one]) (by rw [hB]; exact groupOne_sin_two R.angleA s hs) hsinC
  simpa only [mul_one] using h

theorem Triangle.groupOne_V_normalized_outer_sides (P R : Triangle) (s : ℝ)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi)
    (hs : s = 2 * Real.sin (R.angleA / 2))
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) :
    ∃ L : ℝ, 0 < L ∧ P.sideLength 0 / R.sideLength 2 = L * (s * (2 - s ^ 2)) ∧
      P.sideLength 1 / R.sideLength 2 = L * (1 - s ^ 2) ∧
      P.sideLength 2 / R.sideLength 2 = L := by
  have hRC : R.angleC = Real.pi / 2 + R.angleA / 2 := by linarith [R.angle_sum]
  have hsin : Real.sin R.angleC = Real.cos (R.angleA / 2) := by
    rw [hRC, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have h := P.normalized_outer_sides_of_sines R (Real.sin R.angleC)
    (s * (2 - s ^ 2)) (1 - s ^ 2) 1 R.sin_angleC_pos
    (by rw [hA, hsin]; exact groupOne_sin_two_half R.angleA s hs)
    (by rw [hB, hsin]; exact groupOne_sin_beta R.angleA R.angleB s hrel hs)
    (by rw [hC, hsin, mul_one]; exact groupOne_sin_sum R.angleA R.angleB hrel)
  simpa only [mul_one] using h

theorem Triangle.oneTwenty_Y_normalized_outer_sides (P R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = 2 * R.angleA + R.angleB) :
    ∃ L : ℝ, 0 < L ∧
      P.sideLength 0 / R.sideLength 2 = L * R.normalizedSide 0 ∧
      P.sideLength 1 / R.sideLength 2 =
        L * (R.normalizedSide 1 * (2 * R.normalizedSide 0 + R.normalizedSide 1)) ∧
      P.sideLength 2 / R.sideLength 2 = L * (R.normalizedSide 0 + R.normalizedSide 1) := by
  obtain ⟨_, _, hsA, _, hcA, hcB⟩ := R.oneTwenty_normalized_parameters hrel
  have hsB := (R.oneTwenty_normalized_parameters hrel).2.2.2.1
  apply P.normalized_outer_sides_of_sines R (Real.sin (Real.pi / 3))
  · rw [Real.sin_pi_div_three]
    positivity
  · rw [hA]
    exact hsA
  · rw [hB, Real.sin_two_mul, hsB, hcB]
    ring
  · rw [hC, show 2 * R.angleA + R.angleB = Real.pi / 3 + R.angleA by linarith]
    exact oneTwenty_sin_sixty_add R.angleA (R.normalizedSide 0) (R.normalizedSide 1) hsA hcA

theorem Triangle.oneTwenty_U_two_normalized_outer_sides (P R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = 2 * R.angleA)
    (hC : P.angleC = 3 * R.angleB) :
    ∃ L : ℝ, 0 < L ∧ P.sideLength 0 / R.sideLength 2 = L ∧
      P.sideLength 1 / R.sideLength 2 = L * (R.normalizedSide 0 + 2 * R.normalizedSide 1) ∧
      P.sideLength 2 / R.sideLength 2 =
        L * (3 * R.normalizedSide 1 * (R.normalizedSide 0 + R.normalizedSide 1)) := by
  obtain ⟨_, hc, hsA, _, hcA, _⟩ := R.oneTwenty_normalized_parameters hrel
  have hsinB : Real.sin P.angleB =
      Real.sin R.angleA * (R.normalizedSide 0 + 2 * R.normalizedSide 1) := by
    rw [hB, Real.sin_two_mul, hcA]
    ring
  have hsinC : Real.sin P.angleC =
      Real.sin R.angleA * (3 * R.normalizedSide 1 * (R.normalizedSide 0 + R.normalizedSide 1)) := by
    rw [hC, show 3 * R.angleB = Real.pi - 3 * R.angleA by linarith, Real.sin_pi_sub]
    exact oneTwenty_sin_three R.angleA (R.normalizedSide 0) (R.normalizedSide 1) hsA hc
  have h := P.normalized_outer_sides_of_sines R (Real.sin R.angleA)
    1 (R.normalizedSide 0 + 2 * R.normalizedSide 1)
    (3 * R.normalizedSide 1 * (R.normalizedSide 0 + R.normalizedSide 1))
    R.sin_angleA_pos (by rw [hA, mul_one]) hsinB hsinC
  simpa only [mul_one] using h

end Erdos633
