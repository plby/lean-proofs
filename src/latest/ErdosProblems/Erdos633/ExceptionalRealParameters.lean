import ErdosProblems.Erdos633.NormalizedSides
import ErdosProblems.Erdos633.OneTwentyTrigonometry
import ErdosProblems.Erdos633.GroupOneTrigonometry

/-!
# Real normalized parameters of the exceptional reference tiles

These parameters come from the actual Euclidean sides and angles. Their
conic and trigonometric identities are proved before any rationality claim.
-/

namespace Erdos633

theorem oneTwenty_real_cosines (α β a b : ℝ) (hrel : α + β = Real.pi / 3)
    (hsA : Real.sin α = Real.sin (Real.pi / 3) * a)
    (hsB : Real.sin β = Real.sin (Real.pi / 3) * b) :
    Real.cos α = (a + 2 * b) / 2 ∧ Real.cos β = (2 * a + b) / 2 := by
  have hS : Real.sin (Real.pi / 3) ≠ 0 := by
    rw [Real.sin_pi_div_three]
    positivity
  have hβ : Real.sin β = Real.sin (Real.pi / 3) * Real.cos α -
      (1 / 2) * Real.sin α := by
    rw [show β = Real.pi / 3 - α by linarith, Real.sin_sub, Real.cos_pi_div_three]
  have hα : Real.sin α = Real.sin (Real.pi / 3) * Real.cos β -
      (1 / 2) * Real.sin β := by
    rw [show α = Real.pi / 3 - β by linarith, Real.sin_sub, Real.cos_pi_div_three]
  rw [hsA, hsB] at hα hβ
  constructor
  · apply mul_left_cancel₀ hS
    linear_combination -hβ
  · apply mul_left_cancel₀ hS
    linear_combination -hα

theorem oneTwenty_real_conic (α a b : ℝ)
    (hsA : Real.sin α = Real.sin (Real.pi / 3) * a)
    (hcA : Real.cos α = (a + 2 * b) / 2) : a ^ 2 + a * b + b ^ 2 = 1 := by
  have h := Real.sin_sq_add_cos_sq α
  rw [hsA, hcA, Real.sin_pi_div_three] at h
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  linear_combination h - (a ^ 2 / 4) * hroot

theorem Triangle.oneTwenty_normalized_parameters (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi) :
    R.angleC = 2 * Real.pi / 3 ∧
      R.normalizedSide 0 ^ 2 + R.normalizedSide 0 * R.normalizedSide 1 +
        R.normalizedSide 1 ^ 2 = 1 ∧
      Real.sin R.angleA = Real.sin (Real.pi / 3) * R.normalizedSide 0 ∧
      Real.sin R.angleB = Real.sin (Real.pi / 3) * R.normalizedSide 1 ∧
      Real.cos R.angleA = (R.normalizedSide 0 + 2 * R.normalizedSide 1) / 2 ∧
      Real.cos R.angleB = (2 * R.normalizedSide 0 + R.normalizedSide 1) / 2 := by
  have hC : R.angleC = 2 * Real.pi / 3 := by linarith [R.angle_sum]
  have hsinC : Real.sin R.angleC = Real.sin (Real.pi / 3) := by
    rw [hC, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring, Real.sin_pi_sub]
  have hsA : Real.sin R.angleA = Real.sin (Real.pi / 3) * R.normalizedSide 0 := by
    simpa [Triangle.cornerAngle, hsinC] using R.sin_cornerAngle_eq_normalizedSide 0
  have hsB : Real.sin R.angleB = Real.sin (Real.pi / 3) * R.normalizedSide 1 := by
    simpa [Triangle.cornerAngle, hsinC] using R.sin_cornerAngle_eq_normalizedSide 1
  have hc := oneTwenty_real_cosines R.angleA R.angleB
    (R.normalizedSide 0) (R.normalizedSide 1) (by linarith) hsA hsB
  exact ⟨hC, oneTwenty_real_conic _ _ _ hsA hc.1, hsA, hsB, hc⟩

theorem Triangle.groupOne_normalized_parameters (R : Triangle)
    (hrel : 3 * R.angleA + 2 * R.angleB = Real.pi) :
    ∃ s : ℝ, 0 < s ∧ s < 1 ∧ s = 2 * Real.sin (R.angleA / 2) ∧
      R.normalizedSide 0 = s ∧ R.normalizedSide 1 = 1 - s ^ 2 ∧
      2 * Real.cos R.angleA = 2 - s ^ 2 := by
  let s := 2 * Real.sin (R.angleA / 2)
  have hα1 : R.angleA < Real.pi / 3 := by linarith [R.angleB_pos]
  obtain ⟨hs0, hs1⟩ := groupOne_parameter_range R.angleA s R.angleA_pos hα1 rfl
  have hC : R.angleC = Real.pi / 2 + R.angleA / 2 := by linarith [R.angle_sum]
  have hsinC : Real.sin R.angleC = Real.cos (R.angleA / 2) := by
    rw [hC, Real.sin_add, Real.sin_pi_div_two, Real.cos_pi_div_two]
    ring
  have hcos0 : Real.cos (R.angleA / 2) ≠ 0 := by
    rw [← hsinC]
    exact ne_of_gt R.sin_angleC_pos
  have hsA : Real.sin R.angleA = s * Real.cos (R.angleA / 2) := by
    dsimp [s]
    rw [← Real.sin_two_mul, show 2 * (R.angleA / 2) = R.angleA by ring]
  have hsB := groupOne_sin_beta R.angleA R.angleB s hrel rfl
  refine ⟨s, hs0, hs1, rfl, ?_, ?_, groupOne_cos R.angleA s rfl⟩
  · rw [R.normalizedSide_eq_sin_ratio]
    change Real.sin R.angleA / Real.sin R.angleC = s
    rw [hsA, hsinC, mul_div_cancel_right₀ _ hcos0]
  · rw [R.normalizedSide_eq_sin_ratio]
    change Real.sin R.angleB / Real.sin R.angleC = 1 - s ^ 2
    rw [hsB, hsinC, mul_div_cancel_left₀ _ hcos0]

theorem Triangle.oneTwenty_W_normalized_outer_sides (P R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleA + R.angleB)
    (hC : P.angleC = R.angleA + 2 * R.angleB) :
    ∃ L : ℝ, 0 < L ∧
      P.sideLength 0 / R.sideLength 2 = L * R.normalizedSide 0 ∧
      P.sideLength 1 / R.sideLength 2 = L ∧
      P.sideLength 2 / R.sideLength 2 = L * (R.normalizedSide 0 + R.normalizedSide 1) := by
  obtain ⟨_, _, hsA, hsB, _, hcB⟩ := R.oneTwenty_normalized_parameters hrel
  let S := Real.sin (Real.pi / 3)
  let L := P.sineScale * S / R.sideLength 2
  have hS : 0 < S := by dsimp [S]; rw [Real.sin_pi_div_three]; positivity
  have hsum : R.angleA + R.angleB = Real.pi / 3 := by linarith
  have hsinB : Real.sin P.angleB = S := by rw [hB, hsum]
  have hsinC : Real.sin P.angleC = S * (R.normalizedSide 0 + R.normalizedSide 1) := by
    rw [hC, show R.angleA + 2 * R.angleB = Real.pi / 3 + R.angleB by linarith]
    have h := oneTwenty_sin_sixty_add R.angleB (R.normalizedSide 1) (R.normalizedSide 0)
      hsB (by linarith)
    simpa only [S, add_comm] using h
  refine ⟨L, div_pos (mul_pos P.sineScale_pos hS) (R.sideLength_pos 2), ?_, ?_, ?_⟩
  · rw [P.sideLength_eq_sineScale 0]
    change P.sineScale * Real.sin P.angleA / R.sideLength 2 = _
    rw [hA, hsA]
    dsimp [L, S]
    ring
  · rw [P.sideLength_eq_sineScale 1]
    change P.sineScale * Real.sin P.angleB / R.sideLength 2 = _
    rw [hsinB]
  · rw [P.sideLength_eq_sineScale 2]
    change P.sineScale * Real.sin P.angleC / R.sideLength 2 = _
    rw [hsinC]
    dsimp [L]
    ring

theorem Triangle.oneTwenty_Z_normalized_outer_sides (P R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hA : P.angleA = 2 * R.angleA) (hB : P.angleB = 2 * R.angleB)
    (hC : P.angleC = R.angleA + R.angleB) :
    ∃ L : ℝ, 0 < L ∧
      P.sideLength 0 / R.sideLength 2 =
        L * (R.normalizedSide 0 * (R.normalizedSide 0 + 2 * R.normalizedSide 1)) ∧
      P.sideLength 1 / R.sideLength 2 =
        L * (R.normalizedSide 1 * (2 * R.normalizedSide 0 + R.normalizedSide 1)) ∧
      P.sideLength 2 / R.sideLength 2 = L := by
  obtain ⟨_, _, hsA, hsB, hcA, hcB⟩ := R.oneTwenty_normalized_parameters hrel
  let S := Real.sin (Real.pi / 3)
  let L := P.sineScale * S / R.sideLength 2
  have hS : 0 < S := by dsimp [S]; rw [Real.sin_pi_div_three]; positivity
  have hsum : R.angleA + R.angleB = Real.pi / 3 := by linarith
  refine ⟨L, div_pos (mul_pos P.sineScale_pos hS) (R.sideLength_pos 2), ?_, ?_, ?_⟩
  · rw [P.sideLength_eq_sineScale 0]
    change P.sineScale * Real.sin P.angleA / R.sideLength 2 = _
    rw [hA, Real.sin_two_mul, hsA, hcA]
    dsimp [L, S]
    ring
  · rw [P.sideLength_eq_sineScale 1]
    change P.sineScale * Real.sin P.angleB / R.sideLength 2 = _
    rw [hB, Real.sin_two_mul, hsB, hcB]
    dsimp [L, S]
    ring
  · rw [P.sideLength_eq_sineScale 2]
    change P.sineScale * Real.sin P.angleC / R.sideLength 2 = _
    rw [hC, hsum]

theorem Triangle.oneTwenty_normalizedSides_ne_of_independent (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi)
    (hind : IntegerIndependentAngles R.angleA R.angleB) :
    R.normalizedSide 0 ≠ R.normalizedSide 1 := by
  intro hab
  obtain ⟨_, _, _, _, hcA, hcB⟩ := R.oneTwenty_normalized_parameters hrel
  have hcos : Real.cos R.angleA = Real.cos R.angleB := by rw [hcA, hcB, hab]; ring
  have heq := Real.strictAntiOn_cos.injOn
    ⟨R.angleA_pos.le, R.angleA_lt_pi.le⟩ ⟨R.angleB_pos.le, R.angleB_lt_pi.le⟩ hcos
  obtain ⟨h, _⟩ := hind 1 (-1) (by norm_num; linarith)
  norm_num at h

theorem tan_half_mul_one_add_cos (x : ℝ) (hx : Real.cos x ≠ -1) :
    Real.tan (x / 2) * (1 + Real.cos x) = Real.sin x := by
  rw [Real.cos_eq_two_mul_tan_half_div_one_sub_tan_half_sq x hx,
    Real.sin_eq_two_mul_tan_half_div_one_add_tan_half_sq]
  have hd : 1 + Real.tan (x / 2) ^ 2 ≠ 0 := by positivity
  field_simp
  ring

theorem Triangle.oneTwenty_half_tangent_formula (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi) :
    Real.sqrt 3 * Real.tan (R.angleA / 2) =
      3 * R.normalizedSide 0 / (2 + R.normalizedSide 0 + 2 * R.normalizedSide 1) := by
  obtain ⟨_, _, hsA, _, hcA, _⟩ := R.oneTwenty_normalized_parameters hrel
  have ha := R.normalizedSide_pos 0
  have hb := R.normalizedSide_pos 1
  have hcos : Real.cos R.angleA ≠ -1 := by rw [hcA]; linarith
  have h := tan_half_mul_one_add_cos R.angleA hcos
  rw [hcA, hsA, Real.sin_pi_div_three] at h
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  apply (eq_div_iff (by positivity)).mpr
  linear_combination 2 * Real.sqrt 3 * h + R.normalizedSide 0 * hroot

theorem Triangle.oneTwenty_tangent_formula (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi) :
    Real.sqrt 3 * Real.tan R.angleA =
      3 * R.normalizedSide 0 / (R.normalizedSide 0 + 2 * R.normalizedSide 1) := by
  obtain ⟨_, _, hsA, _, hcA, _⟩ := R.oneTwenty_normalized_parameters hrel
  have ha := R.normalizedSide_pos 0
  have hb := R.normalizedSide_pos 1
  rw [Real.tan_eq_sin_div_cos, hsA, hcA, Real.sin_pi_div_three]
  have hroot : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
  field_simp
  nlinarith [hroot]

theorem Triangle.oneTwenty_half_tangent_rational (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi) (hrat : R.CommensurableSides) :
    Real.sqrt 3 * Real.tan (R.angleA / 2) ∈ rationalReals := by
  rw [R.oneTwenty_half_tangent_formula hrel]
  exact rationalReals.div_mem (rationalReals.mul_mem (rationalReals_nat 3) (hrat 0))
    (rationalReals.add_mem (rationalReals.add_mem (rationalReals_nat 2) (hrat 0))
      (rationalReals.mul_mem (rationalReals_nat 2) (hrat 1)))

theorem Triangle.oneTwenty_tangent_rational (R : Triangle)
    (hrel : 3 * R.angleA + 3 * R.angleB = Real.pi) (hrat : R.CommensurableSides) :
    Real.sqrt 3 * Real.tan R.angleA ∈ rationalReals := by
  rw [R.oneTwenty_tangent_formula hrel]
  exact rationalReals.div_mem (rationalReals.mul_mem (rationalReals_nat 3) (hrat 0))
    (rationalReals.add_mem (hrat 0) (rationalReals.mul_mem (rationalReals_nat 2) (hrat 1)))

end Erdos633
