import ErdosProblems.Erdos633.OneTwentyTiling
import ErdosProblems.Erdos633.TriangleAngles

/-!
# Euclidean and arithmetic interpretation of the 120-degree construction

The reference triangle really has a 120-degree angle, and the outer triangle
really is equilateral. The constructed count is square exactly when `ab` is
square. No general impossibility theorem for square `ab` is assumed here.
-/

namespace Erdos633

theorem Triangle.angleA_eq_two_pi_div_three_of_squares (P : Triangle)
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hab : Complex.normSq (P.b - P.a) = a ^ 2)
    (hac : Complex.normSq (P.c - P.a) = b ^ 2)
    (hbc : Complex.normSq (P.c - P.b) = a ^ 2 + a * b + b ^ 2) :
    P.angleA = 2 * Real.pi / 3 := by
  have hdab : dist P.a P.b = a := by
    apply (sq_eq_sq₀ dist_nonneg ha.le).mp
    rw [← normSq_sub_eq_dist_sq]
    exact hab
  have hdac : dist P.a P.c = b := by
    apply (sq_eq_sq₀ dist_nonneg hb.le).mp
    rw [← normSq_sub_eq_dist_sq]
    exact hac
  have hcos := EuclideanGeometry.law_cos P.b P.a P.c
  rw [dist_comm P.b P.a, dist_comm P.c P.a, hdab, hdac] at hcos
  have hbc' : dist P.b P.c ^ 2 = a ^ 2 + a * b + b ^ 2 := by
    rw [← normSq_sub_eq_dist_sq]
    exact hbc
  change dist P.b P.c * dist P.b P.c =
    a * a + b * b - 2 * a * b * Real.cos P.angleA at hcos
  have hcosA : Real.cos P.angleA = -(1 / 2) := by
    apply mul_left_cancel₀ (ne_of_gt (mul_pos ha hb))
    nlinarith
  apply Real.injOn_cos ⟨P.angleA_pos.le, P.angleA_lt_pi.le⟩
    ⟨by positivity, by linarith [Real.pi_pos]⟩
  rw [hcosA, show 2 * Real.pi / 3 = Real.pi - Real.pi / 3 by ring,
    Real.cos_pi_sub, Real.cos_pi_div_three]

theorem OneTwentyShape.reference_angleA (S : OneTwentyShape) :
    S.reference.angleA = 2 * Real.pi / 3 := by
  apply S.reference.angleA_eq_two_pi_div_three_of_squares S.a S.b S.a_pos S.b_pos
    S.reference_side_squares.1 S.reference_side_squares.2.1
  rw [S.reference_side_squares.2.2, S.conic]

theorem OneTwentyShape.smallTile_angleA (S : OneTwentyShape) (ε : ℝ) (hε : 0 < ε) :
    (S.smallTile ε hε).angleA = 2 * Real.pi / 3 := by
  apply Triangle.angleA_eq_two_pi_div_three_of_squares _ (ε * S.a) (ε * S.b)
    (mul_pos hε S.a_pos) (mul_pos hε S.b_pos)
  · change Complex.normSq ((0 + (ε : ℂ) * S.reference.b) -
      (0 + (ε : ℂ) * S.reference.a)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.1, Complex.normSq_ofReal]
    ring
  · change Complex.normSq ((0 + (ε : ℂ) * S.reference.c) -
      (0 + (ε : ℂ) * S.reference.a)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.2.1, Complex.normSq_ofReal]
    ring
  · change Complex.normSq ((0 + (ε : ℂ) * S.reference.c) -
      (0 + (ε : ℂ) * S.reference.b)) = _
    rw [normSq_similarity_sub, S.reference_side_squares.2.2, Complex.normSq_ofReal, S.conic]
    ring

theorem hexEquilateral_side_squares (n : ℕ) (hn : 0 < n) :
    Complex.normSq ((hexEquilateral n hn).b - (hexEquilateral n hn).a) = (n : ℝ) ^ 2 ∧
    Complex.normSq ((hexEquilateral n hn).c - (hexEquilateral n hn).a) = (n : ℝ) ^ 2 ∧
    Complex.normSq ((hexEquilateral n hn).c - (hexEquilateral n hn).b) = (n : ℝ) ^ 2 := by
  change Complex.normSq (hexCoordinates (0 + (n : ℂ) * 1) -
      hexCoordinates (0 + (n : ℂ) * 0)) = _ ∧
    Complex.normSq (hexCoordinates (0 + (n : ℂ) * Complex.I) -
      hexCoordinates (0 + (n : ℂ) * 0)) = _ ∧
    Complex.normSq (hexCoordinates (0 + (n : ℂ) * Complex.I) -
      hexCoordinates (0 + (n : ℂ) * 1)) = _
  simp only [hexCoordinates_normSq_sub, Complex.add_re, Complex.add_im,
    Complex.mul_re, Complex.mul_im, Complex.natCast_re, Complex.natCast_im,
    Complex.zero_re, Complex.zero_im, Complex.one_re, Complex.one_im,
    Complex.I_re, Complex.I_im]
  constructor
  · ring
  constructor <;> ring

theorem oneTwenty_equilateral_count_isSquare_iff (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) :
    IsSquare (9 * (c ^ 2) ^ 2 * (a * b) ^ 3) ↔ IsSquare (a * b) := by
  have haQ : (a : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt ha
  have hbQ : (b : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hb
  have hcQ : (c : ℚ) ≠ 0 := by exact_mod_cast ne_of_gt hc
  have h := count_isSquare_iff (9 * (c ^ 2) ^ 2 * (a * b) ^ 3)
    (3 * (c : ℚ) ^ 2 * ((a : ℚ) * b)) ((a * b : ℕ) : ℚ)
    (by positivity) (by push_cast; ring)
  exact h.trans Rat.isSquare_natCast_iff

theorem oneTwenty_integer_equilateral_nonsquare (a b c : ℕ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c)
    (h : c ^ 2 = a ^ 2 + a * b + b ^ 2) (hns : ¬ IsSquare (a * b)) :
    AdmitsNonsquareTiling (hexEquilateral (3 * (c ^ 2 * (a * b))) (by positivity)) := by
  refine ⟨9 * (c ^ 2) ^ 2 * (a * b) ^ 3, _, ?_,
    oneTwenty_integer_equilateral_tiling a b c ha hb hc h⟩
  exact fun hn => hns ((oneTwenty_equilateral_count_isSquare_iff a b c ha hb hc).mp hn)

/-- A checked concrete instance of the full construction, with no tiles enumerated. -/
theorem oneTwenty_three_five_seven_equilateral_tiling :
    ∃ R : Triangle, R.angleA = 2 * Real.pi / 3 ∧
      Nonempty (CongruentTiling (hexEquilateral 2205 (by norm_num)) R 72930375) := by
  let S := OneTwentyShape.ofIntegers 3 5 7 (by norm_num) (by norm_num) (by norm_num)
    (by norm_num)
  have h := oneTwenty_integer_equilateral_tiling 3 5 7 (by norm_num)
    (by norm_num) (by norm_num) (by norm_num)
  refine ⟨S.smallTile (1 / 15) (by norm_num), S.smallTile_angleA _ _, ?_⟩
  norm_num at h
  exact h

end Erdos633
