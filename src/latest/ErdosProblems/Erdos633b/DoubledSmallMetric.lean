import ErdosProblems.Erdos633b.DoubledScaledPoints

/-! Exact side lengths of the two small triangular pieces. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem aef_sides (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![point d 0 0, pointE d a b m, pointF d a b c m]) (i : Fin 3) :
    S.side i = (2 * m * a * c / (a + b)) * ![b, c, a] i := by
  have hZ : 0 < a + b := add_pos ha hb
  rw [pointE_eq, pointF_eq d a b c m ha hb hc] at hp
  have hs : S.side i ^ 2 = ((2 * m * a * c / (a + b)) * ![b, c, a] i) ^ 2 := by
    rw [side_sq_of_points d he S 0 0 (2 * m * a ^ 3 / (a + b))
      (2 * m * a ^ 2 * b / (a + b)) (2 * m * a * (a - b))
      (2 * m * a * b * (2 * a + b) / (a + b)) hp]
    fin_cases i
    · change (2 * m * a ^ 3 / (a + b) - 2 * m * a * (a - b)) ^ 2 +
        (2 * m * a ^ 3 / (a + b) - 2 * m * a * (a - b)) *
          (2 * m * a ^ 2 * b / (a + b) - 2 * m * a * b * (2 * a + b) / (a + b)) +
        (2 * m * a ^ 2 * b / (a + b) - 2 * m * a * b * (2 * a + b) / (a + b)) ^ 2 =
          (2 * m * a * c / (a + b) * b) ^ 2
      simp only [mul_pow, div_pow, hrel]
      field_simp
      ring
    · change (2 * m * a * (a - b) - 0) ^ 2 + (2 * m * a * (a - b) - 0) *
          (2 * m * a * b * (2 * a + b) / (a + b) - 0) +
        (2 * m * a * b * (2 * a + b) / (a + b) - 0) ^ 2 =
          (2 * m * a * c / (a + b) * c) ^ 2
      have hh : (2 * m * a * c / (a + b) * c) ^ 2 =
          (2 * m * a / (a + b)) ^ 2 * (c ^ 2) ^ 2 := by ring
      rw [hh, hrel]
      field_simp
      ring
    · change (0 - 2 * m * a ^ 3 / (a + b)) ^ 2 +
        (0 - 2 * m * a ^ 3 / (a + b)) * (0 - 2 * m * a ^ 2 * b / (a + b)) +
        (0 - 2 * m * a ^ 2 * b / (a + b)) ^ 2 = (2 * m * a * c / (a + b) * a) ^ 2
      simp only [mul_pow, div_pow, hrel]
      field_simp
      ring
  have hp' : 0 < (2 * m * a * c / (a + b)) * ![b, c, a] i := by
    apply mul_pos (by positivity)
    fin_cases i <;> assumption
  nlinarith [S.side_pos i]

theorem cfg_sides (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hab : a < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![bigC d a b c m, pointF d a b c m, pointG d a b m]) (i : Fin 3) :
    S.side i = (m * a * (b - a) / (a + b)) * ![c, a + b, a] i := by
  have hb : 0 < b := ha.trans hab
  have hZ : 0 < a + b := add_pos ha hb
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  rw [pointF_eq d a b c m ha hb hc] at hp
  have hs : S.side i ^ 2 = ((m * a * (b - a) / (a + b)) * ![c, a + b, a] i) ^ 2 := by
    rw [side_sq_of_points d he S (cX a b c m) (cY a b c m)
      (2 * m * a * (a - b)) (2 * m * a * b * (2 * a + b) / (a + b))
      (m * a * (a - b)) (m * a * (a + 2 * b)) hp]
    fin_cases i
    · change (2 * m * a * (a - b) - m * a * (a - b)) ^ 2 +
        (2 * m * a * (a - b) - m * a * (a - b)) *
          (2 * m * a * b * (2 * a + b) / (a + b) - m * a * (a + 2 * b)) +
        (2 * m * a * b * (2 * a + b) / (a + b) - m * a * (a + 2 * b)) ^ 2 =
          (m * a * (b - a) / (a + b) * c) ^ 2
      simp only [mul_pow, div_pow, hrel]
      field_simp
      ring
    · change (m * a * (a - b) - cX a b c m) ^ 2 +
        (m * a * (a - b) - cX a b c m) * (m * a * (a + 2 * b) - cY a b c m) +
        (m * a * (a + 2 * b) - cY a b c m) ^ 2 = (m * a * (b - a) / (a + b) * (a + b)) ^ 2
      dsimp only [cX, cY]
      rw [hrel]
      field_simp
      ring
    · change (cX a b c m - 2 * m * a * (a - b)) ^ 2 +
        (cX a b c m - 2 * m * a * (a - b)) *
          (cY a b c m - 2 * m * a * b * (2 * a + b) / (a + b)) +
        (cY a b c m - 2 * m * a * b * (2 * a + b) / (a + b)) ^ 2 =
          (m * a * (b - a) / (a + b) * a) ^ 2
      dsimp only [cX, cY]
      rw [hrel]
      field_simp
      ring
  have hp' : 0 < (m * a * (b - a) / (a + b)) * ![c, a + b, a] i := by
    apply mul_pos (by positivity)
    fin_cases i
    · exact hc
    · exact hZ
    · exact ha
  nlinarith [S.side_pos i]

end Erdos633b.DoubledCoordinates
