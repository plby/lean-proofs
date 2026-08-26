import ErdosProblems.Erdos633b.DoubledCoordinates

/-! Exact side lengths for the two large triangular pieces in the doubled construction. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem abd_sides (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![point d 0 0, bigB d c m, pointD d a b m]) (i : Fin 3) :
    S.side i = (m * c) * ![b, a, c] i := by
  have hs : S.side i ^ 2 = ((m * c) * ![b, a, c] i) ^ 2 := by
    rw [side_sq_of_points d he S 0 0 (m * c ^ 2) 0 (m * a ^ 2) (m * a * b) hp]
    fin_cases i
    · change (m * c ^ 2 - m * a ^ 2) ^ 2 +
        (m * c ^ 2 - m * a ^ 2) * (0 - m * a * b) +
        (0 - m * a * b) ^ 2 = (m * c * b) ^ 2
      simp only [mul_pow, hrel]
      ring
    · change (m * a ^ 2 - 0) ^ 2 + (m * a ^ 2 - 0) * (m * a * b - 0) +
        (m * a * b - 0) ^ 2 = (m * c * a) ^ 2
      simp only [mul_pow, hrel]
      ring
    · change (0 - m * c ^ 2) ^ 2 + (0 - m * c ^ 2) * (0 - 0) +
        (0 - 0) ^ 2 = (m * c * c) ^ 2
      ring
  have hp' : 0 < m * c * ![b, a, c] i := by
    apply mul_pos (mul_pos hm hc)
    fin_cases i <;> assumption
  nlinarith [S.side_pos i]

theorem bdg_sides (d : ℝ) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (S : Triangle)
    (hp : S.points = ![bigB d c m, pointD d a b m, pointG d a b m]) (i : Fin 3) :
    S.side i = (m * c) * ![a, c, b] i := by
  have hs : S.side i ^ 2 = ((m * c) * ![a, c, b] i) ^ 2 := by
    rw [side_sq_of_points d he S (m * c ^ 2) 0 (m * a ^ 2) (m * a * b)
      (m * a * (a - b)) (m * a * (a + 2 * b)) hp]
    fin_cases i
    · change (m * a ^ 2 - m * a * (a - b)) ^ 2 +
        (m * a ^ 2 - m * a * (a - b)) * (m * a * b - m * a * (a + 2 * b)) +
        (m * a * b - m * a * (a + 2 * b)) ^ 2 = (m * c * a) ^ 2
      simp only [mul_pow, hrel]
      ring
    · change (m * a * (a - b) - m * c ^ 2) ^ 2 +
        (m * a * (a - b) - m * c ^ 2) * (m * a * (a + 2 * b) - 0) +
        (m * a * (a + 2 * b) - 0) ^ 2 = (m * c * c) ^ 2
      have hh : (m * c * c) ^ 2 = m ^ 2 * (c ^ 2) ^ 2 := by ring
      rw [hh, hrel]
      ring
    · change (m * c ^ 2 - m * a ^ 2) ^ 2 +
        (m * c ^ 2 - m * a ^ 2) * (0 - m * a * b) +
        (0 - m * a * b) ^ 2 = (m * c * b) ^ 2
      simp only [mul_pow, hrel]
      ring
  have hp' : 0 < m * c * ![a, c, b] i := by
    apply mul_pos (mul_pos hm hc)
    fin_cases i <;> assumption
  nlinarith [S.side_pos i]

end Erdos633b.DoubledCoordinates
