import ErdosProblems.Erdos633b.DoubledCoordinates

/-! Exact side lengths of the outer doubled triangle. -/

namespace Erdos633b.DoubledCoordinates

open Sixty

theorem outer_sides (d : ℝ) (hd : 0 < d) (he : d ^ 2 = 3) (a b c m : ℝ)
    (ha : 0 < a) (hb : 0 < b) (hc : 0 < c) (hm : 0 < m)
    (hrel : c ^ 2 = a ^ 2 + a * b + b ^ 2) (i : Fin 3) :
    (outer d hd a b c m ha hb hc hm).side i =
      ![m * b * (2 * a + b), m * a * (a + 2 * b), m * c ^ 2] i := by
  let T := outer d hd a b c m ha hb hc hm
  have hC : a ^ 2 + a * b + b ^ 2 ≠ 0 := by rw [← hrel]; exact (sq_pos_of_pos hc).ne'
  have hs : T.side i ^ 2 = (![m * b * (2 * a + b), m * a * (a + 2 * b), m * c ^ 2] i) ^ 2 := by
    rw [side_sq_of_points d he T 0 0 (m * c ^ 2) 0 (cX a b c m) (cY a b c m)
      (outer_points d hd a b c m ha hb hc hm)]
    fin_cases i
    · change (m * c ^ 2 - cX a b c m) ^ 2 +
        (m * c ^ 2 - cX a b c m) * (0 - cY a b c m) + (0 - cY a b c m) ^ 2 =
          (m * b * (2 * a + b)) ^ 2
      dsimp only [cX, cY]
      rw [hrel]
      field_simp
      ring
    · change (cX a b c m - 0) ^ 2 + (cX a b c m - 0) * (cY a b c m - 0) +
        (cY a b c m - 0) ^ 2 = (m * a * (a + 2 * b)) ^ 2
      dsimp only [cX, cY]
      rw [hrel]
      field_simp
      ring
    · change (0 - m * c ^ 2) ^ 2 + (0 - m * c ^ 2) * (0 - 0) + (0 - 0) ^ 2 = (m * c ^ 2) ^ 2
      ring
  have hp : 0 < ![m * b * (2 * a + b), m * a * (a + 2 * b), m * c ^ 2] i := by
    fin_cases i
    · change 0 < m * b * (2 * a + b)
      positivity
    · change 0 < m * a * (a + 2 * b)
      positivity
    · change 0 < m * c ^ 2
      positivity
  nlinarith [T.side_pos i]

end Erdos633b.DoubledCoordinates
