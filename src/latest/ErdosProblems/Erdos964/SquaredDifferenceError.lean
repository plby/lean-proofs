import ErdosProblems.Erdos964.SievePolynomial

/-!
# Error propagation for squared differences
-/

namespace Erdos964

theorem abs_sq_sub_sq_le_error (x y E B : ℝ) (hE : 0 ≤ E)
    (hxy : |x - y| ≤ E) (hy : |y| ≤ B) : |x ^ 2 - y ^ 2| ≤ E * (E + 2 * B) := by
  have hsum : |x + y| ≤ E + 2 * B := by
    calc
      _ = |(x - y) + 2 * y| := by congr 1; ring
      _ ≤ |x - y| + |2 * y| := abs_add_le _ _
      _ ≤ E + 2 * B := by rw [abs_mul]; norm_num; linarith
  rw [show x ^ 2 - y ^ 2 = (x - y) * (x + y) by ring, abs_mul]
  exact mul_le_mul hxy hsum (abs_nonneg _) hE

theorem abs_difference_sq_error (a b A B E D : ℝ) (hE : 0 ≤ E)
    (ha : |a - A| ≤ E) (hb : |b - B| ≤ E)
    (hA : |A| ≤ 4 * D) (hB : |B| ≤ 4 * D) :
    |(a - b) ^ 2 - (A - B) ^ 2| ≤ (2 * E) * (2 * E + 16 * D) := by
  have hdiff : |(a - b) - (A - B)| ≤ 2 * E := by
    calc
      _ = |(a - A) - (b - B)| := by congr 1; ring
      _ ≤ |a - A| + |b - B| := abs_sub _ _
      _ ≤ 2 * E := by linarith
  have hmain : |A - B| ≤ 8 * D := (abs_sub A B).trans (by linarith)
  have h := abs_sq_sub_sq_le_error (a - b) (A - B) (2 * E) (8 * D)
    (by positivity) hdiff hmain
  convert h using 1
  ring

end Erdos964
