import ErdosProblems.Erdos633b.RightTenthPolynomial

/-! The negative real conjugate excludes two of the three non-reptiling
outer shapes for a pi/10 right tile. -/

namespace Erdos633b.RightTenth
open Polynomial

theorem Pair.third_sixth_impossible (P : Pair) (ha : 0 < P.a) (ha2 : P.a < 1 / 2)
    (n : ℕ) (hn : 0 < n) (m : Fin 3 → ℕ)
    (h : (n : ℝ) * P.a ^ 2 = (P.boundary m) ^ 2 * (P.a + 1 / 2)) : False := by
  obtain ⟨Q, _, hQneg, hQsq⟩ := P.exists_negative ha ha2
  let g : ℚ[X] := C (n : ℚ) * sinePoly ^ 2 - boundaryPoly m ^ 2 * (sinePoly + C (1 / 2))
  have hg : aeval (2 * P.b) g = 0 := by simpa [g] using sub_eq_zero.mpr h
  have hg' := P.transfer Q g hg
  have he : (n : ℝ) * Q.a ^ 2 = (Q.boundary m) ^ 2 * (Q.a + 1 / 2) := by
    simpa [g, sub_eq_zero] using hg'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hpos : 0 < (n : ℝ) * Q.a ^ 2 := mul_pos hn' (by nlinarith [sq_nonneg P.a])
  have hnonpos : (Q.boundary m) ^ 2 * (Q.a + 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (sq_nonneg _) hQneg.le
  linarith

theorem Pair.second_third_impossible (P : Pair) (ha : 0 < P.a) (ha2 : P.a < 1 / 2)
    (n : ℕ) (hn : 0 < n) (m : Fin 3 → ℕ)
    (h : (n : ℝ) = 2 * (P.boundary m) ^ 2 * (P.a + 1 / 2)) : False := by
  obtain ⟨Q, _, hQneg, _⟩ := P.exists_negative ha ha2
  let g : ℚ[X] := C (n : ℚ) - C 2 * boundaryPoly m ^ 2 * (sinePoly + C (1 / 2))
  have hg : aeval (2 * P.b) g = 0 := by simpa [g] using sub_eq_zero.mpr h
  have hg' := P.transfer Q g hg
  have he : (n : ℝ) = 2 * (Q.boundary m) ^ 2 * (Q.a + 1 / 2) := by
    simpa [g, sub_eq_zero] using hg'
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hnonpos : 2 * (Q.boundary m) ^ 2 * (Q.a + 1 / 2) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) hQneg.le
  linarith

end Erdos633b.RightTenth
