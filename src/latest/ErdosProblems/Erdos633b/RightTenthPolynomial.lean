import ErdosProblems.Erdos633b.RightTileQuartics
import ErdosProblems.Erdos633b.RightTenthTrigonometry

/-! Polynomial coordinates on the real roots of X^4 - 5 X^2 + 5.
Each pair consists of actual real numbers satisfying two explicit equations. -/

namespace Erdos633b.RightTenth
open Polynomial

structure Pair where
  a : ℝ
  b : ℝ
  quadratic : 4 * a ^ 2 + 2 * a = 1
  unit : a ^ 2 + b ^ 2 = 1

noncomputable def original : Pair :=
  ⟨Real.sin (Real.pi / 10), Real.cos (Real.pi / 10),
    tenth_sine_quadratic, Real.sin_sq_add_cos_sq (Real.pi / 10)⟩

noncomputable def Pair.reflect (P : Pair) : Pair :=
  ⟨P.a, -P.b, P.quadratic, by nlinarith [P.unit]⟩

noncomputable def sinePoly : ℚ[X] := (X ^ 2 - C 3) * C (1 / 2)
noncomputable def cosinePoly : ℚ[X] := X * C (1 / 2)
noncomputable def boundaryPoly (m : Fin 3 → ℕ) : ℚ[X] :=
  C (m 0 : ℚ) * sinePoly + C (m 1 : ℚ) * cosinePoly + C (m 2 : ℚ)

noncomputable def Pair.boundary (P : Pair) (m : Fin 3 → ℕ) : ℝ :=
  (m 0 : ℝ) * P.a + m 1 * P.b + m 2

@[simp] theorem Pair.eval_sine (P : Pair) : aeval (2 * P.b) sinePoly = P.a := by
  have he := (tenth_polynomial_data P.a P.b P.quadratic P.unit).1
  simpa [sinePoly, div_eq_mul_inv] using he.symm

@[simp] theorem Pair.eval_cosine (P : Pair) : aeval (2 * P.b) cosinePoly = P.b := by
  simp [cosinePoly]

@[simp] theorem Pair.eval_boundary (P : Pair) (m : Fin 3 → ℕ) :
    aeval (2 * P.b) (boundaryPoly m) = P.boundary m := by
  simp [boundaryPoly, Pair.boundary]

theorem Pair.transfer (P Q : Pair) (g : ℚ[X]) (hg : aeval (2 * P.b) g = 0) :
    aeval (2 * Q.b) g = 0 := by
  apply rational_polynomial_root_transfer (evenQuartic 5 5) g _ _
    rightQuarticTen_irreducible (evenQuartic_monic 5 5) _ _ hg
  · simpa [evenQuartic] using (tenth_polynomial_data P.a P.b P.quadratic P.unit).2
  · simpa [evenQuartic] using (tenth_polynomial_data Q.a Q.b Q.quadratic Q.unit).2

theorem Pair.exists_negative (P : Pair) (ha : 0 < P.a) (ha2 : P.a < 1 / 2) :
    ∃ Q : Pair, 0 < Q.b ∧ Q.a + 1 / 2 < 0 ∧ P.a ^ 2 < Q.a ^ 2 := by
  obtain ⟨a', b', hb', ha', hs, hu, hq⟩ :=
    tenth_negative_conjugate P.a ha ha2 P.quadratic
  exact ⟨⟨a', b', hq, hu⟩, hb', ha', hs⟩

theorem Pair.transfer_square (P Q : Pair) (n : ℕ) (m : Fin 3 → ℕ)
    (h : (P.boundary m) ^ 2 = 2 * n * P.a ^ 2) :
    (Q.boundary m) ^ 2 = 2 * n * Q.a ^ 2 := by
  let g : ℚ[X] := boundaryPoly m ^ 2 - C (2 * (n : ℚ)) * sinePoly ^ 2
  have hg : aeval (2 * P.b) g = 0 := by simpa [g] using sub_eq_zero.mpr h
  have hg' := P.transfer Q g hg
  simpa [g, sub_eq_zero] using hg'

theorem Pair.transfer_double_side (P Q : Pair) (m l : Fin 3 → ℕ)
    (h : P.boundary l = 2 * P.b * P.boundary m) :
    Q.boundary l = 2 * Q.b * Q.boundary m := by
  let g : ℚ[X] := boundaryPoly l - C 2 * cosinePoly * boundaryPoly m
  have hg : aeval (2 * P.b) g = 0 := by simpa [g] using sub_eq_zero.mpr h
  have hg' := P.transfer Q g hg
  simpa [g, sub_eq_zero] using hg'

end Erdos633b.RightTenth
