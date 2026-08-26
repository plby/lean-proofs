import ErdosProblems.Erdos633b.BoundaryPolynomialRemainders
import ErdosProblems.Erdos633b.Primitive30Polynomial

/-! A fully explicit finite boundary exclusion: tile angles (4,1,10)π/15
cannot tile an outer triangle with angles (8,2,5)π/15. -/

namespace Erdos633b
open Polynomial

def boundary30DoubleTileWeights : Fin 3 → ℕ := ![4, 1, 10]

def boundary30DoubleOuterWeights : Fin 3 → ℕ := ![8, 2, 5]

noncomputable def boundary30DoubleQuotients00 : ℚ[X] :=
  X ^ 40 - X ^ 39 + X ^ 38 + X ^ 35 - X ^ 34 + X ^ 33 - X ^ 26 - X ^ 23 - X ^ 21 - 2 * X ^ 18 + X
    ^ 17 - X ^ 16 - X ^ 13 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X

noncomputable def boundary30DoubleQuotients01 : ℚ[X] :=
  X ^ 46 - X ^ 45 + X ^ 44 + X ^ 41 - X ^ 40 + X ^ 39 - X ^ 31 + X ^ 30 - X ^ 29 - X ^ 26 + X ^
    25 - 2 * X ^ 24 + X ^ 23 - X ^ 22 - X ^ 20 - X ^ 17 + X ^ 16 - 2 * X ^ 15 + 2 * X ^ 14 - X ^ 13
    + X ^ 11 - X ^ 10 + 2 * X ^ 9 - X ^ 8 + X ^ 7 + X ^ 5 + X ^ 2 - X + 2

noncomputable def boundary30DoubleQuotients02 : ℚ[X] :=
  X ^ 43 - X ^ 42 + X ^ 41 + X ^ 38 - X ^ 37 + X ^ 36 - X ^ 28 + X ^ 27 - X ^ 26 - 2 * X ^ 23 + 2
    * X ^ 22 - 3 * X ^ 21 + X ^ 20 - X ^ 19 - X ^ 18 + X ^ 17 - 2 * X ^ 16 + X ^ 15 - X ^ 14 + X ^
    13 - X ^ 12 + X ^ 11 + 2 * X ^ 8 - 2 * X ^ 7 + 3 * X ^ 6 - X ^ 5 + X ^ 4 + X ^ 3 - X ^ 2 + 3 *
    X - 2

noncomputable def boundary30DoubleQuotients10 : ℚ[X] :=
  X ^ 43 - X ^ 42 + X ^ 41 + X ^ 38 - X ^ 37 + X ^ 36 - X ^ 29 - X ^ 26 - X ^ 24 - X ^ 21 - X ^
    15 + 2 * X ^ 14 - X ^ 13 + X ^ 11 - X ^ 10 + 2 * X ^ 9 - X ^ 8 + X ^ 6 + X

noncomputable def boundary30DoubleQuotients11 : ℚ[X] :=
  X ^ 49 - X ^ 48 + X ^ 47 + X ^ 44 - X ^ 43 + X ^ 42 - X ^ 34 + X ^ 33 - X ^ 32 - X ^ 29 + X ^
    28 - X ^ 27 - X ^ 23 + X ^ 22 - 2 * X ^ 21 + X ^ 20 - 2 * X ^ 18 + 2 * X ^ 17 - 2 * X ^ 16 + X
    ^ 15 - X ^ 13 + X ^ 12 + X ^ 8 - X ^ 7 + 2 * X ^ 6 - X ^ 5 + 2 * X ^ 3 - 2 * X ^ 2 + 2 * X - 1

noncomputable def boundary30DoubleQuotients12 : ℚ[X] :=
  X ^ 46 - X ^ 45 + X ^ 44 + X ^ 41 - X ^ 40 + X ^ 39 - X ^ 31 + X ^ 30 - X ^ 29 - 2 * X ^ 26 + 2
    * X ^ 25 - 2 * X ^ 24 - X ^ 21 + X ^ 20 - X ^ 19 - X ^ 18 + X ^ 17 - X ^ 15 + X ^ 14 - X ^ 13 +
    X ^ 12 + X ^ 11 - 2 * X ^ 10 + 2 * X ^ 9 + X ^ 6 - X ^ 5 + X ^ 4 + X ^ 3 - X ^ 2 + 1

noncomputable def boundary30DoubleQuotients20 : ℚ[X] :=
  X ^ 34 - X ^ 33 + X ^ 32 + X ^ 29 - X ^ 28 + X ^ 27 - X ^ 24 + X ^ 23 - X ^ 22 - X ^ 20 - X ^
    19 + X ^ 18 - 2 * X ^ 17 - X ^ 15 - X ^ 12 + X ^ 10 + X ^ 7 + 2 * X ^ 5 + 2 * X ^ 2 + 1

noncomputable def boundary30DoubleQuotients21 : ℚ[X] :=
  X ^ 40 - X ^ 39 + X ^ 38 + X ^ 35 - X ^ 34 + X ^ 33 - X ^ 30 + X ^ 29 - X ^ 28 - 2 * X ^ 25 + 2
    * X ^ 24 - 2 * X ^ 23 - X ^ 20 + X ^ 19 - X ^ 18 + X ^ 15 - 2 * X ^ 14 + 2 * X ^ 13 - X ^ 12 +
    2 * X ^ 10 - 3 * X ^ 9 + 3 * X ^ 8 - X ^ 7 + X ^ 5 + X ^ 2 - 1

noncomputable def boundary30DoubleQuotients22 : ℚ[X] :=
  X ^ 37 - X ^ 36 + X ^ 35 + X ^ 32 - X ^ 31 + X ^ 30 - X ^ 27 + X ^ 26 - X ^ 25 - 2 * X ^ 22 + 2
    * X ^ 21 - 2 * X ^ 20 - 2 * X ^ 17 + 2 * X ^ 16 - 2 * X ^ 15 + 3 * X ^ 7 - 3 * X ^ 6 + 3 * X ^
    5 + 3 * X ^ 2 - 3 * X + 3 * 1

noncomputable def boundary30DoubleQuotients (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then boundary30DoubleQuotients00 else if j = 1 then
    boundary30DoubleQuotients01 else boundary30DoubleQuotients02
  else if i = 1 then if j = 0 then boundary30DoubleQuotients10 else if j = 1 then
    boundary30DoubleQuotients11 else boundary30DoubleQuotients12
  else if j = 0 then boundary30DoubleQuotients20 else if j = 1 then boundary30DoubleQuotients21
    else boundary30DoubleQuotients22

noncomputable def boundary30DoubleRemainders00 : ℚ[X] :=
  X ^ 7 + X ^ 6 - X ^ 4 - X ^ 3 - X ^ 2 - X

noncomputable def boundary30DoubleRemainders01 : ℚ[X] :=
  -2 * X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 - X - 2

noncomputable def boundary30DoubleRemainders02 : ℚ[X] :=
  2 * X ^ 7 + X ^ 6 - X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - X + 2

noncomputable def boundary30DoubleRemainders10 : ℚ[X] :=
  -X ^ 7 + X ^ 5 + X ^ 4 - X ^ 2 - X

noncomputable def boundary30DoubleRemainders11 : ℚ[X] :=
  X ^ 6 - X ^ 4 - X + 1

noncomputable def boundary30DoubleRemainders12 : ℚ[X] :=
  -X ^ 7 + X ^ 6 - X ^ 4 + X ^ 3 + X ^ 2 - X - 1

noncomputable def boundary30DoubleRemainders20 : ℚ[X] :=
  X ^ 5 + X ^ 4 - X ^ 3 - 2 * X ^ 2 - X - 1

noncomputable def boundary30DoubleRemainders21 : ℚ[X] :=
  3 * X ^ 7 - X ^ 5 - X ^ 4 - 2 * X ^ 3 - X ^ 2 + X + 1

noncomputable def boundary30DoubleRemainders22 : ℚ[X] :=
  -3 * 1

noncomputable def boundary30DoubleRemainders (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then boundary30DoubleRemainders00 else if j = 1 then
    boundary30DoubleRemainders01 else boundary30DoubleRemainders02
  else if i = 1 then if j = 0 then boundary30DoubleRemainders10 else if j = 1 then
    boundary30DoubleRemainders11 else boundary30DoubleRemainders12
  else if j = 0 then boundary30DoubleRemainders20 else if j = 1 then boundary30DoubleRemainders21
    else boundary30DoubleRemainders22

theorem boundary30Double_product_0_0 :
    rootSinePoly 30 4 * rootSinePoly 30 8 =
      root30Polynomial * boundary30DoubleQuotients 0 0 + boundary30DoubleRemainders 0 0 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients00, boundary30DoubleRemainders00]
  ring

theorem boundary30Double_product_0_1 :
    rootSinePoly 30 4 * rootSinePoly 30 2 =
      root30Polynomial * boundary30DoubleQuotients 0 1 + boundary30DoubleRemainders 0 1 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients01, boundary30DoubleRemainders01]
  ring

theorem boundary30Double_product_0_2 :
    rootSinePoly 30 4 * rootSinePoly 30 5 =
      root30Polynomial * boundary30DoubleQuotients 0 2 + boundary30DoubleRemainders 0 2 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients02, boundary30DoubleRemainders02]
  ring

theorem boundary30Double_product_1_0 :
    rootSinePoly 30 1 * rootSinePoly 30 8 =
      root30Polynomial * boundary30DoubleQuotients 1 0 + boundary30DoubleRemainders 1 0 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients10, boundary30DoubleRemainders10]
  ring

theorem boundary30Double_product_1_1 :
    rootSinePoly 30 1 * rootSinePoly 30 2 =
      root30Polynomial * boundary30DoubleQuotients 1 1 + boundary30DoubleRemainders 1 1 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients11, boundary30DoubleRemainders11]
  ring

theorem boundary30Double_product_1_2 :
    rootSinePoly 30 1 * rootSinePoly 30 5 =
      root30Polynomial * boundary30DoubleQuotients 1 2 + boundary30DoubleRemainders 1 2 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients12, boundary30DoubleRemainders12]
  ring

theorem boundary30Double_product_2_0 :
    rootSinePoly 30 10 * rootSinePoly 30 8 =
      root30Polynomial * boundary30DoubleQuotients 2 0 + boundary30DoubleRemainders 2 0 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients20, boundary30DoubleRemainders20]
  ring

theorem boundary30Double_product_2_1 :
    rootSinePoly 30 10 * rootSinePoly 30 2 =
      root30Polynomial * boundary30DoubleQuotients 2 1 + boundary30DoubleRemainders 2 1 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients21, boundary30DoubleRemainders21]
  ring

theorem boundary30Double_product_2_2 :
    rootSinePoly 30 10 * rootSinePoly 30 5 =
      root30Polynomial * boundary30DoubleQuotients 2 2 + boundary30DoubleRemainders 2 2 := by
  dsimp [rootSinePoly, root30Polynomial, boundary30DoubleQuotients, boundary30DoubleRemainders,
    boundary30DoubleQuotients22, boundary30DoubleRemainders22]
  ring

theorem boundary30Double_products (l t : Fin 3) :
    rootSinePoly 30 (boundary30DoubleTileWeights l) * rootSinePoly 30
      (boundary30DoubleOuterWeights t) =
      root30Polynomial * boundary30DoubleQuotients l t + boundary30DoubleRemainders l t := by
  fin_cases l <;> fin_cases t
  · exact boundary30Double_product_0_0
  · exact boundary30Double_product_0_1
  · exact boundary30Double_product_0_2
  · exact boundary30Double_product_1_0
  · exact boundary30Double_product_1_1
  · exact boundary30Double_product_1_2
  · exact boundary30Double_product_2_0
  · exact boundary30Double_product_2_1
  · exact boundary30Double_product_2_2

theorem boundary30Double_degree (m : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) :
    (boundaryRemainderPoly m boundary30DoubleRemainders i j).natDegree < 8 := by
  fin_cases i <;> fin_cases j <;>
    simp only [boundaryRemainderPoly, Fin.sum_univ_three] <;>
    dsimp [boundary30DoubleRemainders, boundary30DoubleRemainders00, boundary30DoubleRemainders01,
      boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22]
        <;> compute_degree <;> norm_num

theorem boundary30Double_first_row_zero (m : Fin 3 → Fin 3 → ℕ)
    (hzero : ∀ i j, boundaryRemainderPoly m boundary30DoubleRemainders i j = 0) :
    m 0 0 + m 0 1 + m 0 2 = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h0 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 1
    (hzero 0 1) 0
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h0
  have h1 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 1
    (hzero 0 1) 1
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h1
  have h2 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 1
    (hzero 0 1) 2
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h2
  have h3 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 1
    (hzero 0 1) 3
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h3
  have h4 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 2
    (hzero 0 2) 0
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h4
  have h5 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 2
    (hzero 0 2) 1
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h5
  have h6 := boundary_remainder_coefficients m boundary30DoubleRemainders 0 2
    (hzero 0 2) 2
  norm_num [boundary30DoubleRemainders, boundary30DoubleRemainders00,
    boundary30DoubleRemainders01, boundary30DoubleRemainders02,
      boundary30DoubleRemainders10, boundary30DoubleRemainders11, boundary30DoubleRemainders12,
      boundary30DoubleRemainders20, boundary30DoubleRemainders21, boundary30DoubleRemainders22,
        Fin.sum_univ_three, h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h6
  have hh : (m 0 0 : ℚ) + m 0 1 + m 0 2 + 2 * m 1 1 = 0 := by
    linear_combination (-8/3) * h0 + (-2/3) * h1 + (8/3) * h2 + (-2) * h3 + (-1) * h4 + (-1) * h5
      + (1) * h6
  have hhN : m 0 0 + m 0 1 + m 0 2 + 2 * m 1 1 = 0 := by exact_mod_cast hh
  omega

namespace Tiling

theorem boundary30Double_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (boundary30DoubleTileWeights i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (boundary30DoubleOuterWeights i : ℝ) * (Real.pi / 15)) : False := by
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / 15 : ℝ) : ℂ) * Complex.I)) 30 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceMul, one_mul] using
      primitive_pi_root 15 1 (by decide) (by decide)
  have hP := root30Polynomial_vanishes _ hz
  have hzero (i j : Fin 3) :
      boundaryRemainderPoly d.boundarySideCount boundary30DoubleRemainders i j = 0 := by
    apply d.boundary_polynomial_remainder_zero 15 (by decide)
      boundary30DoubleTileWeights boundary30DoubleOuterWeights hw ha
      (by intro l; fin_cases l <;> decide) (by intro l; fin_cases l <;> decide)
      root30Polynomial hP boundary30DoubleQuotients boundary30DoubleRemainders
        boundary30Double_products i j
    exact boundary30Double_degree d.boundarySideCount i j
  have hrow := boundary30Double_first_row_zero d.boundarySideCount hzero
  obtain ⟨j, hj⟩ := d.boundary_row_positive 0
  have hh : d.boundarySideCount 0 j ≤ ∑ k, d.boundarySideCount 0 k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [Fin.sum_univ_three, hrow] at hh
  omega

end Tiling
end Erdos633b
