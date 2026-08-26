import ErdosProblems.Erdos633b.BoundaryPolynomialRemainders
import ErdosProblems.Erdos633b.ScaledAreaRemainders
import ErdosProblems.Erdos633b.PrimitiveFinitePolynomials

/-! Explicit finite geometric exclusion for group-2 shape 3, phase (20,3).
Every polynomial identity, coefficient equation and row combination is checked by Lean. -/

namespace Erdos633b
namespace FiniteThirdOrder20Three
open Polynomial

def tileWeights : Fin 3 → ℕ := ![9, 1, 20]

def outerWeights : Fin 3 → ℕ := ![9, 10, 11]

noncomputable def quotients00 : ℚ[X] :=
  X ^ 86 - X ^ 84 + X ^ 82 + X ^ 76 - X ^ 74 + X ^ 72 - X ^ 56 + X ^ 54 - X ^ 52 - X ^ 46 - X ^ 44
    + X ^ 42 - 2 * X ^ 40 - 2 * X ^ 34 + 2 * X ^ 32 - 2 * X ^ 30 + X ^ 26 - X ^ 24 + X ^ 22 + X ^
    16 + X ^ 14 - X ^ 12 + 2 * X ^ 10 + 2 * X ^ 4 - X ^ 2 + 1

noncomputable def quotients01 : ℚ[X] :=
  X ^ 85 - X ^ 83 + X ^ 81 + X ^ 75 - X ^ 73 + X ^ 71 - X ^ 55 + X ^ 53 - X ^ 51 - 2 * X ^ 45 + X
    ^ 43 - X ^ 41 - X ^ 39 - X ^ 35 - X ^ 29 + X ^ 25 - X ^ 23 + X ^ 21 + 2 * X ^ 15 - X ^ 13 + X
    ^ 11 + X ^ 9 + X ^ 5 + X ^ 3 - X

noncomputable def quotients02 : ℚ[X] :=
  X ^ 84 - X ^ 82 + X ^ 80 + X ^ 74 - X ^ 72 + X ^ 70 - X ^ 54 + X ^ 52 - X ^ 50 - X ^ 46 - X ^ 42
    - X ^ 38 - X ^ 36 + X ^ 34 - 2 * X ^ 32 + X ^ 30 - X ^ 28 + X ^ 24 - X ^ 22 + X ^ 20 + X ^ 16
    + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 2

noncomputable def quotients10 : ℚ[X] :=
  X ^ 94 - X ^ 92 + X ^ 90 + X ^ 84 - X ^ 82 + X ^ 80 - X ^ 64 + X ^ 62 - X ^ 60 - X ^ 54 - X ^ 48
    - X ^ 42 + X ^ 40 - X ^ 38 - X ^ 36 + 2 * X ^ 34 - 2 * X ^ 32 + X ^ 30 - X ^ 26 + 2 * X ^ 24 -
    X ^ 22 + X ^ 18 + X ^ 12 - X ^ 10 + X ^ 8 + X ^ 6 - 2 * X ^ 4 + 2 * X ^ 2 - 1

noncomputable def quotients11 : ℚ[X] :=
  X ^ 93 - X ^ 91 + X ^ 89 + X ^ 83 - X ^ 81 + X ^ 79 - X ^ 63 + X ^ 61 - X ^ 59 - 2 * X ^ 53 + 2
    * X ^ 51 - 2 * X ^ 49 - X ^ 43 + X ^ 41 - X ^ 39 - X ^ 35 + 2 * X ^ 33 - 2 * X ^ 31 + X ^ 29 -
    X ^ 25 + 3 * X ^ 23 - 3 * X ^ 21 + 2 * X ^ 19 + X ^ 13 - X ^ 11 + X ^ 9 + X ^ 5 - 2 * X ^ 3 +
    2 * X

noncomputable def quotients12 : ℚ[X] :=
  X ^ 92 - X ^ 90 + X ^ 88 + X ^ 82 - X ^ 80 + X ^ 78 - X ^ 62 + X ^ 60 - X ^ 58 - X ^ 54 - X ^ 48
    - X ^ 44 + X ^ 42 - X ^ 40 - X ^ 34 + 2 * X ^ 32 - 2 * X ^ 30 + X ^ 28 + X ^ 22 - X ^ 20 + X ^
    18 + X ^ 14 - X ^ 12 + X ^ 10 + X ^ 4 - 2 * X ^ 2 + 2

noncomputable def quotients20 : ℚ[X] :=
  X ^ 75 - X ^ 73 + X ^ 71 + X ^ 65 - X ^ 63 + X ^ 61 - X ^ 55 + X ^ 53 - X ^ 51 - 2 * X ^ 45 + 2
    * X ^ 43 - 2 * X ^ 41 - X ^ 35 - X ^ 29 + X ^ 25 - 2 * X ^ 23 + 2 * X ^ 21 - X ^ 19 + 2 * X ^
    15 - X ^ 13 + X ^ 11 + X ^ 9 + X ^ 5 + X ^ 3 - X

noncomputable def quotients21 : ℚ[X] :=
  X ^ 74 - X ^ 72 + X ^ 70 + X ^ 64 - X ^ 62 + X ^ 60 - X ^ 54 + X ^ 52 - X ^ 50 - 2 * X ^ 44 + 2
    * X ^ 42 - 2 * X ^ 40 - 2 * X ^ 34 + 2 * X ^ 32 - 2 * X ^ 30 + 3 * X ^ 14 - 3 * X ^ 12 + 3 * X
    ^ 10 + 3 * X ^ 4 - 3 * X ^ 2 + 3

noncomputable def quotients22 : ℚ[X] :=
  X ^ 73 - X ^ 71 + X ^ 69 + X ^ 63 - X ^ 61 + X ^ 59 - X ^ 53 + X ^ 51 - X ^ 49 - 2 * X ^ 43 + 2
    * X ^ 41 - 2 * X ^ 39 - X ^ 35 - X ^ 29 - X ^ 25 + 2 * X ^ 23 - 2 * X ^ 21 + X ^ 19 + X ^ 15 +
    X ^ 13 - X ^ 11 + 2 * X ^ 9 + 2 * X ^ 5 - X ^ 3 + X

noncomputable def quotients (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then quotients00 else if j = 1 then quotients01 else quotients02
  else if i = 1 then if j = 0 then quotients10 else if j = 1 then quotients11 else quotients12
  else if j = 0 then quotients20 else if j = 1 then quotients21 else quotients22

noncomputable def remainders00 : ℚ[X] :=
  X ^ 14 - X ^ 6 - X ^ 4 - 1

noncomputable def remainders01 : ℚ[X] :=
  2 * X ^ 15 + 2 * X ^ 13 - X ^ 11 - X ^ 9 - 2 * X ^ 7 - 2 * X ^ 5 + X

noncomputable def remainders02 : ℚ[X] :=
  X ^ 14 + X ^ 12 - X ^ 8 - X ^ 6 - X ^ 4 - X ^ 2

noncomputable def remainders10 : ℚ[X] :=
  X ^ 12 - X ^ 8 - X ^ 2 + 1

noncomputable def remainders11 : ℚ[X] :=
  -X ^ 15 - X ^ 13 + 2 * X ^ 11 - X ^ 9 + X ^ 7 + X ^ 5 - 2 * X

noncomputable def remainders12 : ℚ[X] :=
  -X ^ 14 + X ^ 6 + X ^ 4 - 2

noncomputable def remainders20 : ℚ[X] :=
  2 * X ^ 15 + 2 * X ^ 13 - X ^ 11 - X ^ 9 - 2 * X ^ 7 - 2 * X ^ 5 + X

noncomputable def remainders21 : ℚ[X] :=
  -3

noncomputable def remainders22 : ℚ[X] :=
  X ^ 15 + X ^ 13 + X ^ 11 - 2 * X ^ 9 - X ^ 7 - X ^ 5 - X

noncomputable def remainders (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then remainders00 else if j = 1 then remainders01 else remainders02
  else if i = 1 then if j = 0 then remainders10 else if j = 1 then remainders11 else remainders12
  else if j = 0 then remainders20 else if j = 1 then remainders21 else remainders22

theorem product_0_0 : rootSinePoly 60 9 * rootSinePoly 60 9 =
    root60Polynomial * quotients 0 0 + remainders 0 0 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients00, remainders00]
  ring

theorem product_0_1 : rootSinePoly 60 9 * rootSinePoly 60 10 =
    root60Polynomial * quotients 0 1 + remainders 0 1 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients01, remainders01]
  ring

theorem product_0_2 : rootSinePoly 60 9 * rootSinePoly 60 11 =
    root60Polynomial * quotients 0 2 + remainders 0 2 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients02, remainders02]
  ring

theorem product_1_0 : rootSinePoly 60 1 * rootSinePoly 60 9 =
    root60Polynomial * quotients 1 0 + remainders 1 0 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients10, remainders10]
  ring

theorem product_1_1 : rootSinePoly 60 1 * rootSinePoly 60 10 =
    root60Polynomial * quotients 1 1 + remainders 1 1 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients11, remainders11]
  ring

theorem product_1_2 : rootSinePoly 60 1 * rootSinePoly 60 11 =
    root60Polynomial * quotients 1 2 + remainders 1 2 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients12, remainders12]
  ring

theorem product_2_0 : rootSinePoly 60 20 * rootSinePoly 60 9 =
    root60Polynomial * quotients 2 0 + remainders 2 0 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients20, remainders20]
  ring

theorem product_2_1 : rootSinePoly 60 20 * rootSinePoly 60 10 =
    root60Polynomial * quotients 2 1 + remainders 2 1 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients21, remainders21]
  ring

theorem product_2_2 : rootSinePoly 60 20 * rootSinePoly 60 11 =
    root60Polynomial * quotients 2 2 + remainders 2 2 := by
  dsimp [rootSinePoly, root60Polynomial, quotients, remainders, quotients22, remainders22]
  ring

theorem products (i j : Fin 3) :
    rootSinePoly 60 (tileWeights i) * rootSinePoly 60 (outerWeights j) =
      root60Polynomial * quotients i j + remainders i j := by
  fin_cases i <;> fin_cases j
  · exact product_0_0
  · exact product_0_1
  · exact product_0_2
  · exact product_1_0
  · exact product_1_1
  · exact product_1_2
  · exact product_2_0
  · exact product_2_1
  · exact product_2_2

theorem remainder_degree (m : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) :
    (boundaryRemainderPoly m remainders i j).natDegree < 16 := by
  fin_cases i <;> fin_cases j <;>
    simp only [boundaryRemainderPoly, Fin.sum_univ_three] <;>
    dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22] <;> compute_degree <;> norm_num

theorem coefficient_0 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-3 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 1 0 : ℚ) + (-1 : ℚ) * (m 1 1 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 0 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_1 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (1 : ℚ) * (m 0 0 : ℚ) + (-2 : ℚ) * (m 0 1 : ℚ) + (-1 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_2 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (1 : ℚ) * (m 1 1 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 2 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]

theorem coefficient_3 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (1 : ℚ) * (m 1 0 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 4 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]

theorem coefficient_4 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-2 : ℚ) * (m 0 0 : ℚ) + (1 : ℚ) * (m 0 1 : ℚ) + (2 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 5 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_5 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-2 : ℚ) * (m 0 1 : ℚ) + (1 : ℚ) * (m 2 0 : ℚ) + (-1 : ℚ) * (m 2 1 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 0 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_6 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-1 : ℚ) * (m 0 2 : ℚ) + (-1 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_7 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (1 : ℚ) * (m 2 1 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 2 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]

noncomputable def pattern (i j : Fin 3) : ℕ :=
  if i = 0 then if j = 0 then 1 else if j = 1 then 0 else 0
  else if i = 1 then if j = 0 then 0 else if j = 1 then 0 else 1
  else if j = 0 then 1 else if j = 1 then 1 else 0

theorem counts_scaled (m : Fin 3 → Fin 3 → ℕ)
    (hz : ∀ i j, boundaryRemainderPoly m remainders i j = 0) :
    ∀ i j, m i j = pattern i j * m 0 0 := by
  have h0 := coefficient_0 m (hz 0 1)
  have h1 := coefficient_1 m (hz 0 1)
  have h2 := coefficient_2 m (hz 0 1)
  have h3 := coefficient_3 m (hz 0 1)
  have h4 := coefficient_4 m (hz 0 1)
  have h5 := coefficient_5 m (hz 0 2)
  have h6 := coefficient_6 m (hz 0 2)
  have h7 := coefficient_7 m (hz 0 2)
  intro i j
  fin_cases i <;> fin_cases j
  · change m 0 0 = 1 * m 0 0
    omega
  · change m 0 1 = 0 * m 0 0
    have hh : (m 0 1 : ℚ) - (0 : ℚ) * m 0 0 = 0 := by
      linear_combination (-2/3) * h1 + (-1/3) * h4
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 0 2 = 0 * m 0 0
    have hh : (m 0 2 : ℚ) - (0 : ℚ) * m 0 0 = 0 := by
      linear_combination (-1/3) * h0 + (-1/3) * h2 + (1/3) * h3
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 0 = 0 * m 0 0
    have hh : (m 1 0 : ℚ) - (0 : ℚ) * m 0 0 = 0 := by
      linear_combination (1) * h3
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 1 = 0 * m 0 0
    have hh : (m 1 1 : ℚ) - (0 : ℚ) * m 0 0 = 0 := by
      linear_combination (1) * h2
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 2 = 1 * m 0 0
    have hh : (m 1 2 : ℚ) - (1 : ℚ) * m 0 0 = 0 := by
      linear_combination (1/3) * h1 + (2/3) * h4
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 0 = 1 * m 0 0
    have hh : (m 2 0 : ℚ) - (1 : ℚ) * m 0 0 = 0 := by
      linear_combination (-4/3) * h1 + (-2/3) * h4 + (1) * h5 + (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 1 = 1 * m 0 0
    have hh : (m 2 1 : ℚ) - (1 : ℚ) * m 0 0 = 0 := by
      linear_combination (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 2 = 0 * m 0 0
    have hh : (m 2 2 : ℚ) - (0 : ℚ) * m 0 0 = 0 := by
      linear_combination (1/3) * h0 + (1/3) * h2 + (-1/3) * h3 + (-1) * h6
    exact_mod_cast (sub_eq_zero.mp hh)

noncomputable def areaQuotient : ℚ[X] :=
  X ^ 83 - X ^ 81 + X ^ 79 + X ^ 75 + X ^ 69 + X ^ 65 - 2 * X ^ 63 + 2 * X ^ 61 - X ^ 59 - X ^ 55
    - X ^ 53 + X ^ 51 - 2 * X ^ 49 - 2 * X ^ 45 + X ^ 43 - X ^ 41 - X ^ 39 - X ^ 35 + X ^ 33 - X ^
    31 + X ^ 23 - X ^ 21 + X ^ 19 + X ^ 15 + X ^ 13 - X ^ 11 + 2 * X ^ 9 + 2 * X ^ 5 - X ^ 3 + X


noncomputable def areaRemainder : ℚ[X] :=
  X ^ 15 + X ^ 13 + X ^ 11 - 2 * X ^ 9 - X ^ 7 - X ^ 5 - X


noncomputable def tileQuotient : ℚ[X] :=
  X ^ 83 - X ^ 81 + X ^ 79 + X ^ 73 - X ^ 71 + X ^ 69 - X ^ 63 + X ^ 61 - X ^ 59 - 2 * X ^ 53 + 2
    * X ^ 51 - 2 * X ^ 49 - X ^ 43 + X ^ 41 - X ^ 39 + X ^ 33 - X ^ 31 + X ^ 29 - X ^ 25 + 3 * X ^
    23 - 3 * X ^ 21 + 2 * X ^ 19 - X ^ 15 + 2 * X ^ 13 - 2 * X ^ 11 + X ^ 9 + X ^ 5 - 2 * X ^ 3 +
    2 * X


noncomputable def tileRemainder : ℚ[X] :=
  -X ^ 15 - X ^ 13 + 2 * X ^ 11 - X ^ 9 + X ^ 7 + X ^ 5 - 2 * X

theorem area_product : rootAreaBasePoly 60 tileWeights pattern =
    root60Polynomial * areaQuotient + areaRemainder := by
  simp only [rootAreaBasePoly, rootBoundaryPoly, Fin.sum_univ_three]
  dsimp [tileWeights, pattern, rootSinePoly, root60Polynomial, areaQuotient, areaRemainder]
  simp only [map_zero, map_one]
  ring

theorem tile_product : rootTileAreaPoly 60 tileWeights =
    root60Polynomial * tileQuotient + tileRemainder := by
  dsimp [rootTileAreaPoly, tileWeights, rootSinePoly, root60Polynomial, tileQuotient,
    tileRemainder]
  ring

theorem area_remainder_degree (r n : ℕ) :
    (scaledAreaRemainder r n areaRemainder tileRemainder).natDegree < 16 := by
  dsimp [scaledAreaRemainder, areaRemainder, tileRemainder]
  compute_degree
  norm_num

theorem area_count_zero (r n : ℕ)
    (hz : scaledAreaRemainder r n areaRemainder tileRemainder = 0) : n = 0 := by
  have h0 := scaledAreaRemainder_coefficients r n areaRemainder tileRemainder hz 1
  norm_num [areaRemainder, tileRemainder, coeff_X, coeff_one,
    -map_add, -map_mul, -map_sub] at h0
  have h1 := scaledAreaRemainder_coefficients r n areaRemainder tileRemainder hz 5
  norm_num [areaRemainder, tileRemainder, coeff_X, coeff_one,
    -map_add, -map_mul, -map_sub] at h1
  have hn : (n : ℚ) = 0 := by linarith
  exact_mod_cast hn

end FiniteThirdOrder20Three
namespace Tiling
open FiniteThirdOrder20Three

theorem groupTwo_finite_20_3_3_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (tileWeights i : ℝ) * (Real.pi / 30))
    (ha : ∀ i, T.angle i = (outerWeights i : ℝ) * (Real.pi / 30)) : False := by
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / 30 : ℝ) : ℂ) * Complex.I)) 60 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceMul, one_mul] using
      primitive_pi_root 30 1 (by decide) (by decide)
  have hP := root60Polynomial_vanishes _ hz
  have hzero (i j : Fin 3) : boundaryRemainderPoly d.boundarySideCount remainders i j = 0 := by
    apply d.boundary_polynomial_remainder_zero 30 (by decide) tileWeights outerWeights hw ha
      (by intro l; fin_cases l <;> decide) (by intro l; fin_cases l <;> decide)
      root60Polynomial hP quotients remainders products i j
    exact remainder_degree d.boundarySideCount i j
  have hc := counts_scaled d.boundarySideCount hzero
  have h0 : T.angle 0 = d.tile.angle 0 := by rw [ha 0, hw 0]; rfl
  have hr := d.scaled_area_remainder_zero h0 30 (by decide) tileWeights hw
    (by intro l; fin_cases l <;> decide) pattern (d.boundarySideCount 0 0) hc
    root60Polynomial hP areaQuotient tileQuotient areaRemainder tileRemainder
    area_product tile_product (area_remainder_degree _ n)
  exact d.positive.ne' (area_count_zero _ n hr)

end Tiling
end Erdos633b
