import ErdosProblems.Erdos633b.BoundaryPolynomialRemainders
import ErdosProblems.Erdos633b.ScaledAreaRemainders
import ErdosProblems.Erdos633b.PrimitiveFinitePolynomials

/-! Explicit finite geometric exclusion for group-2 shape 1, phase (15,2).
Every polynomial identity, coefficient equation and row combination is checked by Lean. -/

namespace Erdos633b
namespace FiniteFirstOrder15
open Polynomial

def tileWeights : Fin 3 → ℕ := ![4, 1, 10]

def outerWeights : Fin 3 → ℕ := ![4, 8, 3]

noncomputable def quotients00 : ℚ[X] :=
  X ^ 44 - X ^ 43 + X ^ 42 + X ^ 39 - X ^ 38 + X ^ 37 - X ^ 29 + X ^ 28 - X ^ 27 - X ^ 24 + X ^ 23
    - 3 * X ^ 22 + 2 * X ^ 21 - 2 * X ^ 20 - 2 * X ^ 17 + 2 * X ^ 16 - 2 * X ^ 15 + X ^ 14 - X ^
    13 + X ^ 12 + X ^ 9 - X ^ 8 + 3 * X ^ 7 - 2 * X ^ 6 + 2 * X ^ 5 + 2 * X ^ 2 - 2 * X + 3

noncomputable def quotients01 : ℚ[X] :=
  X ^ 40 - X ^ 39 + X ^ 38 + X ^ 35 - X ^ 34 + X ^ 33 - X ^ 26 - X ^ 23 - X ^ 21 - 2 * X ^ 18 + X
    ^ 17 - X ^ 16 - X ^ 13 + X ^ 12 + X ^ 8 + X ^ 6 + X ^ 4 + X ^ 3 + X

noncomputable def quotients02 : ℚ[X] :=
  X ^ 45 - X ^ 44 + X ^ 43 + X ^ 40 - X ^ 39 + X ^ 38 - X ^ 30 + X ^ 29 - X ^ 28 - X ^ 25 + X ^ 24
    - 2 * X ^ 23 + X ^ 22 - 2 * X ^ 21 + X ^ 20 - X ^ 19 - X ^ 18 + X ^ 17 - 2 * X ^ 16 + 2 * X ^
    15 - 2 * X ^ 14 + X ^ 13 + X ^ 10 - X ^ 9 + 2 * X ^ 8 - X ^ 7 + 2 * X ^ 6 - X ^ 5 + X ^ 4 + X
    ^ 3 - X ^ 2 + 2 * X - 2

noncomputable def quotients10 : ℚ[X] :=
  X ^ 47 - X ^ 46 + X ^ 45 + X ^ 42 - X ^ 41 + X ^ 40 - X ^ 32 + X ^ 31 - X ^ 30 - X ^ 27 + X ^ 26
    - 2 * X ^ 25 + X ^ 24 - X ^ 23 - X ^ 20 - X ^ 16 + X ^ 15 - X ^ 14 + X ^ 13 - X ^ 11 + 2 * X ^
    10 - X ^ 9 + X ^ 8 + X ^ 5 + X - 1

noncomputable def quotients11 : ℚ[X] :=
  X ^ 43 - X ^ 42 + X ^ 41 + X ^ 38 - X ^ 37 + X ^ 36 - X ^ 29 - X ^ 26 - X ^ 24 - X ^ 21 - X ^ 15
    + 2 * X ^ 14 - X ^ 13 + X ^ 11 - X ^ 10 + 2 * X ^ 9 - X ^ 8 + X ^ 6 + X

noncomputable def quotients12 : ℚ[X] :=
  X ^ 48 - X ^ 47 + X ^ 46 + X ^ 43 - X ^ 42 + X ^ 41 - X ^ 33 + X ^ 32 - X ^ 31 - X ^ 28 + X ^ 27
    - X ^ 26 - X ^ 24 + X ^ 23 - X ^ 22 - X ^ 20 + X ^ 18 - 2 * X ^ 17 + X ^ 16 - X ^ 15 + X ^ 14
    - X ^ 12 + X ^ 11 + X ^ 9 - X ^ 8 + X ^ 7 + X ^ 5 - X ^ 3 + 2 * X ^ 2 - X + 1

noncomputable def quotients20 : ℚ[X] :=
  X ^ 38 - X ^ 37 + X ^ 36 + X ^ 33 - X ^ 32 + X ^ 31 - X ^ 28 + X ^ 27 - X ^ 26 - 2 * X ^ 23 + 2
    * X ^ 22 - 2 * X ^ 21 - X ^ 18 + X ^ 17 - 2 * X ^ 16 + X ^ 15 - X ^ 14 + X ^ 13 - X ^ 12 + X ^
    10 - X ^ 9 + 2 * X ^ 8 - 2 * X ^ 7 + 3 * X ^ 6 - X ^ 5 + X ^ 4 + X ^ 3 - X ^ 2 + 3 * X - 2

noncomputable def quotients21 : ℚ[X] :=
  X ^ 34 - X ^ 33 + X ^ 32 + X ^ 29 - X ^ 28 + X ^ 27 - X ^ 24 + X ^ 23 - X ^ 22 - X ^ 20 - X ^ 19
    + X ^ 18 - 2 * X ^ 17 - X ^ 15 - X ^ 12 + X ^ 10 + X ^ 7 + 2 * X ^ 5 + 2 * X ^ 2 + 1

noncomputable def quotients22 : ℚ[X] :=
  X ^ 39 - X ^ 38 + X ^ 37 + X ^ 34 - X ^ 33 + X ^ 32 - X ^ 29 + X ^ 28 - X ^ 27 - 2 * X ^ 24 + 2
    * X ^ 23 - 2 * X ^ 22 - X ^ 19 + X ^ 18 - X ^ 17 - X ^ 15 + 2 * X ^ 14 - 2 * X ^ 13 + X ^ 12 -
    X ^ 10 + 3 * X ^ 9 - 3 * X ^ 8 + 2 * X ^ 7 + X ^ 5 + X ^ 2 + 2

noncomputable def quotients (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then quotients00 else if j = 1 then quotients01 else quotients02
  else if i = 1 then if j = 0 then quotients10 else if j = 1 then quotients11 else quotients12
  else if j = 0 then quotients20 else if j = 1 then quotients21 else quotients22

noncomputable def remainders00 : ℚ[X] :=
  -2 * X ^ 7 + X ^ 5 + X ^ 4 + X ^ 3 - X - 3

noncomputable def remainders01 : ℚ[X] :=
  X ^ 7 + X ^ 6 - X ^ 4 - X ^ 3 - X ^ 2 - X

noncomputable def remainders02 : ℚ[X] :=
  3 * X ^ 7 + X ^ 6 - X ^ 5 - 2 * X ^ 4 - 2 * X ^ 3 - X ^ 2 + 2

noncomputable def remainders10 : ℚ[X] :=
  X ^ 7 - X ^ 3 - X ^ 2 + 1

noncomputable def remainders11 : ℚ[X] :=
  -X ^ 7 + X ^ 5 + X ^ 4 - X ^ 2 - X

noncomputable def remainders12 : ℚ[X] :=
  -X ^ 7 - X ^ 6 + X ^ 5 + 2 * X ^ 4 - X ^ 2 - 1

noncomputable def remainders20 : ℚ[X] :=
  2 * X ^ 7 + X ^ 6 - X ^ 4 - 2 * X ^ 3 - 2 * X ^ 2 - X + 2

noncomputable def remainders21 : ℚ[X] :=
  X ^ 5 + X ^ 4 - X ^ 3 - 2 * X ^ 2 - X - 1

noncomputable def remainders22 : ℚ[X] :=
  -3 * X ^ 7 + 2 * X ^ 5 + 2 * X ^ 4 + X ^ 3 - X ^ 2 - 2 * X - 2

noncomputable def remainders (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then remainders00 else if j = 1 then remainders01 else remainders02
  else if i = 1 then if j = 0 then remainders10 else if j = 1 then remainders11 else remainders12
  else if j = 0 then remainders20 else if j = 1 then remainders21 else remainders22

theorem product_0_0 : rootSinePoly 30 4 * rootSinePoly 30 4 =
    root30Polynomial * quotients 0 0 + remainders 0 0 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients00, remainders00]
  ring

theorem product_0_1 : rootSinePoly 30 4 * rootSinePoly 30 8 =
    root30Polynomial * quotients 0 1 + remainders 0 1 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients01, remainders01]
  ring

theorem product_0_2 : rootSinePoly 30 4 * rootSinePoly 30 3 =
    root30Polynomial * quotients 0 2 + remainders 0 2 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients02, remainders02]
  ring

theorem product_1_0 : rootSinePoly 30 1 * rootSinePoly 30 4 =
    root30Polynomial * quotients 1 0 + remainders 1 0 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients10, remainders10]
  ring

theorem product_1_1 : rootSinePoly 30 1 * rootSinePoly 30 8 =
    root30Polynomial * quotients 1 1 + remainders 1 1 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients11, remainders11]
  ring

theorem product_1_2 : rootSinePoly 30 1 * rootSinePoly 30 3 =
    root30Polynomial * quotients 1 2 + remainders 1 2 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients12, remainders12]
  ring

theorem product_2_0 : rootSinePoly 30 10 * rootSinePoly 30 4 =
    root30Polynomial * quotients 2 0 + remainders 2 0 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients20, remainders20]
  ring

theorem product_2_1 : rootSinePoly 30 10 * rootSinePoly 30 8 =
    root30Polynomial * quotients 2 1 + remainders 2 1 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients21, remainders21]
  ring

theorem product_2_2 : rootSinePoly 30 10 * rootSinePoly 30 3 =
    root30Polynomial * quotients 2 2 + remainders 2 2 := by
  dsimp [rootSinePoly, root30Polynomial, quotients, remainders, quotients22, remainders22]
  ring

theorem products (i j : Fin 3) :
    rootSinePoly 30 (tileWeights i) * rootSinePoly 30 (outerWeights j) =
      root30Polynomial * quotients i j + remainders i j := by
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
    (boundaryRemainderPoly m remainders i j).natDegree < 8 := by
  fin_cases i <;> fin_cases j <;>
    simp only [boundaryRemainderPoly, Fin.sum_univ_three] <;>
    dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22] <;> compute_degree <;> norm_num

theorem coefficient_0 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-1 : ℚ) * (m 0 2 : ℚ) + (3 : ℚ) * (m 1 0 : ℚ) + (-1 : ℚ) * (m 1 1 : ℚ) + (-2 : ℚ) * (m 1 2 :
      ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 0 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_1 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 1 : ℚ) + (-1 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 1 0 :
      ℚ) + (1 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_2 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 1 : ℚ) + (-2 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 1 1 :
      ℚ) + (2 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 2 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_3 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 2 : ℚ) + (-1 : ℚ) * (m 1 0 : ℚ) + (1 : ℚ) * (m 1 1 :
      ℚ) + (2 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 3 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_4 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (2 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 1 : ℚ) + (-2 : ℚ) * (m 0 2 : ℚ) + (3 : ℚ) * (m 2 0 :
      ℚ) + (-1 : ℚ) * (m 2 1 : ℚ) + (-2 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 0 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_5 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-2 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 2 0 : ℚ) + (1 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_6 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 1 : ℚ) + (-1 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 2 1 :
      ℚ) + (2 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 2 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_7 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-2 : ℚ) * (m 0 0 : ℚ) + (1 : ℚ) * (m 0 2 : ℚ) + (-1 : ℚ) * (m 2 0 : ℚ) + (1 : ℚ) * (m 2 1 :
      ℚ) + (2 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 3 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

noncomputable def pattern (i j : Fin 3) : ℕ :=
  if i = 0 then if j = 0 then 2 else if j = 1 then 1 else 1
  else if i = 1 then if j = 0 then 2 else if j = 1 then 1 else 2
  else if j = 0 then 1 else if j = 1 then 2 else 1

theorem counts_scaled (m : Fin 3 → Fin 3 → ℕ)
    (hz : ∀ i j, boundaryRemainderPoly m remainders i j = 0) :
    ∀ i j, m i j = pattern i j * m 0 1 := by
  have h0 := coefficient_0 m (hz 0 1)
  have h1 := coefficient_1 m (hz 0 1)
  have h2 := coefficient_2 m (hz 0 1)
  have h3 := coefficient_3 m (hz 0 1)
  have h4 := coefficient_4 m (hz 0 2)
  have h5 := coefficient_5 m (hz 0 2)
  have h6 := coefficient_6 m (hz 0 2)
  have h7 := coefficient_7 m (hz 0 2)
  intro i j
  fin_cases i <;> fin_cases j
  · change m 0 0 = 2 * m 0 1
    have hh : (m 0 0 : ℚ) - (2 : ℚ) * m 0 1 = 0 := by
      linear_combination (-1) * h0 + (2) * h2 + (-3) * h3
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 0 1 = 1 * m 0 1
    omega
  · change m 0 2 = 1 * m 0 1
    have hh : (m 0 2 : ℚ) - (1 : ℚ) * m 0 1 = 0 := by
      linear_combination (-2/3) * h0 + (4/3) * h2 + (-2) * h3 + (1/3) * h4 + (-2/3) * h6 + (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 0 = 2 * m 0 1
    have hh : (m 1 0 : ℚ) - (2 : ℚ) * m 0 1 = 0 := by
      linear_combination (-2/3) * h0 + (7/3) * h2 + (-3) * h3 + (1/3) * h4 + (-2/3) * h6 + (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 1 = 1 * m 0 1
    have hh : (m 1 1 : ℚ) - (1 : ℚ) * m 0 1 = 0 := by
      linear_combination (-1/3) * h0 + (-2) * h1 + (11/3) * h2 + (-3) * h3 + (2/3) * h4 + (-4/3) *
        h6 + (2) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 1 2 = 2 * m 0 1
    have hh : (m 1 2 : ℚ) - (2 : ℚ) * m 0 1 = 0 := by
      linear_combination (-1) * h0 + (1) * h1 + (1) * h2 + (-2) * h3
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 0 = 1 * m 0 1
    have hh : (m 2 0 : ℚ) - (1 : ℚ) * m 0 1 = 0 := by
      linear_combination (-1/3) * h0 + (2/3) * h2 + (-1) * h3 + (2/3) * h4 + (-1/3) * h6 + (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 1 = 2 * m 0 1
    have hh : (m 2 1 : ℚ) - (2 : ℚ) * m 0 1 = 0 := by
      linear_combination (1/3) * h0 + (-2/3) * h2 + (1) * h3 + (1/3) * h4 + (-2) * h5 + (7/3) * h6
        + (-1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)
  · change m 2 2 = 1 * m 0 1
    have hh : (m 2 2 : ℚ) - (1 : ℚ) * m 0 1 = 0 := by
      linear_combination (-1) * h0 + (2) * h2 + (-3) * h3 + (1) * h5 + (-1) * h6 + (1) * h7
    exact_mod_cast (sub_eq_zero.mp hh)

noncomputable def areaQuotient : ℚ[X] :=
  2 * X ^ 50 - 2 * X ^ 49 + 2 * X ^ 48 + 5 * X ^ 47 - 5 * X ^ 46 + 7 * X ^ 45 + 7 * X ^ 42 + 7 * X
    ^ 39 + 2 * X ^ 38 - 2 * X ^ 37 + 9 * X ^ 36 - 7 * X ^ 35 + 7 * X ^ 34 + 2 * X ^ 33 - 7 * X ^
    32 + 2 * X ^ 31 - 5 * X ^ 29 - 4 * X ^ 28 - X ^ 27 - 11 * X ^ 26 + 2 * X ^ 25 - 7 * X ^ 24 -
    11 * X ^ 23 - 6 * X ^ 22 - X ^ 21 - 10 * X ^ 20 - 7 * X ^ 19 - 2 * X ^ 18 - 10 * X ^ 17 + 6 *
    X ^ 16 - 8 * X ^ 15 - 4 * X ^ 14 + 4 * X ^ 13 + 3 * X ^ 12 + 4 * X ^ 10 + 3 * X ^ 9 + 6 * X ^
    8 + 13 * X ^ 7 - 2 * X ^ 6 + 8 * X ^ 5 + 11 * X ^ 4 + 7 * X ^ 3 + 5 * X ^ 2 + 3 * X + 6


noncomputable def areaRemainder : ℚ[X] :=
  6 * X ^ 7 + 9 * X ^ 6 - 9 * X ^ 4 - 6 * X ^ 3 - 6 * X ^ 2 - 9 * X - 6


noncomputable def tileQuotient : ℚ[X] :=
  X ^ 41 - X ^ 40 + X ^ 39 + X ^ 36 - X ^ 35 + X ^ 34 - X ^ 31 + X ^ 30 - X ^ 29 - 2 * X ^ 26 + 2
    * X ^ 25 - 2 * X ^ 24 - X ^ 21 + X ^ 20 - X ^ 19 + X ^ 16 - X ^ 15 + X ^ 14 - X ^ 13 + X ^ 12
    + X ^ 11 - 2 * X ^ 10 + 2 * X ^ 9 - X ^ 8 + X ^ 7 - X ^ 5 + X ^ 4 + X ^ 3 - X ^ 2 + 1


noncomputable def tileRemainder : ℚ[X] :=
  -X ^ 7 + X ^ 6 - X ^ 4 + X ^ 3 + X ^ 2 - X - 1

theorem area_product : rootAreaBasePoly 30 tileWeights pattern =
    root30Polynomial * areaQuotient + areaRemainder := by
  simp only [rootAreaBasePoly, rootBoundaryPoly, Fin.sum_univ_three]
  dsimp [tileWeights, pattern, rootSinePoly, root30Polynomial, areaQuotient, areaRemainder]
  simp only [map_one, C_ofNat]
  ring

theorem tile_product : rootTileAreaPoly 30 tileWeights =
    root30Polynomial * tileQuotient + tileRemainder := by
  dsimp [rootTileAreaPoly, tileWeights, rootSinePoly, root30Polynomial, tileQuotient,
    tileRemainder]
  ring

theorem area_remainder_degree (r n : ℕ) :
    (scaledAreaRemainder r n areaRemainder tileRemainder).natDegree < 8 := by
  dsimp [scaledAreaRemainder, areaRemainder, tileRemainder]
  compute_degree
  norm_num

theorem area_count_zero (r n : ℕ)
    (hz : scaledAreaRemainder r n areaRemainder tileRemainder = 0) : n = 0 := by
  have h0 := scaledAreaRemainder_coefficients r n areaRemainder tileRemainder hz 0
  norm_num [areaRemainder, tileRemainder, coeff_X, coeff_one,
    -map_add, -map_mul, -map_sub] at h0
  have h1 := scaledAreaRemainder_coefficients r n areaRemainder tileRemainder hz 1
  norm_num [areaRemainder, tileRemainder, coeff_X, coeff_one,
    -map_add, -map_mul, -map_sub] at h1
  have hn : (n : ℚ) = 0 := by linarith
  exact_mod_cast hn

end FiniteFirstOrder15
namespace Tiling
open FiniteFirstOrder15

theorem groupTwo_finite_15_2_1_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (tileWeights i : ℝ) * (Real.pi / 15))
    (ha : ∀ i, T.angle i = (outerWeights i : ℝ) * (Real.pi / 15)) : False := by
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / 15 : ℝ) : ℂ) * Complex.I)) 30 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceMul, one_mul] using
      primitive_pi_root 15 1 (by decide) (by decide)
  have hP := root30Polynomial_vanishes _ hz
  have hzero (i j : Fin 3) : boundaryRemainderPoly d.boundarySideCount remainders i j = 0 := by
    apply d.boundary_polynomial_remainder_zero 15 (by decide) tileWeights outerWeights hw ha
      (by intro l; fin_cases l <;> decide) (by intro l; fin_cases l <;> decide)
      root30Polynomial hP quotients remainders products i j
    exact remainder_degree d.boundarySideCount i j
  have hc := counts_scaled d.boundarySideCount hzero
  have h0 : T.angle 0 = d.tile.angle 0 := by rw [ha 0, hw 0]; rfl
  have hr := d.scaled_area_remainder_zero h0 15 (by decide) tileWeights hw
    (by intro l; fin_cases l <;> decide) pattern (d.boundarySideCount 0 1) hc
    root30Polynomial hP areaQuotient tileQuotient areaRemainder tileRemainder
    area_product tile_product (area_remainder_degree _ n)
  exact d.positive.ne' (area_count_zero _ n hr)

end Tiling
end Erdos633b
