import ErdosProblems.Erdos633b.BoundaryPolynomialRemainders
import ErdosProblems.Erdos633b.FinitePrimitiveAnnihilators


/-! Exact geometric boundary exclusion for finite angle pair 25.
Every polynomial identity, coefficient equation and row combination is checked by Lean. -/

namespace Erdos633b
namespace FiniteBoundary25
open Polynomial

def tileWeights : Fin 3 → ℕ := ![3, 4, 11]

def outerWeights : Fin 3 → ℕ := ![4, 6, 8]

noncomputable def quotients00 : ℚ[X] :=
  X ^ 53 + X ^ 47 - X ^ 35 - X ^ 29 - X ^ 25 - X ^ 23 - X ^ 19 + X ^ 11 + X ^ 7 + X ^ 5 + X

noncomputable def quotients01 : ℚ[X] :=
  X ^ 51 + X ^ 45 - X ^ 33 - 2 * X ^ 27 - 2 * X ^ 21 + 2 * X ^ 9 + 2 * X ^ 3

noncomputable def quotients02 : ℚ[X] :=
  X ^ 49 + X ^ 43 - X ^ 31 - X ^ 29 - X ^ 25 - X ^ 23 - X ^ 19 + X ^ 11 + X ^ 7 + X ^ 5 + X

noncomputable def quotients10 : ℚ[X] :=
  X ^ 52 + X ^ 46 - X ^ 34 - X ^ 28 - 2 * X ^ 24 - 2 * X ^ 18 + X ^ 16 + X ^ 10 + 2 * X ^ 6 + 2

noncomputable def quotients11 : ℚ[X] :=
  X ^ 50 + X ^ 44 - X ^ 32 - 2 * X ^ 26 - X ^ 22 - X ^ 20 - X ^ 16 + X ^ 14 + 2 * X ^ 8 + X ^ 4 +
    X ^ 2

noncomputable def quotients12 : ℚ[X] :=
  X ^ 48 + X ^ 42 - X ^ 30 - X ^ 28 - X ^ 24 - X ^ 22 - X ^ 20 - X ^ 14 + X ^ 12 + X ^ 10 + X ^ 6
    + X ^ 4 + X ^ 2 + 1

noncomputable def quotients20 : ℚ[X] :=
  X ^ 45 + X ^ 39 - X ^ 31 - X ^ 27 - X ^ 25 - X ^ 21 - X ^ 17 + X ^ 13 - X ^ 11 + X ^ 9 + X ^ 7 +
    2 * X ^ 3

noncomputable def quotients21 : ℚ[X] :=
  X ^ 43 + X ^ 37 - X ^ 29 - X ^ 25 - X ^ 23 - 2 * X ^ 19 - X ^ 13 + X ^ 11 + X ^ 7 + 2 * X ^ 5 +
    2 * X

noncomputable def quotients22 : ℚ[X] :=
  X ^ 41 + X ^ 35 - X ^ 27 - X ^ 23 - 2 * X ^ 21 - X ^ 17 - X ^ 15 + X ^ 9 + X ^ 7 + X ^ 5 + 2 * X
    ^ 3 + X

noncomputable def quotients (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then quotients00 else if j = 1 then quotients01 else quotients02
  else if i = 1 then if j = 0 then quotients10 else if j = 1 then quotients11 else quotients12
  else if j = 0 then quotients20 else if j = 1 then quotients21 else quotients22

noncomputable def remainders00 : ℚ[X] :=
  X ^ 7 - X ^ 5 - X

noncomputable def remainders01 : ℚ[X] :=
  X ^ 9 - 2 * X ^ 3

noncomputable def remainders02 : ℚ[X] :=
  X ^ 11 - X ^ 5 - X

noncomputable def remainders10 : ℚ[X] :=
  -X ^ 10 + X ^ 8 - 2

noncomputable def remainders11 : ℚ[X] :=
  2 * X ^ 10 - X ^ 8 - X ^ 4 - X ^ 2

noncomputable def remainders12 : ℚ[X] :=
  X ^ 8 - X ^ 4 - X ^ 2 - 1

noncomputable def remainders20 : ℚ[X] :=
  X ^ 11 + X ^ 9 - X ^ 7 - 2 * X ^ 3

noncomputable def remainders21 : ℚ[X] :=
  X ^ 11 + X ^ 7 - 2 * X ^ 5 - 2 * X

noncomputable def remainders22 : ℚ[X] :=
  X ^ 11 + X ^ 9 - X ^ 5 - 2 * X ^ 3 - X

noncomputable def remainders (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then remainders00 else if j = 1 then remainders01 else remainders02
  else if i = 1 then if j = 0 then remainders10 else if j = 1 then remainders11 else remainders12
  else if j = 0 then remainders20 else if j = 1 then remainders21 else remainders22

theorem product_0_0 : rootSinePoly 36 3 * rootSinePoly 36 4 =
    root36Polynomial * quotients 0 0 + remainders 0 0 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients00, remainders00]
  ring

theorem product_0_1 : rootSinePoly 36 3 * rootSinePoly 36 6 =
    root36Polynomial * quotients 0 1 + remainders 0 1 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients01, remainders01]
  ring

theorem product_0_2 : rootSinePoly 36 3 * rootSinePoly 36 8 =
    root36Polynomial * quotients 0 2 + remainders 0 2 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients02, remainders02]
  ring

theorem product_1_0 : rootSinePoly 36 4 * rootSinePoly 36 4 =
    root36Polynomial * quotients 1 0 + remainders 1 0 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients10, remainders10]
  ring

theorem product_1_1 : rootSinePoly 36 4 * rootSinePoly 36 6 =
    root36Polynomial * quotients 1 1 + remainders 1 1 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients11, remainders11]
  ring

theorem product_1_2 : rootSinePoly 36 4 * rootSinePoly 36 8 =
    root36Polynomial * quotients 1 2 + remainders 1 2 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients12, remainders12]
  ring

theorem product_2_0 : rootSinePoly 36 11 * rootSinePoly 36 4 =
    root36Polynomial * quotients 2 0 + remainders 2 0 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients20, remainders20]
  ring

theorem product_2_1 : rootSinePoly 36 11 * rootSinePoly 36 6 =
    root36Polynomial * quotients 2 1 + remainders 2 1 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients21, remainders21]
  ring

theorem product_2_2 : rootSinePoly 36 11 * rootSinePoly 36 8 =
    root36Polynomial * quotients 2 2 + remainders 2 2 := by
  dsimp [rootSinePoly, root36Polynomial, quotients, remainders, quotients22, remainders22]
  ring

theorem products (i j : Fin 3) :
    rootSinePoly 36 (tileWeights i) * rootSinePoly 36 (outerWeights j) =
      root36Polynomial * quotients i j + remainders i j := by
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

theorem remainder_degree_0_0 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 0 0).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_0_1 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 0 1).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_0_2 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 0 2).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_1_0 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 1 0).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_1_1 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 1 1).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_1_2 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 1 2).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_2_0 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 2 0).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_2_1 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 2 1).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree_2_2 (m : Fin 3 → Fin 3 → ℕ) :
    (boundaryRemainderPoly m remainders 2 2).natDegree < 12 := by
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  dsimp [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
    remainders12, remainders20, remainders21, remainders22]
  compute_degree
  norm_num

theorem remainder_degree (m : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) :
    (boundaryRemainderPoly m remainders i j).natDegree < 12 := by
  fin_cases i <;> fin_cases j
  · exact remainder_degree_0_0 m
  · exact remainder_degree_0_1 m
  · exact remainder_degree_0_2 m
  · exact remainder_degree_1_0 m
  · exact remainder_degree_1_1 m
  · exact remainder_degree_1_2 m
  · exact remainder_degree_2_0 m
  · exact remainder_degree_2_1 m
  · exact remainder_degree_2_2 m

theorem coefficient_1 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-2 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 1 0 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_2 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-1 : ℚ) * (m 0 1 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 2 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]

theorem coefficient_3 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (-2 : ℚ) * (m 0 0 : ℚ) + (2 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 3 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_4 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 1 = 0) :
    (1 : ℚ) * (m 0 2 : ℚ) + (-1 : ℚ) * (m 1 0 : ℚ) + (1 : ℚ) * (m 1 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 1 h 7 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_6 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-1 : ℚ) * (m 0 0 : ℚ) + (-1 : ℚ) * (m 0 2 : ℚ) + (1 : ℚ) * (m 2 0 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 1 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]

theorem coefficient_7 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-2 : ℚ) * (m 0 2 : ℚ) + (2 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 3 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem coefficient_8 (m : Fin 3 → Fin 3 → ℕ)
    (h : boundaryRemainderPoly m remainders 0 2 = 0) :
    (-1 : ℚ) * (m 2 0 : ℚ) + (1 : ℚ) * (m 2 2 : ℚ) = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  convert boundary_remainder_coefficients m remainders 0 2 h 7 using 1
  norm_num [remainders, remainders00, remainders01, remainders02, remainders10, remainders11,
      remainders12, remainders20, remainders21, remainders22, Fin.sum_univ_three, h20, h21,
      coeff_X, coeff_one, -map_add, -map_mul, -map_sub]
  ring

theorem first_row_zero (m : Fin 3 → Fin 3 → ℕ)
    (hz : ∀ i j, boundaryRemainderPoly m remainders i j = 0) :
    m 0 0 + m 0 1 + m 0 2 = 0 := by
  have h1 := coefficient_1 m (hz 0 1)
  have h2 := coefficient_2 m (hz 0 1)
  have h3 := coefficient_3 m (hz 0 1)
  have h4 := coefficient_4 m (hz 0 1)
  have h6 := coefficient_6 m (hz 0 2)
  have h7 := coefficient_7 m (hz 0 2)
  have h8 := coefficient_8 m (hz 0 2)
  have hh : (1 : ℚ) * (m 0 0 : ℚ) + (1 : ℚ) * (m 0 1 : ℚ) + (1 : ℚ) * (m 0 2 : ℚ) = 0 := by
    linear_combination (-1) * h1 + (-1) * h2 + (1/2) * h3 + (-1) * h4 + (-2) * h6 + (1) * h7 +
      (-2) * h8
  have hhN : 1 * m 0 0 + 1 * m 0 1 + 1 * m 0 2 = 0 := by exact_mod_cast hh
  omega

end FiniteBoundary25
namespace Tiling
open FiniteBoundary25

theorem finite_boundary_25_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (tileWeights i : ℝ) * (Real.pi / 18))
    (ha : ∀ i, T.angle i = (outerWeights i : ℝ) * (Real.pi / 18)) : False := by
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / 18 : ℝ) : ℂ) * Complex.I)) 36 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceMul, one_mul] using
      primitive_pi_root 18 1 (by decide) (by decide)
  have hP := root36Polynomial_vanishes _ hz
  have hzero (i j : Fin 3) : boundaryRemainderPoly d.boundarySideCount remainders i j = 0 := by
    apply d.boundary_polynomial_remainder_zero 18 (by decide) tileWeights outerWeights hw ha
      (by intro l; fin_cases l <;> decide) (by intro l; fin_cases l <;> decide)
      root36Polynomial hP quotients remainders products i j
    exact remainder_degree d.boundarySideCount i j
  have hrow := first_row_zero d.boundarySideCount hzero
  obtain ⟨j, hj⟩ := d.boundary_row_positive 0
  have hh : d.boundarySideCount 0 j ≤ ∑ k, d.boundarySideCount 0 k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [Fin.sum_univ_three, hrow] at hh
  omega

end Tiling
end Erdos633b
