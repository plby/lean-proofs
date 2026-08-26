import ErdosProblems.Erdos633b.BoundaryPolynomialRemainders

/-! A fully explicit finite boundary exclusion: tile angles (3,5,16)π/24
cannot tile an outer triangle with angles (3,10,11)π/24. -/

namespace Erdos633b
open Polynomial

noncomputable def root48Polynomial : ℚ[X] := X ^ 16 - X ^ 8 + 1

theorem root48Polynomial_vanishes (z : ℂ) (hz : IsPrimitiveRoot z 48) :
    aeval z root48Polynomial = 0 := by
  have h24 : z ^ 24 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have h16 : z ^ 16 - 1 ≠ 0 := sub_ne_zero.mpr
    (hz.pow_ne_one_of_pos_of_lt (by decide) (by decide))
  have he : (z ^ 48 - 1) * (z ^ 8 - 1) =
      (z ^ 16 - z ^ 8 + 1) * ((z ^ 24 - 1) * (z ^ 16 - 1)) := by ring
  rw [hz.pow_eq_one, sub_self, zero_mul] at he
  have hh := (mul_eq_zero.mp he.symm).resolve_right (mul_ne_zero h24 h16)
  simpa only [root48Polynomial, map_add, map_sub, map_pow, aeval_X, map_one] using hh

def boundary48TileWeights : Fin 3 → ℕ := ![3, 5, 16]

def boundary48OuterWeights : Fin 3 → ℕ := ![3, 10, 11]

noncomputable def boundary48Quotients00 : ℚ[X] :=
  X ^ 74 + X ^ 66 - X ^ 50 - X ^ 42 - 2 * X ^ 32 + X ^ 26 - 2 * X ^ 24 + X ^ 18 + 2 * X ^ 8 - X ^
    2 + 2

noncomputable def boundary48Quotients01 : ℚ[X] :=
  X ^ 67 + X ^ 59 - X ^ 43 - X ^ 39 - X ^ 35 - X ^ 31 - X ^ 25 + X ^ 19 - X ^ 17 + X ^ 15 + X ^
    11 + X ^ 7 + X

noncomputable def boundary48Quotients02 : ℚ[X] :=
  X ^ 66 + X ^ 58 - X ^ 42 - X ^ 40 - X ^ 34 - X ^ 32 - X ^ 24 + X ^ 18 + X ^ 10 + X ^ 8 + 1

noncomputable def boundary48Quotients10 : ℚ[X] :=
  X ^ 72 + X ^ 64 - X ^ 48 - X ^ 40 - X ^ 34 - X ^ 30 - X ^ 26 + X ^ 24 - X ^ 22 + X ^ 16 + X ^
    10 + X ^ 6 + X ^ 2 - 1

noncomputable def boundary48Quotients11 : ℚ[X] :=
  X ^ 65 + X ^ 57 - X ^ 41 - X ^ 37 - X ^ 33 - X ^ 29 - X ^ 27 - X ^ 19 + X ^ 17 + X ^ 13 + X ^ 9
    + X ^ 5 + X ^ 3

noncomputable def boundary48Quotients12 : ℚ[X] :=
  X ^ 64 + X ^ 56 - X ^ 40 - X ^ 38 - X ^ 32 - X ^ 30 - X ^ 26 - X ^ 18 + X ^ 16 + X ^ 14 + X ^ 8
    + X ^ 6 + X ^ 2 + 1

noncomputable def boundary48Quotients20 : ℚ[X] :=
  X ^ 61 + X ^ 53 - X ^ 45 - 2 * X ^ 37 - X ^ 29 + X ^ 21 - X ^ 19 + 2 * X ^ 13 - X ^ 11 + X ^ 5
    + X ^ 3

noncomputable def boundary48Quotients21 : ℚ[X] :=
  X ^ 54 + X ^ 46 - X ^ 38 - 2 * X ^ 30 - X ^ 26 - X ^ 22 - X ^ 18 + X ^ 14 + X ^ 10 + 2 * X ^ 6
    + 2 * X ^ 2

noncomputable def boundary48Quotients22 : ℚ[X] :=
  X ^ 53 + X ^ 45 - X ^ 37 - 2 * X ^ 29 - X ^ 27 - X ^ 21 - X ^ 19 + X ^ 13 + X ^ 11 + 2 * X ^ 5
    + 2 * X ^ 3

noncomputable def boundary48Quotients (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then boundary48Quotients00 else if j = 1 then boundary48Quotients01 else
    boundary48Quotients02
  else if i = 1 then if j = 0 then boundary48Quotients10 else if j = 1 then boundary48Quotients11
    else boundary48Quotients12
  else if j = 0 then boundary48Quotients20 else if j = 1 then boundary48Quotients21 else
    boundary48Quotients22

noncomputable def boundary48Remainders00 : ℚ[X] :=
  -X ^ 10 + X ^ 6 + X ^ 2 - 2

noncomputable def boundary48Remainders01 : ℚ[X] :=
  X ^ 13 - X ^ 11 + X ^ 9 - X ^ 7 - X

noncomputable def boundary48Remainders02 : ℚ[X] :=
  X ^ 14 - X ^ 10 - 1

noncomputable def boundary48Remainders10 : ℚ[X] :=
  X ^ 14 - X ^ 6 - X ^ 2 + 1

noncomputable def boundary48Remainders11 : ℚ[X] :=
  X ^ 15 + X ^ 11 - X ^ 9 - X ^ 5 - X ^ 3

noncomputable def boundary48Remainders12 : ℚ[X] :=
  X ^ 10 - X ^ 6 - X ^ 2 - 1

noncomputable def boundary48Remainders20 : ℚ[X] :=
  -X ^ 13 + 2 * X ^ 11 - X ^ 5 - X ^ 3

noncomputable def boundary48Remainders21 : ℚ[X] :=
  X ^ 14 + X ^ 10 - 2 * X ^ 6 - 2 * X ^ 2

noncomputable def boundary48Remainders22 : ℚ[X] :=
  X ^ 13 + X ^ 11 - 2 * X ^ 5 - 2 * X ^ 3

noncomputable def boundary48Remainders (i j : Fin 3) : ℚ[X] :=
  if i = 0 then if j = 0 then boundary48Remainders00 else if j = 1 then boundary48Remainders01
    else boundary48Remainders02
  else if i = 1 then if j = 0 then boundary48Remainders10 else if j = 1 then
    boundary48Remainders11 else boundary48Remainders12
  else if j = 0 then boundary48Remainders20 else if j = 1 then boundary48Remainders21 else
    boundary48Remainders22

theorem boundary48_product_0_0 :
    rootSinePoly 48 3 * rootSinePoly 48 3 =
      root48Polynomial * boundary48Quotients 0 0 + boundary48Remainders 0 0 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients00, boundary48Remainders00]
  ring

theorem boundary48_product_0_1 :
    rootSinePoly 48 3 * rootSinePoly 48 10 =
      root48Polynomial * boundary48Quotients 0 1 + boundary48Remainders 0 1 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients01, boundary48Remainders01]
  ring

theorem boundary48_product_0_2 :
    rootSinePoly 48 3 * rootSinePoly 48 11 =
      root48Polynomial * boundary48Quotients 0 2 + boundary48Remainders 0 2 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients02, boundary48Remainders02]
  ring

theorem boundary48_product_1_0 :
    rootSinePoly 48 5 * rootSinePoly 48 3 =
      root48Polynomial * boundary48Quotients 1 0 + boundary48Remainders 1 0 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients10, boundary48Remainders10]
  ring

theorem boundary48_product_1_1 :
    rootSinePoly 48 5 * rootSinePoly 48 10 =
      root48Polynomial * boundary48Quotients 1 1 + boundary48Remainders 1 1 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients11, boundary48Remainders11]
  ring

theorem boundary48_product_1_2 :
    rootSinePoly 48 5 * rootSinePoly 48 11 =
      root48Polynomial * boundary48Quotients 1 2 + boundary48Remainders 1 2 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients12, boundary48Remainders12]
  ring

theorem boundary48_product_2_0 :
    rootSinePoly 48 16 * rootSinePoly 48 3 =
      root48Polynomial * boundary48Quotients 2 0 + boundary48Remainders 2 0 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients20, boundary48Remainders20]
  ring

theorem boundary48_product_2_1 :
    rootSinePoly 48 16 * rootSinePoly 48 10 =
      root48Polynomial * boundary48Quotients 2 1 + boundary48Remainders 2 1 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients21, boundary48Remainders21]
  ring

theorem boundary48_product_2_2 :
    rootSinePoly 48 16 * rootSinePoly 48 11 =
      root48Polynomial * boundary48Quotients 2 2 + boundary48Remainders 2 2 := by
  dsimp [rootSinePoly, root48Polynomial, boundary48Quotients, boundary48Remainders,
    boundary48Quotients22, boundary48Remainders22]
  ring

theorem boundary48_products (l t : Fin 3) :
    rootSinePoly 48 (boundary48TileWeights l) * rootSinePoly 48 (boundary48OuterWeights t) =
      root48Polynomial * boundary48Quotients l t + boundary48Remainders l t := by
  fin_cases l <;> fin_cases t
  · exact boundary48_product_0_0
  · exact boundary48_product_0_1
  · exact boundary48_product_0_2
  · exact boundary48_product_1_0
  · exact boundary48_product_1_1
  · exact boundary48_product_1_2
  · exact boundary48_product_2_0
  · exact boundary48_product_2_1
  · exact boundary48_product_2_2

theorem boundary48_degree (m : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) :
    (boundaryRemainderPoly m boundary48Remainders i j).natDegree < 16 := by
  fin_cases i <;> fin_cases j <;>
    simp only [boundaryRemainderPoly, Fin.sum_univ_three] <;>
    dsimp [boundary48Remainders, boundary48Remainders00, boundary48Remainders01,
      boundary48Remainders02,
      boundary48Remainders10, boundary48Remainders11, boundary48Remainders12,
      boundary48Remainders20, boundary48Remainders21, boundary48Remainders22] <;> compute_degree
        <;> norm_num

theorem boundary48_first_row_zero (m : Fin 3 → Fin 3 → ℕ)
    (hzero : ∀ i j, boundaryRemainderPoly m boundary48Remainders i j = 0) :
    m 0 0 + m 0 1 + m 0 2 = 0 := by
  have h20 : (2 : Fin 3) ≠ 0 := by decide
  have h21 : (2 : Fin 3) ≠ 1 := by decide
  have h1 := boundary_remainder_coefficients m boundary48Remainders 0 1
    (hzero 0 1) 1
  norm_num [boundary48Remainders, boundary48Remainders00, boundary48Remainders01,
    boundary48Remainders02,
      boundary48Remainders10, boundary48Remainders11, boundary48Remainders12,
      boundary48Remainders20, boundary48Remainders21, boundary48Remainders22, Fin.sum_univ_three,
        h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h1
  have h4 := boundary_remainder_coefficients m boundary48Remainders 0 1
    (hzero 0 1) 9
  norm_num [boundary48Remainders, boundary48Remainders00, boundary48Remainders01,
    boundary48Remainders02,
      boundary48Remainders10, boundary48Remainders11, boundary48Remainders12,
      boundary48Remainders20, boundary48Remainders21, boundary48Remainders22, Fin.sum_univ_three,
        h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h4
  have h5 := boundary_remainder_coefficients m boundary48Remainders 0 1
    (hzero 0 1) 10
  norm_num [boundary48Remainders, boundary48Remainders00, boundary48Remainders01,
    boundary48Remainders02,
      boundary48Remainders10, boundary48Remainders11, boundary48Remainders12,
      boundary48Remainders20, boundary48Remainders21, boundary48Remainders22, Fin.sum_univ_three,
        h20, h21, coeff_X, coeff_one, -map_add, -map_mul, -map_sub] at h5
  rw [h1] at h4
  norm_num at h4
  have h5n : m 0 2 + m 1 0 = 0 := by exact_mod_cast h5
  omega

namespace Tiling

theorem boundary48_impossible {T : Triangle} {n : ℕ} (d : Tiling T n)
    (hw : ∀ i, d.tile.angle i = (boundary48TileWeights i : ℝ) * (Real.pi / 24))
    (ha : ∀ i, T.angle i = (boundary48OuterWeights i : ℝ) * (Real.pi / 24)) : False := by
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / 24 : ℝ) : ℂ) * Complex.I)) 48 := by
    simpa only [Nat.cast_one, Nat.cast_ofNat, Nat.reduceMul, one_mul] using
      primitive_pi_root 24 1 (by decide) (by decide)
  have hP := root48Polynomial_vanishes _ hz
  have hzero (i j : Fin 3) :
      boundaryRemainderPoly d.boundarySideCount boundary48Remainders i j = 0 := by
    apply d.boundary_polynomial_remainder_zero 24 (by decide)
      boundary48TileWeights boundary48OuterWeights hw ha
      (by intro l; fin_cases l <;> decide) (by intro l; fin_cases l <;> decide)
      root48Polynomial hP boundary48Quotients boundary48Remainders boundary48_products i j
    exact boundary48_degree d.boundarySideCount i j
  have hrow := boundary48_first_row_zero d.boundarySideCount hzero
  obtain ⟨j, hj⟩ := d.boundary_row_positive 0
  have hh : d.boundarySideCount 0 j ≤ ∑ k, d.boundarySideCount 0 k :=
    Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ j)
  rw [Fin.sum_univ_three, hrow] at hh
  omega

end Tiling
end Erdos633b
