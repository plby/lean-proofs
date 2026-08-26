import ErdosProblems.Erdos633.ReferenceRelabelling
import Mathlib.LinearAlgebra.Matrix.ToLinearEquiv

/-!
# The negative similarity eigenvalue of a nonsquare reptiling

A three-by-three rational determinant is a cubic with rational coefficients.
If its root has an irrational square root of a natural number as value, the
constant and linear terms after reduction modulo that square relation vanish
separately. Thus the negative root is also an eigenvalue. No spectral or
quadratic-field classification is assumed.
-/

namespace Erdos633

open scoped BigOperators

theorem CongruentTiling.aligned_reptile_scale
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hA : P.angleA = R.angleA) (hB : P.angleB = R.angleB) :
    ∃ x : ℝ, 0 < x ∧ x ^ 2 = N ∧ (∀ i, P.sideLength i = x * R.sideLength i) ∧
      ∀ i, ∑ j : Fin 3, (T.boundarySideCount i j : ℝ) * R.sideLength j = x * R.sideLength i := by
  obtain ⟨x, hx, hab, hac, hbc⟩ := P.scaled_sides_of_angles_eq R hA hB
  obtain ⟨e, he⟩ := P.isometry_of_scaled_sides R x hx hab hac hbc
  have hside (i : Fin 3) : P.sideLength i = x * R.sideLength i := by
    have hi : i = 0 ∨ i = 1 ∨ i = 2 := by omega
    rcases hi with rfl | rfl | rfl
    · exact hbc
    · change dist P.c P.a = x * dist R.c R.a
      rw [dist_comm P.c P.a, dist_comm R.c R.a]
      exact hac
    · exact hab
  exact ⟨x, hx, T.similarity_scale_squared x hx e he, hside,
    fun i => (T.boundary_side_count_equation i).symm.trans (hside i)⟩

theorem not_rational_of_sq_eq_nonsquare (N : ℕ) (x : ℝ)
    (hN : ¬ IsSquare N) (hx : x ^ 2 = N) : x ∉ rationalReals := by
  rintro ⟨q, hq⟩
  change (q : ℝ) = x at hq
  have hqR : (q : ℝ) * q = N := by rw [hq, ← pow_two]; exact hx
  have hqQ : q * q = (N : ℚ) := by exact_mod_cast hqR
  exact hN (Rat.isSquare_natCast_iff.mp ⟨q, hqQ.symm⟩)

theorem rational_matrix_three_det_polynomial (D : Matrix (Fin 3) (Fin 3) ℚ) :
    ∃ t u v : ℚ, ∀ x : ℝ,
      (D.map (Rat.castHom ℝ) - x • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det =
        -x ^ 3 + (t : ℝ) * x ^ 2 - (u : ℝ) * x + v := by
  refine ⟨D 0 0 + D 1 1 + D 2 2,
    D 0 0 * D 1 1 + D 0 0 * D 2 2 + D 1 1 * D 2 2 -
      D 0 1 * D 1 0 - D 0 2 * D 2 0 - D 1 2 * D 2 1,
    D 0 0 * D 1 1 * D 2 2 + D 0 1 * D 1 2 * D 2 0 + D 0 2 * D 1 0 * D 2 1 -
      D 0 2 * D 1 1 * D 2 0 - D 0 1 * D 1 0 * D 2 2 - D 0 0 * D 1 2 * D 2 1, ?_⟩
  intro x
  simp [Matrix.det_fin_three, Matrix.sub_apply, Matrix.smul_apply, Matrix.map_apply]
  ring

theorem rational_matrix_three_negative_eigenvector
    (D : Matrix (Fin 3) (Fin 3) ℚ) (N : ℕ) (x : ℝ)
    (hN : ¬ IsSquare N) (hx : x ^ 2 = N)
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (heigen : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i := by
  let A : Matrix (Fin 3) (Fin 3) ℝ := D.map (Rat.castHom ℝ)
  have hdet : (A - x • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    apply Matrix.exists_mulVec_eq_zero_iff.mp
    refine ⟨v, hv, ?_⟩
    rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec]
    ext i
    change (∑ j : Fin 3, (D i j : ℝ) * v j) - x * v i = 0
    exact sub_eq_zero.mpr (heigen i)
  obtain ⟨t, u, z, hpoly⟩ := rational_matrix_three_det_polynomial D
  have hx3 : x ^ 3 = (N : ℝ) * x := by rw [pow_succ, hx]
  have hlinear : ((N : ℝ) + (u : ℝ)) * x = (t : ℝ) * N + z := by
    change (D.map (Rat.castHom ℝ) - x • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 at hdet
    rw [hpoly, hx3, hx] at hdet
    linarith
  have hcoeff : (N : ℝ) + (u : ℝ) = 0 := rational_coefficients_eq
    (not_rational_of_sq_eq_nonsquare N x hN hx)
    (rationalReals.add_mem (rationalReals_nat N) (rationalReals_rat u))
    (rationalReals.add_mem
      (rationalReals.mul_mem (rationalReals_rat t) (rationalReals_nat N))
      (rationalReals_rat z)) hlinear
  have hconstant : (t : ℝ) * N + z = 0 := by rw [hcoeff, zero_mul] at hlinear; exact hlinear.symm
  have hnegative : (A - (-x) • (1 : Matrix (Fin 3) (Fin 3) ℝ)).det = 0 := by
    calc
      _ = -(-x) ^ 3 + (t : ℝ) * (-x) ^ 2 - (u : ℝ) * (-x) + z := hpoly (-x)
      _ = x ^ 3 + (t : ℝ) * x ^ 2 + (u : ℝ) * x + z := by ring
      _ = ((N : ℝ) + (u : ℝ)) * x + ((t : ℝ) * N + z) := by rw [hx3, hx]; ring
      _ = 0 := by rw [hcoeff, hconstant]; ring
  obtain ⟨w, hw, hker⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hnegative
  refine ⟨w, hw, ?_⟩
  rw [Matrix.sub_mulVec, Matrix.smul_mulVec, Matrix.one_mulVec] at hker
  intro i
  have hi := congrFun hker i
  change (∑ j : Fin 3, (D i j : ℝ) * w j) - (-x) * w i = 0 at hi
  exact sub_eq_zero.mp hi

theorem natural_matrix_three_negative_eigenvector
    (D : Fin 3 → Fin 3 → ℕ) (N : ℕ) (x : ℝ)
    (hN : ¬ IsSquare N) (hx : x ^ 2 = N)
    (v : Fin 3 → ℝ) (hv : v ≠ 0)
    (heigen : ∀ i, ∑ j : Fin 3, (D i j : ℝ) * v j = x * v i) :
    ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
      ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i := by
  have h := rational_matrix_three_negative_eigenvector
    (fun i j => (D i j : ℚ)) N x hN hx v hv
    (by simpa only [Rat.cast_natCast] using heigen)
  simpa only [Rat.cast_natCast] using h

theorem CongruentTiling.boundary_matrix_with_negative_eigenvector
    {P R : Triangle} {N : ℕ} (T : CongruentTiling P R N)
    (hN : ¬ IsSquare N) (h : PermutedTriple P.cornerAngle R.cornerAngle) :
    ∃ x : ℝ, 0 < x ∧ x ^ 2 = N ∧ ∃ D : Fin 3 → Fin 3 → ℕ,
      (∀ i, ∑ j : Fin 3, (D i j : ℝ) * R.sideLength j = x * R.sideLength i) ∧
      ∃ w : Fin 3 → ℝ, w ≠ 0 ∧
        ∀ i, ∑ j : Fin 3, (D i j : ℝ) * w j = -x * w i := by
  obtain ⟨x, hx, hsq, D, hD⟩ := T.boundary_matrix_of_permuted_angles h
  have hv : R.sideLength ≠ 0 := by
    intro hz
    have hzero := congrFun hz 0
    exact (ne_of_gt (R.sideLength_pos 0)) hzero
  exact ⟨x, hx, hsq, D, hD, natural_matrix_three_negative_eigenvector D N x hN hsq _ hv hD⟩

end Erdos633
