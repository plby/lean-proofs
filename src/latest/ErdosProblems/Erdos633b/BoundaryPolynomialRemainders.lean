import ErdosProblems.Erdos633b.PrimitiveSinePolynomials

/-! Polynomial remainder certificates give exact rational linear
constraints on the natural boundary counts of an actual tiling. -/

namespace Erdos633b
open Polynomial

noncomputable def boundaryRemainderPoly (m : Fin 3 → Fin 3 → ℕ)
    (r : Fin 3 → Fin 3 → ℚ[X]) (i j : Fin 3) : ℚ[X] :=
  (∑ l, C (m i l : ℚ) * r l j) - ∑ l, C (m j l : ℚ) * r l i

theorem root_boundary_cross_decomposition (M : ℕ) (w a : Fin 3 → ℕ)
    (m : Fin 3 → Fin 3 → ℕ) (P : ℚ[X]) (q r : Fin 3 → Fin 3 → ℚ[X])
    (hprod : ∀ l t, rootSinePoly M (w l) * rootSinePoly M (a t) = P * q l t + r l t)
    (i j : Fin 3) :
    rootBoundaryCrossPoly M w a m i j =
      P * boundaryRemainderPoly m q i j + boundaryRemainderPoly m r i j := by
  unfold rootBoundaryCrossPoly rootBoundaryPoly
  rw [Finset.sum_mul, Finset.sum_mul]
  simp_rw [mul_assoc, hprod]
  simp only [boundaryRemainderPoly, Fin.sum_univ_three]
  ring

theorem boundary_remainder_coefficients (m : Fin 3 → Fin 3 → ℕ)
    (r : Fin 3 → Fin 3 → ℚ[X]) (i j : Fin 3) (h : boundaryRemainderPoly m r i j = 0)
    (k : ℕ) : (∑ l, (m i l : ℚ) * (r l j).coeff k) -
      ∑ l, (m j l : ℚ) * (r l i).coeff k = 0 := by
  have hh := congrArg (fun p : ℚ[X] => p.coeff k) h
  simpa only [boundaryRemainderPoly, Fin.sum_univ_three, coeff_sub, coeff_add,
    coeff_C_mul, coeff_zero] using hh

namespace Tiling

theorem boundary_polynomial_remainder_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 0 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwb : ∀ i, w i ≤ 2 * N) (hab : ∀ i, a i ≤ 2 * N)
    (P : ℚ[X]) (hP : aeval (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I)) P = 0)
    (q r : Fin 3 → Fin 3 → ℚ[X])
    (hprod : ∀ l t, rootSinePoly (2 * N) (w l) * rootSinePoly (2 * N) (a t) =
      P * q l t + r l t)
    (i j : Fin 3)
    (hdeg : (boundaryRemainderPoly d.boundarySideCount r i j).natDegree < (2 * N).totient) :
    boundaryRemainderPoly d.boundarySideCount r i j = 0 := by
  have hh := d.root_boundary_cross_aeval_zero N hN w a hw ha hwb hab i j
  rw [root_boundary_cross_decomposition _ _ _ _ P q r hprod i j,
    map_add, map_mul, hP, zero_mul, zero_add] at hh
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I)) (2 * N) := by
    simpa only [Nat.cast_one, one_mul] using primitive_pi_root N 1 hN (by simp)
  exact zero_of_primitive_root_and_small_degree (2 * N) (by omega) _ hz _ hh hdeg

end Tiling
end Erdos633b
