import ErdosProblems.Erdos633b.SharedAngleSinePolynomial

/-! Once exact boundary equations give a natural one-parameter matrix,
shared-angle area reduces to a polynomial linear in the squared parameter
and the actual piece count. -/

namespace Erdos633b
open Polynomial

noncomputable def rootAreaBasePoly (M : ℕ) (w : Fin 3 → ℕ)
    (v : Fin 3 → Fin 3 → ℕ) : ℚ[X] :=
  rootBoundaryPoly M w (v 1) * rootBoundaryPoly M w (v 2)

noncomputable def rootTileAreaPoly (M : ℕ) (w : Fin 3 → ℕ) : ℚ[X] :=
  rootSinePoly M (w 1) * rootSinePoly M (w 2)

noncomputable def scaledAreaRemainder (r n : ℕ) (A B : ℚ[X]) : ℚ[X] :=
  C ((r ^ 2 : ℕ) : ℚ) * A - C (n : ℚ) * B

theorem rootBoundaryPoly_mul_counts (M : ℕ) (w v : Fin 3 → ℕ) (r : ℕ) :
    rootBoundaryPoly M w (fun l => v l * r) = C (r : ℚ) * rootBoundaryPoly M w v := by
  simp only [rootBoundaryPoly, Fin.sum_univ_three, Nat.cast_mul, map_mul]
  ring

theorem rootSharedAreaPoly_of_scaled_counts (M : ℕ) (w : Fin 3 → ℕ)
    (m v : Fin 3 → Fin 3 → ℕ) (r n : ℕ) (hm : ∀ i j, m i j = v i j * r) :
    rootSharedAreaPoly M w m n = scaledAreaRemainder r n (rootAreaBasePoly M w v)
      (rootTileAreaPoly M w) := by
  have hi (i : Fin 3) : rootBoundaryPoly M w (m i) = C (r : ℚ) * rootBoundaryPoly M w (v i) := by
    have hh : m i = fun l => v i l * r := funext (hm i)
    rw [hh]
    exact rootBoundaryPoly_mul_counts M w (v i) r
  simp only [rootSharedAreaPoly, hi, scaledAreaRemainder, rootAreaBasePoly, rootTileAreaPoly,
    Nat.cast_pow, map_pow]
  ring

theorem scaledAreaRemainder_decomposition (r n : ℕ) (A B P qA qB RA RB : ℚ[X])
    (hA : A = P * qA + RA) (hB : B = P * qB + RB) :
    scaledAreaRemainder r n A B = P * scaledAreaRemainder r n qA qB +
      scaledAreaRemainder r n RA RB := by
  simp only [scaledAreaRemainder, hA, hB]
  ring

theorem scaledAreaRemainder_coefficients (r n : ℕ) (A B : ℚ[X])
    (h : scaledAreaRemainder r n A B = 0) (k : ℕ) :
    ((r ^ 2 : ℕ) : ℚ) * A.coeff k - (n : ℚ) * B.coeff k = 0 := by
  simpa only [scaledAreaRemainder, coeff_sub, coeff_C_mul, coeff_zero]
    using congrArg (fun p : ℚ[X] => p.coeff k) h

namespace Tiling

theorem root_scaled_area_aeval_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (N : ℕ) (hN : 0 < N) (w : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (hwb : ∀ i, w i ≤ 2 * N) (v : Fin 3 → Fin 3 → ℕ) (r : ℕ)
    (hm : ∀ i j, d.boundarySideCount i j = v i j * r) :
    aeval (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I))
      (scaledAreaRemainder r n (rootAreaBasePoly (2 * N) w v)
        (rootTileAreaPoly (2 * N) w)) = 0 := by
  have hh := d.root_shared_area_aeval_zero h0 N hN w hw hwb
  rw [rootSharedAreaPoly_of_scaled_counts _ _ _ v r n hm] at hh
  exact hh

theorem scaled_area_remainder_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (h0 : T.angle 0 = d.tile.angle 0) (N : ℕ) (hN : 0 < N) (w : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (hwb : ∀ i, w i ≤ 2 * N) (v : Fin 3 → Fin 3 → ℕ) (r : ℕ)
    (hm : ∀ i j, d.boundarySideCount i j = v i j * r)
    (P : ℚ[X]) (hP : aeval (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I)) P = 0)
    (qA qB RA RB : ℚ[X])
    (hA : rootAreaBasePoly (2 * N) w v = P * qA + RA)
    (hB : rootTileAreaPoly (2 * N) w = P * qB + RB)
    (hdeg : (scaledAreaRemainder r n RA RB).natDegree < (2 * N).totient) :
    scaledAreaRemainder r n RA RB = 0 := by
  have hh := d.root_scaled_area_aeval_zero h0 N hN w hw hwb v r hm
  rw [scaledAreaRemainder_decomposition _ _ _ _ P qA qB RA RB hA hB,
    map_add, map_mul, hP, zero_mul, zero_add] at hh
  have hz : IsPrimitiveRoot (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I)) (2 * N) := by
    simpa only [Nat.cast_one, one_mul] using primitive_pi_root N 1 hN (by simp)
  exact zero_of_primitive_root_and_small_degree (2 * N) (by omega) _ hz _ hh hdeg

end Tiling
end Erdos633b
