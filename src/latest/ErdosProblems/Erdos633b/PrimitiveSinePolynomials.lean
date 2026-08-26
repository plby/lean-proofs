import ErdosProblems.Erdos633b.CosinePolynomialLifts
import ErdosProblems.Erdos633b.ConjugateBoundaryEquations

/-! Exact polynomial coordinates for rational-angle boundary equations
at a primitive complex root. -/

namespace Erdos633b
open Polynomial

noncomputable def rootSinePoly (M k : ℕ) : ℚ[X] := X ^ k - X ^ (M - k)

theorem exp_sub_inv_eq_two_sine (θ : ℝ) :
    Complex.exp ((θ : ℂ) * Complex.I) - (Complex.exp ((θ : ℂ) * Complex.I))⁻¹ =
      2 * Complex.I * (Real.sin θ : ℂ) := by
  rw [← Complex.exp_neg]
  have hn : -((θ : ℂ) * Complex.I) = (-θ : ℂ) * Complex.I := by ring
  rw [hn, Complex.exp_mul_I, Complex.exp_mul_I, Complex.cos_neg, Complex.sin_neg]
  push_cast
  ring

theorem rootSinePoly_eval (M k : ℕ) (hk : k ≤ M) (θ : ℝ)
    (hz : Complex.exp ((θ : ℂ) * Complex.I) ^ M = 1) :
    aeval (Complex.exp ((θ : ℂ) * Complex.I)) (rootSinePoly M k) =
      2 * Complex.I * (Real.sin (k * θ) : ℂ) := by
  let z := Complex.exp ((θ : ℂ) * Complex.I)
  have hp : z ^ k = Complex.exp (((k : ℝ) * θ : ℝ) * Complex.I) := by
    dsimp only [z]
    rw [← Complex.exp_nat_mul]
    congr 1
    push_cast
    ring
  simp only [rootSinePoly, map_sub, map_pow, aeval_X]
  rw [pow_sub₀ _ (Complex.exp_ne_zero _) hk, hz, one_mul]
  change z ^ k - (z ^ k)⁻¹ = _
  rw [hp]
  exact exp_sub_inv_eq_two_sine (k * θ)

noncomputable def rootBoundaryPoly (M : ℕ) (w m : Fin 3 → ℕ) : ℚ[X] :=
  ∑ l, C (m l : ℚ) * rootSinePoly M (w l)

theorem rootBoundaryPoly_eval (M : ℕ) (w m : Fin 3 → ℕ)
    (hw : ∀ l, w l ≤ M) (θ : ℝ)
    (hz : Complex.exp ((θ : ℂ) * Complex.I) ^ M = 1) :
    aeval (Complex.exp ((θ : ℂ) * Complex.I)) (rootBoundaryPoly M w m) =
      2 * Complex.I * (boundarySineCombination m (fun l => Real.sin (w l * θ)) : ℂ) := by
  simp only [rootBoundaryPoly, map_sum, map_mul, aeval_C]
  simp_rw [rootSinePoly_eval M _ (hw _) θ hz]
  simp only [Fin.sum_univ_three, boundarySineCombination]
  push_cast
  ring

noncomputable def rootBoundaryCrossPoly (M : ℕ) (w a : Fin 3 → ℕ)
    (m : Fin 3 → Fin 3 → ℕ) (i j : Fin 3) : ℚ[X] :=
  rootBoundaryPoly M w (m i) * rootSinePoly M (a j) -
    rootBoundaryPoly M w (m j) * rootSinePoly M (a i)

namespace Tiling

theorem root_boundary_cross_aeval_zero {T : Triangle} {n : ℕ} (d : Tiling T n)
    (N : ℕ) (hN : 0 < N) (w a : Fin 3 → ℕ)
    (hw : ∀ i, d.tile.angle i = (w i : ℝ) * (Real.pi / N))
    (ha : ∀ i, T.angle i = (a i : ℝ) * (Real.pi / N))
    (hwb : ∀ i, w i ≤ 2 * N) (hab : ∀ i, a i ≤ 2 * N) (i j : Fin 3) :
    aeval (Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I))
      (rootBoundaryCrossPoly (2 * N) w a d.boundarySideCount i j) = 0 := by
  have hz : Complex.exp (((Real.pi / N : ℝ) : ℂ) * Complex.I) ^ (2 * N) = 1 := by
    have hh := (primitive_pi_root N 1 hN (by simp)).pow_eq_one
    simpa only [Nat.cast_one, one_mul] using hh
  simp only [rootBoundaryCrossPoly, map_sub, map_mul]
  rw [rootBoundaryPoly_eval _ _ _ hwb _ hz, rootBoundaryPoly_eval _ _ _ hwb _ hz,
    rootSinePoly_eval _ _ (hab j) _ hz, rootSinePoly_eval _ _ (hab i) _ hz]
  have hh := d.boundary_sine_cross_eq i j
  simp_rw [hw, ha] at hh
  have hh' :
      (boundarySineCombination (d.boundarySideCount i)
        (fun l => Real.sin (w l * (Real.pi / N))) : ℂ) *
        (Real.sin (a j * (Real.pi / N)) : ℂ) =
      (boundarySineCombination (d.boundarySideCount j)
        (fun l => Real.sin (w l * (Real.pi / N))) : ℂ) *
        (Real.sin (a i * (Real.pi / N)) : ℂ) := by exact_mod_cast hh
  linear_combination (2 * Complex.I) ^ 2 * hh'

end Tiling
end Erdos633b
