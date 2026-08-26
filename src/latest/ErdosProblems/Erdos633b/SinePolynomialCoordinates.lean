import ErdosProblems.Erdos633b.ConjugateAreaSigns
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Chebyshev.Basic

/-! Explicit rational polynomials for normalized integer-multiple sines,
and the resulting necessary conjugate sign agreement for actual tilings. -/

namespace Erdos633b
open Polynomial

noncomputable def sineMultiplePoly (m : ℕ) : ℚ[X] :=
  Chebyshev.S ℚ ((m : ℤ) - 1)

theorem eval_sineMultiplePoly (θ : ℝ) (hs : Real.sin θ ≠ 0) (m : ℕ) :
    aeval (2 * Real.cos θ) (sineMultiplePoly m) =
      Real.sin ((m : ℝ) * θ) / Real.sin θ := by
  apply (eq_div_iff hs).mpr
  rw [sineMultiplePoly, Chebyshev.aeval_S]
  simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_one, sub_add_cancel] using
    Chebyshev.S_two_mul_real_cos θ ((m : ℤ) - 1)

noncomputable def sineProductPoly (w : Fin 3 → ℕ) : ℚ[X] :=
  sineMultiplePoly (w 0) * sineMultiplePoly (w 1) * sineMultiplePoly (w 2)

noncomputable def boundarySinePoly (w m : Fin 3 → ℕ) : ℚ[X] :=
  C (m 0 : ℚ) * sineMultiplePoly (w 0) +
  C (m 1 : ℚ) * sineMultiplePoly (w 1) +
  C (m 2 : ℚ) * sineMultiplePoly (w 2)

theorem eval_sineProductPoly (θ : ℝ) (hs : Real.sin θ ≠ 0) (w : Fin 3 → ℕ) :
    aeval (2 * Real.cos θ) (sineProductPoly w) =
      (Real.sin (w 0 * θ) / Real.sin θ) * (Real.sin (w 1 * θ) / Real.sin θ) *
        (Real.sin (w 2 * θ) / Real.sin θ) := by
  simp [sineProductPoly, eval_sineMultiplePoly θ hs]

theorem eval_boundarySinePoly (θ : ℝ) (hs : Real.sin θ ≠ 0) (w m : Fin 3 → ℕ) :
    aeval (2 * Real.cos θ) (boundarySinePoly w m) =
      (m 0 : ℝ) * (Real.sin (w 0 * θ) / Real.sin θ) +
      m 1 * (Real.sin (w 1 * θ) / Real.sin θ) +
      m 2 * (Real.sin (w 2 * θ) / Real.sin θ) := by
  simp [boundarySinePoly, eval_sineMultiplePoly θ hs]

namespace Tiling

theorem conjugate_weight_sine_product_positive {T : Triangle} {n : ℕ} (d : Tiling T n)
    (θ ψ : ℝ) (hθ : Real.sin θ ≠ 0) (hψ : Real.sin ψ ≠ 0)
    (w a : Fin 3 → ℕ)
    (hw : ∀ j, d.tile.angle j = (w j : ℝ) * θ)
    (ha : ∀ j, T.angle j = (a j : ℝ) * θ)
    (f : ℚ[X]) (hf : Irreducible f) (hm : f.Monic)
    (ht : aeval (2 * Real.cos θ) f = 0) (ht' : aeval (2 * Real.cos ψ) f = 0)
    (hw' : ∀ j, Real.sin (w j * ψ) ≠ 0) (ha' : Real.sin (a 0 * ψ) ≠ 0) :
    0 < (Real.sin (w 0 * ψ) * Real.sin (w 1 * ψ) * Real.sin (w 2 * ψ)) *
      (Real.sin (a 0 * ψ) * Real.sin (a 1 * ψ) * Real.sin (a 2 * ψ)) := by
  have hP' : aeval (2 * Real.cos ψ) (sineProductPoly w) ≠ 0 := by
    rw [eval_sineProductPoly ψ hψ]
    exact mul_ne_zero (mul_ne_zero (div_ne_zero (hw' 0) hψ)
      (div_ne_zero (hw' 1) hψ)) (div_ne_zero (hw' 2) hψ)
  have hF' : aeval (2 * Real.cos ψ) (sineMultiplePoly (a 0)) ≠ 0 := by
    rw [eval_sineMultiplePoly ψ hψ]
    exact div_ne_zero ha' hψ
  have hpos := d.conjugate_sine_product_positive (Real.sin θ) hθ f
    (sineProductPoly w) (sineProductPoly a) (sineMultiplePoly (a 0))
    (boundarySinePoly w (d.boundarySideCount 0))
    (2 * Real.cos θ) (2 * Real.cos ψ) hf hm ht ht'
    (by simpa only [hw] using eval_sineProductPoly θ hθ w)
    (by simpa only [ha] using eval_sineProductPoly θ hθ a)
    (by simpa only [ha] using eval_sineMultiplePoly θ hθ (a 0))
    (by simpa only [hw] using eval_boundarySinePoly θ hθ w (d.boundarySideCount 0))
    hP' hF'
  rw [eval_sineProductPoly ψ hψ, eval_sineProductPoly ψ hψ] at hpos
  have hmpos := mul_pos hpos (pow_pos (sq_pos_of_ne_zero hψ) 3)
  convert hmpos using 1 <;> first | rfl | (field_simp [hψ])

end Tiling
end Erdos633b
