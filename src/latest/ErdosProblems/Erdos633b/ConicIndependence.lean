import ErdosProblems.Erdos633b.ConicComplexCoordinates

/-! Proven rational independence of the quadratic and cubic conic bases
at sufficiently large primitive root orders. -/

namespace Erdos633b
open Polynomial

def QuadraticConicIndependent (x y : ℝ) : Prop :=
  ∀ a : Fin 5 → ℚ,
    (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y = 0 → ∀ i, a i = 0

def CubicConicIndependent (x y : ℝ) : Prop :=
  ∀ a : Fin 7 → ℚ,
    (a 0 : ℝ) + a 1 * x + a 2 * y + a 3 * x ^ 2 + a 4 * x * y +
      a 5 * x ^ 3 + a 6 * x ^ 2 * y = 0 → ∀ i, a i = 0

theorem CubicConicIndependent.quadratic {x y : ℝ} (h : CubicConicIndependent x y) :
    QuadraticConicIndependent x y := by
  intro a ha
  let b : Fin 7 → ℚ := ![a 0, a 1, a 2, a 3, a 4, 0, 0]
  have hb : (b 0 : ℝ) + b 1 * x + b 2 * y + b 3 * x ^ 2 + b 4 * x * y +
      b 5 * x ^ 3 + b 6 * x ^ 2 * y = 0 := by
    simpa [b] using ha
  have hz := h b hb
  intro i
  fin_cases i
  · exact hz 0
  · exact hz 1
  · exact hz 2
  · exact hz 3
  · exact hz 4

theorem quadratic_conic_independent_of_primitive (D : ℕ) (hD : 0 < D)
    (z ω : ℂ) (hz : IsPrimitiveRoot z D) (hω : ω ^ 2 - ω + 1 = 0)
    (hdeg : 8 < D.totient) (x y : ℝ)
    (hx : (2 * ω - 1) * z * (x : ℂ) = z ^ 2 - 1)
    (hy : (2 * ω - 1) * z * (y : ℂ) = ω * (1 + z ^ 2) - z ^ 2) :
    QuadraticConicIndependent x y := by
  intro a ha
  have ha' : (a 0 : ℂ) + a 1 * (x : ℂ) + a 2 * (y : ℂ) +
      a 3 * (x : ℂ) ^ 2 + a 4 * (x : ℂ) * (y : ℂ) = 0 := by exact_mod_cast ha
  have he := quadraticConicLifts_eval_coordinates a z ω x y hω hx hy
  rw [ha', mul_zero] at he
  obtain ⟨hp, hq⟩ := sixth_root_polynomials_zero_of_degree D hD z hz ω hω
    (quadraticConicLift0 a) (quadraticConicLift1 a) 4
    (quadraticConicLift0_degree a) (quadraticConicLift1_degree a) hdeg he
  exact quadraticConicLifts_coeffs_zero a hp hq

theorem cubic_conic_independent_of_primitive (D : ℕ) (hD : 0 < D)
    (z ω : ℂ) (hz : IsPrimitiveRoot z D) (hω : ω ^ 2 - ω + 1 = 0)
    (hdeg : 12 < D.totient) (x y : ℝ)
    (hx : (2 * ω - 1) * z * (x : ℂ) = z ^ 2 - 1)
    (hy : (2 * ω - 1) * z * (y : ℂ) = ω * (1 + z ^ 2) - z ^ 2) :
    CubicConicIndependent x y := by
  intro a ha
  have ha' : (a 0 : ℂ) + a 1 * (x : ℂ) + a 2 * (y : ℂ) +
      a 3 * (x : ℂ) ^ 2 + a 4 * (x : ℂ) * (y : ℂ) +
      a 5 * (x : ℂ) ^ 3 + a 6 * (x : ℂ) ^ 2 * (y : ℂ) = 0 := by exact_mod_cast ha
  have he := cubicConicLifts_eval_coordinates a z ω x y hω hx hy
  rw [ha', mul_zero] at he
  obtain ⟨hp, hq⟩ := sixth_root_polynomials_zero_of_degree D hD z hz ω hω
    (cubicConicLift0 a) (cubicConicLift1 a) 6
    (cubicConicLift0_degree a) (cubicConicLift1_degree a) hdeg he
  exact cubicConicLifts_coeffs_zero a hp hq

namespace Triangle

theorem groupTwo_quadratic_independent_of_order (S : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((S.angle 0 : ℂ) * Complex.I)) D)
    (hdeg : 8 < D.totient) : QuadraticConicIndependent (S.side 0 / S.side 2)
      (S.side 1 / S.side 2) := by
  obtain ⟨hx, hy⟩ := S.groupTwo_exponential_coordinates hg
  exact quadratic_conic_independent_of_primitive D hD _ sixthRootCoordinate hz
    sixthRootCoordinate_quadratic hdeg _ _ hx hy

theorem groupTwo_cubic_independent_of_order (S : Triangle)
    (hg : S.angle 2 = 2 * Real.pi / 3) (D : ℕ) (hD : 0 < D)
    (hz : IsPrimitiveRoot (Complex.exp ((S.angle 0 : ℂ) * Complex.I)) D)
    (hdeg : 12 < D.totient) : CubicConicIndependent (S.side 0 / S.side 2)
      (S.side 1 / S.side 2) := by
  obtain ⟨hx, hy⟩ := S.groupTwo_exponential_coordinates hg
  exact cubic_conic_independent_of_primitive D hD _ sixthRootCoordinate hz
    sixthRootCoordinate_quadratic hdeg _ _ hx hy

end Triangle
end Erdos633b
