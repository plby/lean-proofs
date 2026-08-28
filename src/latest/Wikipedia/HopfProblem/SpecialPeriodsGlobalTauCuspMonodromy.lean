import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMarkingCore
import Wikipedia.HopfProblem.SpecialPeriodsTauCuspCovariance

/-!
# The constructed cusp expansion gives the actual modular monodromy

The analytic cusp formula implies the literal negative unit translation
for the native global lift.  If a modular translate also satisfies the
triangle generator equations, the translating modular matrix commutes
with this cusp action on the entire upper half-plane.
-/

noncomputable section

open Set UpperHalfPlane ModularGroup
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem modular_Tinv_vadd (z : ℍ) : T⁻¹ • z = (-1 : ℝ) +ᵥ z := by
  simpa using UpperHalfPlane.modular_T_zpow_smul z (-1)

/-- The globally continued, actual cusp formula supplies parabolic
monodromy; no equivariance is assumed for the supplied lift. -/
theorem tau_cusp_monodromy_of_formula {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) {r : ℝ} (hr : 0 < r) {h : ℂ → ℂ}
    (hformula : ∀ z : ℍ, ‖Function.Periodic.qParam Triangle.width (z : ℂ)‖ < r →
      (τ z : ℂ) = TauCusp.correctedLogarithmWidth Triangle.width h (z : ℂ)) :
    ∀ z : ℍ, τ (Triangle.cuspSL • z) = T⁻¹ • τ z := by
  intro z
  have he := TauCusp.global_native_sub_int_mul_width_of_cuspFormula
    Triangle.width Triangle.width_pos hr hτ hformula (1 : ℤ) z
  have hz : ((Triangle.cuspSL • z : ℍ) : ℂ) = (z : ℂ) - Triangle.width := by
    rw [Triangle.cuspSL_apply, coe_vadd]
    push_cast
    ring
  have harg : ofComplex ((z : ℂ) - (1 : ℂ) * Triangle.width) = Triangle.cuspSL • z := by
    rw [one_mul, ← hz, ofComplex_apply]
  apply UpperHalfPlane.ext
  calc
    (τ (Triangle.cuspSL • z) : ℂ) = (τ z : ℂ) - 1 := by simpa only [Int.cast_one, harg] using he
    _ = ((T⁻¹ • τ z : ℍ) : ℂ) := by
      rw [modular_Tinv_vadd, coe_vadd]
      push_cast
      ring

/-- The already derived generator laws have the same literal cusp
monodromy for the actual real source cusp matrix. -/
theorem tau_covariant_cuspSL {τ : ℍ → ℍ} (hτ : TauCovariant τ) (z : ℍ) :
    τ (Triangle.cuspSL • z) = T⁻¹ • τ z := by
  rw [Triangle.cuspSL_apply, modular_Tinv_vadd]
  simpa only [triangleGeometricRepresentation_cusp_apply] using tau_covariant_cusp hτ z

/-- If both the initial cusp-normalized lift and its covariant modular
translate have the same primitive cusp translation, that modular change
commutes with the cusp on all of `ℍ`. -/
theorem modular_translate_commutes_Tinv_of_cusp_covariance {τ : ℍ → ℍ}
    (γ : SL(2, ℤ)) (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = T⁻¹ • τ z)
    (hcov : TauCovariant (fun z => γ • τ z))
    (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, γ • (T⁻¹ • z) = T⁻¹ • (γ • z) := by
  have hvalues (z : ℍ) : (γ * T⁻¹) • τ z = (T⁻¹ * γ) • τ z := by
    rw [mul_smul, mul_smul, ← hC z]
    exact tau_covariant_cuspSL hcov z
  simpa only [mul_smul] using
    modularSL_actions_eq_of_two_values (γ * T⁻¹) (T⁻¹ * γ) (τ a) (τ b) hab
      (hvalues a) (hvalues b)

end Wikipedia.HopfProblem.SpecialPeriods
