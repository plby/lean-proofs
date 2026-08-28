import Wikipedia.HopfProblem.PeriodTorusThetaPositivity
import Wikipedia.HopfProblem.PeriodTorusThetaZero
import Wikipedia.HopfProblem.PeriodTorusTypeOneOne

/-!
# Entire theta functions for the actual special period tori

The intrinsic classification of lattice-integral tangent forms combines
with the proved analytic positivity obstruction. Outside the actual
countable exceptional set, a nonzero entire function with genuine
Appell--Humbert automorphy for an integral alternating form of type
`(1,1)` forces that form to be zero. The function is then a nonzero
constant and its actual multiplier is identically one.

This does not assume that arbitrary holomorphic line bundles or their
sections admit an Appell--Humbert presentation.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodTorusTheta

open PeriodTorusTypeOneOne SpecialPeriods UpperHalfPlane

theorem associated_isHermitian (B : RealForm) (hType : IsTypeOneOne B)
    (hAlt : ∀ x, B x x = 0) : IsHermitian (associatedSesquilinear B hType) :=
  associatedSesquilinear_conj_symm B hType hAlt

theorem associated_eq_zero_of_form_eq_zero (B : RealForm) (hType : IsTypeOneOne B)
    (hB : B = 0) : associatedSesquilinear B hType = 0 := by
  apply LinearMap.ext
  intro x
  apply LinearMap.ext
  intro y
  apply Complex.ext
  · simp only [associatedSesquilinear_re, hB, LinearMap.zero_apply, Complex.zero_re]
  · simp only [associatedSesquilinear_im, hB, LinearMap.zero_apply, Complex.zero_im]

/-- The analytic theta obstruction forces the genuine integral tangent form to vanish. -/
theorem form_eq_zero_of_nonzero_theta (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (B : RealForm) (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B)
    (α : (specialPeriodMap.point z).lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy (specialPeriodMap.point z)
      (associatedSesquilinear B hType) α θ)
    (hNonzero : ∃ x, θ x ≠ 0) : B = 0 := by
  apply (associated_nonnegative_iff_zero z hz B hAlt hInt hType).mp
  exact hermitian_nonnegative_of_nonzero_theta (specialPeriodMap.point z)
    (associatedSesquilinear B hType) (associated_isHermitian B hType hAlt)
    α hα θ hθ hAuto hNonzero

/-- All such nonzero entire theta functions are nonzero constants, with trivial multiplier. -/
theorem theta_constant_of_not_exceptional (z : ℍ) (hz : z ∉ exceptionalTypeOneOneSet)
    (B : RealForm) (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B)
    (α : (specialPeriodMap.point z).lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy (specialPeriodMap.point z)
      (associatedSesquilinear B hType) α θ)
    (hNonzero : ∃ x, θ x ≠ 0) :
    B = 0 ∧ ∃ c : ℂ, c ≠ 0 ∧ θ = (fun _ => c) ∧ ∀ l, α l = 1 := by
  have hB := form_eq_zero_of_nonzero_theta z hz B hAlt hInt hType α hα θ hθ hAuto hNonzero
  have hH := associated_eq_zero_of_form_eq_zero B hType hB
  refine ⟨hB, exists_nonzero_const_of_zero_form (specialPeriodMap.point z)
    α hα θ hθ ?_ hNonzero⟩
  simpa only [hH] using hAuto

/-- A nonzero intrinsic integral form has no nonzero entire automorphic functions. -/
theorem theta_eq_zero_of_nonzero_integral_form (z : ℍ)
    (hz : z ∉ exceptionalTypeOneOneSet) (B : RealForm)
    (hAlt : ∀ x, B x x = 0)
    (hInt : IntegralOnPeriodLattice (specialPeriodMap.point z) B)
    (hType : IsTypeOneOne B) (hB : B ≠ 0)
    (α : (specialPeriodMap.point z).lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy (specialPeriodMap.point z)
      (associatedSesquilinear B hType) α θ) : θ = 0 := by
  obtain ⟨_, ⟨v, hv⟩⟩ :=
    associated_indefinite_of_not_exceptional z hz B hAlt hInt hType hB
  exact theta_eq_zero_of_negative_direction (specialPeriodMap.point z)
    (associatedSesquilinear B hType) (associated_isHermitian B hType hAlt)
    α hα θ hθ hAuto v hv

/-- For a nonzero multiple of `η`, the vanishing assertion holds at every period point. -/
theorem theta_eta_multiple_eq_zero (p : PeriodDomain) (n : ℤ) (hn : n ≠ 0)
    (α : p.lattice → ℂ) (hα : ∀ l, ‖α l‖ = 1)
    (θ : ComplexPlane₂ → ℂ) (hθ : Differentiable ℂ θ)
    (hAuto : AppellHumbertAutomorphy p (etaMultipleHermitian p n) α θ) : θ = 0 := by
  obtain ⟨_, ⟨v, hv⟩⟩ := etaMultipleHermitian_indefinite p n hn
  exact theta_eq_zero_of_negative_direction p (etaMultipleHermitian p n)
    (etaMultipleHermitian_conj_symm p n) α hα θ hθ hAuto v hv

end Wikipedia.HopfProblem.PeriodTorusTheta
