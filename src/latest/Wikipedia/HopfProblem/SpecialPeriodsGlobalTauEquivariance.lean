import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauEquivarianceCore
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMultiplier
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauGroupAction

/-!
# Deriving the global special-period generator laws

For an actual holomorphic modular lift, invariance of its modular equation
gives a fixed modular transformation for each source generator.  The exact
order of the lift at an elliptic center determines that transformation's
derivative.  The centered Cayley coordinate then identifies the entire
transformation, and hence proves the global covariance equations.

Both marked values are explicit hypotheses here.  These theorems do not
assume covariance, but they do not construct the global source coordinate
or assert simultaneous normalization of an arbitrary lift.
-/

noncomputable section

open Filter Set UpperHalfPlane ModularGroup
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Exact local ramification determines the global modular action of a
source automorphism on a holomorphic lift. -/
theorem modular_lift_action_of_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (A : SL(2, ℝ)) (a : ℍ)
    (hAa : A • a = a) (k : ℕ)
    (horder : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ))
      (a : ℂ) = (k : ℕ∞))
    (B : SL(2, ℤ)) (hBb : B • τ a = τ a)
    (hBderiv : deriv (fun z : ℂ => ((B • ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k)
    (hJ : ∀ z : ℍ, modularJ (τ (A • z)) = modularJ (τ z))
    (x : ℍ) (hx : modularJ (τ x) ∈ modularRegularValues) :
    ∀ z : ℍ, τ (A • z) = B • τ z := by
  obtain ⟨γ, hγ⟩ := modularJ_invariant_lift_action hτ A hJ x hx
  have hγfix : γ • τ a = τ a := by simpa only [hAa] using hγ a
  let t : ℂ → ℂ := fun z => (τ (ofComplex z) : ℂ)
  let α : ℂ → ℂ := fun z => ((A • ofComplex z : ℍ) : ℂ)
  let β : ℂ → ℂ := fun z => ((γ • ofComplex z : ℍ) : ℂ)
  have ht : AnalyticAt ℂ t (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift (hτ.mdifferentiable (by simp)) a
  have hα : AnalyticAt ℂ α (a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((Triangle.specialLinear_holomorphic A).mdifferentiable (by simp)) a
  have hβ : AnalyticAt ℂ β (τ a : ℂ) :=
    ModularGermLift.analyticAt_upperHalfPlane_lift
      ((modularSL_holomorphic γ).mdifferentiable (by simp)) (τ a)
  have ht₀ : t (a : ℂ) = (τ a : ℂ) := by simp only [t, ofComplex_apply]
  have hα₀ : α (a : ℂ) = (a : ℂ) := by simp only [α, ofComplex_apply, hAa]
  have hβ₀ : β (τ a : ℂ) = (τ a : ℂ) := by simp only [β, ofComplex_apply, hγfix]
  have hsem : t ∘ α =ᶠ[𝓝 (a : ℂ)] β ∘ t := by
    filter_upwards with w
    simpa only [t, α, β, Function.comp_apply, ofComplex_apply] using
      (congrArg (fun z : ℍ => (z : ℂ)) (hγ (ofComplex w))).symm
  have hm := analytic_semiconjugacy_deriv_pow t α β (a : ℂ) (τ a : ℂ) k
    ht ht₀ horder hα hα₀ hβ hβ₀ hsem
  have hderiv : deriv (fun z : ℂ => ((γ • ofComplex z : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by
    simpa only [α, β, Triangle.sl_deriv_smul] using hm
  have he := modularSL_actions_eq_of_fixed_deriv γ B (τ a) hγfix hBb
    (hderiv.trans hBderiv.symm)
  intro z
  exact (hγ z).symm.trans (he (τ z))

/-- The actual two normalized elliptic values and lift orders force both
global generator equations.  No generator covariance is assumed. -/
theorem tau_covariant_of_normalized_modular_invariance {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (ha : τ Triangle.centerOne = rhoPoint)
    (hb : τ Triangle.centerTwo = UpperHalfPlane.I)
    (horder₁ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    (horder₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2)
    (hJ₁ : ∀ z : ℍ, modularJ (τ (Triangle.generatorOneSL • z)) = modularJ (τ z))
    (hJ₂ : ∀ z : ℍ, modularJ (τ (Triangle.generatorTwoSL • z)) = modularJ (τ z)) :
    TauCovariant τ := by
  obtain ⟨x, hx⟩ := exists_regular_modular_value_of_centers hτ.continuous
    Triangle.centerOne Triangle.centerTwo ha hb
  have h₁ := modular_lift_action_of_order hτ Triangle.generatorOneSL Triangle.centerOne
    Triangle.generatorOne_fix 1 (by simpa [ha] using horder₁) (T * S)
    (by rw [ha]; exact TS_smul_rhoPoint)
    (by rw [ha, modularRho_ambient_deriv, Triangle.generatorOne_multiplier, pow_one])
    hJ₁ x hx
  have h₂ := modular_lift_action_of_order hτ Triangle.generatorTwoSL Triangle.centerTwo
    Triangle.generatorTwo_fix 2 (by simpa [hb] using horder₂) S
    (by rw [hb]; exact S_smul_I)
    (by rw [hb, modularI_ambient_deriv, Triangle.generatorTwo_multiplier]; norm_num)
    hJ₂ x hx
  constructor
  · intro z
    have h := congrArg (fun w : ℍ => (w : ℂ)) (h₁ z)
    rw [← modularRhoAction_coe] at h
    exact h
  · intro z
    have h := congrArg (fun w : ℍ => (w : ℂ)) (h₂ z)
    rw [← modularIAction_coe] at h
    exact h

/-- A normalized global lift of an invariant source function with the
actual triangle branching orders satisfies all special-period generator
equations.  The lift orders are derived from the modular equation. -/
theorem tau_covariant_of_normalized_modular_lift (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (ha : τ Triangle.centerOne = rhoPoint)
    (hb : τ Triangle.centerTwo = UpperHalfPlane.I)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728)
      (Triangle.centerTwo : ℂ) = 4) : TauCovariant τ := by
  have hFa : F Triangle.centerOne = 0 := by rw [← hJ _, ha, modularJ_rhoPoint]
  have hFb : F Triangle.centerTwo = 1728 := by rw [← hJ _, hb, modularJ_I]
  have hτMD := hτ.mdifferentiable (by simp)
  have ho₁ := ModularGermLift.native_modularJ_lift_order_of_zero hτMD hJ (n := 1)
    hFa (by simpa using horder₁)
  have ho₂ := ModularGermLift.native_modularJ_lift_order_of_1728 hτMD hJ (n := 2)
    hFb (by simpa using horder₂)
  apply tau_covariant_of_normalized_modular_invariance hτ ha hb
    (by simpa [ha] using ho₁) (by simpa [hb] using ho₂)
  · intro z
    rw [hJ, hJ, hF₁]
  · intro z
    rw [hJ, hJ, hF₂]

end Wikipedia.HopfProblem.SpecialPeriods
