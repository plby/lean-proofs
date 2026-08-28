import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauEquivarianceCore
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMultiplier

/-!
# Derivatives of actual modular monodromy transformations

An intertwining integral modular transformation fixes the image of every
source fixed point.  Its derivative at that actual image is determined by
the local order of the holomorphic lift.  No normalization of the image
point to `ρ` or `i` is assumed.
-/

noncomputable section

open Filter Set UpperHalfPlane
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

theorem modular_lift_monodromy_fixes_image {τ : ℍ → ℍ}
    (A : SL(2, ℝ)) (a : ℍ) (hAa : A • a = a)
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) :
    γ • τ a = τ a := by
  simpa only [hAa] using hγ a

/-- Native upper-half-plane form of the analytic semiconjugacy multiplier
identity, with the target derivative taken at the actual value `τ a`. -/
theorem modular_lift_monodromy_deriv_of_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (A : SL(2, ℝ)) (a : ℍ)
    (hAa : A • a = a) (k : ℕ)
    (horder : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ a : ℂ))
      (a : ℂ) = (k : ℕ∞))
    (γ : SL(2, ℤ)) (hγ : ∀ z : ℍ, γ • τ z = τ (A • z)) :
    deriv (fun w : ℂ => ((γ • ofComplex w : ℍ) : ℂ)) (τ a : ℂ) =
      Triangle.slMultiplier A a ^ k := by
  have hγfix := modular_lift_monodromy_fixes_image A a hAa γ hγ
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
  simpa only [α, β, Triangle.sl_deriv_smul] using hm

/-- The first source generator has target multiplier `-ρ` whenever the
lift has order one at its source center, regardless of the image point. -/
theorem modular_lift_generatorOne_monodromy_deriv {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (horder : analyticOrderAt
      (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ Triangle.centerOne : ℂ))
      (Triangle.centerOne : ℂ) = 1)
    (γ : SL(2, ℤ))
    (hγ : ∀ z : ℍ, γ • τ z = τ (Triangle.generatorOneSL • z)) :
    deriv (fun w : ℂ => ((γ • ofComplex w : ℍ) : ℂ)) (τ Triangle.centerOne : ℂ) =
      -rho := by
  simpa only [Triangle.generatorOne_multiplier, pow_one] using
    modular_lift_monodromy_deriv_of_order hτ Triangle.generatorOneSL Triangle.centerOne
      Triangle.generatorOne_fix 1 horder γ hγ

/-- Ramification order two turns the second source multiplier `-i` into
the target multiplier `-1`, with no assumption that the target point is `i`. -/
theorem modular_lift_generatorTwo_monodromy_deriv {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (horder : analyticOrderAt
      (fun z : ℂ => (τ (ofComplex z) : ℂ) - (τ Triangle.centerTwo : ℂ))
      (Triangle.centerTwo : ℂ) = 2)
    (γ : SL(2, ℤ))
    (hγ : ∀ z : ℍ, γ • τ z = τ (Triangle.generatorTwoSL • z)) :
    deriv (fun w : ℂ => ((γ • ofComplex w : ℍ) : ℂ)) (τ Triangle.centerTwo : ℂ) =
      -1 := by
  simpa only [Triangle.generatorTwo_multiplier, neg_sq, Complex.I_sq] using
    modular_lift_monodromy_deriv_of_order hτ Triangle.generatorTwoSL Triangle.centerTwo
      Triangle.generatorTwo_fix 2 horder γ hγ

end Wikipedia.HopfProblem.SpecialPeriods
