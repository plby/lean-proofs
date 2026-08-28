import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauEquivariance

/-!
# Comparing the actual elliptic and cusp monodromies

The source triangle relation compares the actual modular transformation
at the cusp with the inverse product of the two elliptic monodromies.
Two different values of the lift suffice to identify these Möbius actions
on the whole upper half-plane.  No normalization at the second elliptic
point is assumed in these comparison lemmas.
-/

noncomputable section

open Set UpperHalfPlane ModularGroup
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Two distinct prescribed modular values give an actual regular value,
without specifying which representatives occur above the elliptic values. -/
theorem exists_regular_modular_value_of_j_values {X : Type*} [TopologicalSpace X]
    [PreconnectedSpace X] {τ : X → ℍ} (hτ : Continuous τ) (a b : X)
    (ha : modularJ (τ a) = 0) (hb : modularJ (τ b) = 1728) :
    ∃ x, modularJ (τ x) ∈ modularRegularValues := by
  let F : X → ℝ := fun x => (modularJ (τ x)).re
  have hF : Continuous F := Complex.continuous_re.comp (modularJ_continuous.comp hτ)
  have hmid : (864 : ℝ) ∈ Icc (F a) (F b) := by norm_num [F, ha, hb]
  obtain ⟨x, hx⟩ := intermediate_value_univ a b hF hmid
  refine ⟨x, (mem_modularRegularValues _).mpr ⟨?_, ?_⟩⟩
  · intro hz
    have hh : F x = 0 := by simp [F, hz]
    linarith
  · intro hz
    have hh : F x = 1728 := by norm_num [F, hz]
    linarith

/-- First-order ramification and the value `ρ` already determine the
first generator, with no hypothesis about the other marked value. -/
theorem modular_lift_first_generator_of_rho_order {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ)
    (ha : τ Triangle.centerOne = rhoPoint)
    (horder : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    (hJ : ∀ z : ℍ, modularJ (τ (Triangle.generatorOneSL • z)) = modularJ (τ z))
    (x : ℍ) (hx : modularJ (τ x) ∈ modularRegularValues) :
    ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z := by
  rw [triangleModularA_eq_T_mul_S]
  exact modular_lift_action_of_order hτ Triangle.generatorOneSL Triangle.centerOne
    Triangle.generatorOne_fix 1 (by simpa [ha] using horder) (T * S)
    (by rw [ha]; exact TS_smul_rhoPoint)
    (by rw [ha, modularRho_ambient_deriv, Triangle.generatorOne_multiplier, pow_one]) hJ x hx

/-- Agreement at two distinct interior points identifies entire integral
Möbius actions.  The possible central matrix sign causes no ambiguity. -/
theorem modularSL_actions_eq_of_two_values (B C : SL(2, ℤ)) (a b : ℍ) (hab : a ≠ b)
    (ha : B • a = C • a) (hb : B • b = C • b) :
    ∀ z : ℍ, B • z = C • z := by
  have ha' : (C⁻¹ * B) • a = a := by rw [mul_smul, ha, inv_smul_smul]
  have hb' : (C⁻¹ * B) • b = b := by rw [mul_smul, hb, inv_smul_smul]
  have h := modularSL_action_identity_of_two_fixed (C⁻¹ * B) ha' hb' hab
  intro z
  simpa only [mul_smul, smul_inv_smul] using congrArg (fun w : ℍ => C • w) (h z)

/-- The actual source relation `g₁g₂g₀=1` determines the cusp action on
the image of the lift, before any normalization of the second generator. -/
theorem modular_lift_product_cusp_action {τ : ℍ → ℍ} (B : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z)) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • τ z = τ (Triangle.cuspSL • z) := by
  intro z
  rw [inv_smul_eq_iff, mul_smul, hB, ← hA, ← mul_smul, ← mul_smul,
    Triangle.generatorOneSL_mul_generatorTwoSL_mul_cuspSL, one_smul]

/-- A separately constructed cusp monodromy agrees with the inverse
elliptic product on all of `ℍ`, using two actual distinct lift values. -/
theorem modular_lift_cusp_monodromy_comparison {τ : ℍ → ℍ} (B C : SL(2, ℤ))
    (hA : ∀ z : ℍ, τ (Triangle.generatorOneSL • z) = triangleModularA • τ z)
    (hB : ∀ z : ℍ, B • τ z = τ (Triangle.generatorTwoSL • z))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z)
    (a b : ℍ) (hab : τ a ≠ τ b) :
    ∀ z : ℍ, (triangleModularA * B)⁻¹ • z = C • z := by
  have hp := modular_lift_product_cusp_action B hA hB
  exact modularSL_actions_eq_of_two_values _ _ (τ a) (τ b) hab
    ((hp a).trans (hC a)) ((hp b).trans (hC b))

/-- Changing the chosen modular sheet conjugates the actual cusp
monodromy, as an equality of the genuine upper-half-plane maps. -/
theorem modular_lift_cusp_monodromy_conjugate {τ : ℍ → ℍ} (γ C : SL(2, ℤ))
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∀ z : ℍ, γ • τ (Triangle.cuspSL • z) =
      (γ * C * γ⁻¹) • (γ • τ z) := by
  intro z
  rw [hC, mul_smul, mul_smul, inv_smul_smul]

end Wikipedia.HopfProblem.SpecialPeriods
