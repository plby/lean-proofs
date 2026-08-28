import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMarkingCore
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauMonodromyDerivative
import Wikipedia.HopfProblem.SpecialPeriodsGlobalTauNormalizationDerivatives

/-!
# Simultaneous normalization from the actual cusp monodromy

For a holomorphic modular lift of an invariant triangle function with
branch orders three and four, a parabolic cusp monodromy supplies the
missing relation between the two elliptic markings.  After first taking
the order-three value to `ρ`, one of three explicit cyclic normalizers
takes the order-four value to `i` and produces both global generator laws.

Thus neither elliptic normalization is assumed in the final theorem.
The modular lift and its parabolic cusp monodromy are inputs here; a
separate analytic cusp construction supplies them from a simple pole.
-/

noncomputable section

open Set UpperHalfPlane ModularGroup Matrix
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods

/-- Once the first value is `ρ`, the actual cusp monodromy forces one of
three explicit cyclic changes to normalize the second value as well. -/
theorem exists_cyclic_normalization_of_rho_lift (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (ha : τ Triangle.centerOne = rhoPoint) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728)
      (Triangle.centerTwo : ℂ) = 4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ k : Fin 3, TauCovariant (fun z => modularCyclicNormalizer k • τ z) ∧
      modularCyclicNormalizer k • τ Triangle.centerOne = rhoPoint ∧
      modularCyclicNormalizer k • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hJa : modularJ (τ Triangle.centerOne) = 0 := by rw [ha, modularJ_rhoPoint]
  have hJb : modularJ (τ Triangle.centerTwo) = 1728 := (hJ _).trans hFb
  have hFa : F Triangle.centerOne = 0 := (hJ _).symm.trans hJa
  obtain ⟨x, hx⟩ := exists_regular_modular_value_of_j_values hτ.continuous
    Triangle.centerOne Triangle.centerTwo hJa hJb
  have hτMD := hτ.mdifferentiable (by simp)
  have ho₁ := ModularGermLift.native_modularJ_lift_order_of_zero hτMD hJ (n := 1)
    hFa (by simpa using horder₁)
  have ho₂ := ModularGermLift.native_modularJ_lift_order_of_1728 hτMD hJ (n := 2)
    hFb (by simpa using horder₂)
  have hA := modular_lift_first_generator_of_rho_order hτ ha (by simpa [ha] using ho₁)
    (by intro z; rw [hJ, hJ, hF₁]) x hx
  obtain ⟨B, hB⟩ := modularJ_invariant_lift_action hτ Triangle.generatorTwoSL
    (by intro z; rw [hJ, hJ, hF₂]) x hx
  have hBfix := modular_lift_monodromy_fixes_image Triangle.generatorTwoSL
    Triangle.centerTwo Triangle.generatorTwo_fix B hB
  have hBderiv := modular_lift_generatorTwo_monodromy_deriv hτ (by simpa using ho₂) B hB
  have hBtr := modularSL_trace_zero_of_fixed_deriv_neg_one B (τ Triangle.centerTwo)
    hBfix hBderiv
  have hab : τ Triangle.centerOne ≠ τ Triangle.centerTwo := by
    intro he
    have hh := congrArg modularJ he
    rw [hJa, hJb] at hh
    norm_num at hh
  have hcomp := modular_lift_cusp_monodromy_comparison B C hA hB hC
    Triangle.centerOne Triangle.centerTwo hab
  have hprod := modular_pair_trace_two_or_neg_two_of_cusp_actions_eq B C hcomp hCtr
  obtain ⟨k, hkρ, hki, hkA, hkB, _⟩ :=
    modular_pair_elliptic_value_normalization B hBtr hprod (τ Triangle.centerTwo) hBfix
  refine ⟨k, ⟨?_, ?_⟩, ?_, hki⟩
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorOneSL • z) : ℍ) : ℂ) = _
    rw [hA, hkA, triangleModularA_eq_T_mul_S, ← modularRhoAction_coe]
    rfl
  · intro z
    change ((modularCyclicNormalizer k • τ (Triangle.generatorTwoSL • z) : ℍ) : ℂ) = _
    rw [← hB z, hkB, ← modularIAction_coe]
    rfl
  · rw [ha, hkρ]

/-- A genuine integral modular translate simultaneously normalizes both
elliptic values and satisfies the two global special-period equations.
Neither marked value nor covariance is assumed for the supplied lift. -/
theorem exists_normalized_covariant_modular_translate (F : ℍ → ℂ) {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hJ : ∀ z : ℍ, modularJ (τ z) = F z)
    (hFa : F Triangle.centerOne = 0) (hFb : F Triangle.centerTwo = 1728)
    (hF₁ : ∀ z : ℍ, F (Triangle.generatorOneSL • z) = F z)
    (hF₂ : ∀ z : ℍ, F (Triangle.generatorTwoSL • z) = F z)
    (horder₁ : analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 3)
    (horder₂ : analyticOrderAt (fun z : ℂ => F (ofComplex z) - 1728)
      (Triangle.centerTwo : ℂ) = 4)
    (C : SL(2, ℤ)) (hCtr : Matrix.trace C.val = 2 ∨ Matrix.trace C.val = -2)
    (hC : ∀ z : ℍ, τ (Triangle.cuspSL • z) = C • τ z) :
    ∃ γ : SL(2, ℤ), TauCovariant (fun z => γ • τ z) ∧
      γ • τ Triangle.centerOne = rhoPoint ∧
      γ • τ Triangle.centerTwo = UpperHalfPlane.I := by
  have hzero : modularJ rhoPoint = modularJ (τ Triangle.centerOne) := by
    rw [modularJ_rhoPoint, hJ, hFa]
  obtain ⟨δ, hδ⟩ := (modularJ_eq_iff_exists_smul rhoPoint (τ Triangle.centerOne)).mp hzero
  let σ : ℍ → ℍ := fun z => δ • τ z
  have hσ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω σ := (modularSL_holomorphic δ).comp hτ
  have hσJ : ∀ z : ℍ, modularJ (σ z) = F z := by
    intro z
    exact (modularJ_SL_invariant δ (τ z)).trans (hJ z)
  have hσa : σ Triangle.centerOne = rhoPoint := hδ
  have hCtr' : Matrix.trace (δ * C * δ⁻¹).val = 2 ∨
      Matrix.trace (δ * C * δ⁻¹).val = -2 := by
    simpa only [modularSL_trace_conjugate] using hCtr
  have hC' : ∀ z : ℍ, σ (Triangle.cuspSL • z) = (δ * C * δ⁻¹) • σ z :=
    modular_lift_cusp_monodromy_conjugate δ C hC
  obtain ⟨k, hkc, hka, hkb⟩ := exists_cyclic_normalization_of_rho_lift F hσ hσJ hσa
    hFb hF₁ hF₂ horder₁ horder₂ (δ * C * δ⁻¹) hCtr' hC'
  refine ⟨modularCyclicNormalizer k * δ, ?_, ?_, ?_⟩
  · simpa only [TauCovariant, σ, mul_smul] using hkc
  · simpa only [σ, mul_smul] using hka
  · simpa only [σ, mul_smul] using hkb

end Wikipedia.HopfProblem.SpecialPeriods
