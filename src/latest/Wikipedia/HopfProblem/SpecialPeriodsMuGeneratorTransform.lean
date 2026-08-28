import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorBasic
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorRootSecondSign
import Wikipedia.HopfProblem.SpecialPeriodsTriangleRepresentation

/-!
# The actual homogeneous transformation laws of the μ-generator

The weights of `E₄²`, the square root of `E₆`, and the discriminant are
eight, three, and twelve. Their quotient therefore has the required
weight minus one. The two signs are those forced by the actual elliptic
fixed points, not additional assumptions about the generator.

Two functions with the same homogeneous law have an invariant pointwise
quotient. This algebraic statement also holds at zeros of the denominator;
holomorphic extension of that quotient is a separate analytic question.
-/

noncomputable section

open UpperHalfPlane ModularForm ModularGroup
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- Every genuine level-one modular form has its usual weight under the
first source generator, by covariance of the supplied map `τ`. -/
theorem modularForm_generatorOne {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : TauCovariant τ) (z : ℍ) :
    f (τ (Triangle.generatorOneSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg : τ (Triangle.generatorOneSL • z) = (T * S) • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularRhoAction_coe]
    exact hτc.1 z
  have hd : denom (T * S : SL(2, ℤ)) (τ z) = (τ z : ℂ) := by
    have h10 : (T * S : SL(2, ℤ)) 1 0 = 1 := by decide
    have h11 : (T * S : SL(2, ℤ)) 1 1 = 0 := by decide
    rw [denom_apply, h10, h11]
    simp
  rw [hτg, levelOne_transform, hd]

/-- The corresponding modular weight law for the second source generator. -/
theorem modularForm_generatorTwo {τ : ℍ → ℍ} {k : ℤ}
    (f : ModularForm 𝒮ℒ k) (hτc : TauCovariant τ) (z : ℍ) :
    f (τ (Triangle.generatorTwoSL • z)) = (τ z : ℂ) ^ k * f (τ z) := by
  have hτg : τ (Triangle.generatorTwoSL • z) = S • τ z := by
    apply UpperHalfPlane.ext
    rw [← modularIAction_coe]
    exact hτc.2 z
  rw [hτg, levelOne_transform, denom_S]

/-- Invariance under the two actual generators gives invariance under
the entire actual triangle-group representation. -/
theorem triangle_invariant_of_generators (f : ℍ → ℂ)
    (h₁ : ∀ z, f (Triangle.generatorOneSL • z) = f z)
    (h₂ : ∀ z, f (Triangle.generatorTwoSL • z) = f z)
    (g : TriangleGroup) :
    ∀ z, f (triangleGeometricRepresentation g z) = f z := by
  let := triangleGeometricAction
  have hg : g ∈ Subgroup.closure
      ({triangleGenerator₁, triangleGenerator₂} : Set TriangleGroup) := by
    rw [triangle_generators_generate]
    trivial
  change ∀ z, f (g • z) = f z
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · intro z
      change f (triangleGeometricRepresentation triangleGenerator₁ z) = f z
      simpa only [triangleGeometricRepresentation_generator₁_apply] using h₁ z
    · intro z
      change f (triangleGeometricRepresentation triangleGenerator₂ z) = f z
      simpa only [triangleGeometricRepresentation_generator₂_apply] using h₂ z
  | one => intro z; rw [one_smul]
  | mul g h _ _ ihg ihh => intro z; rw [mul_smul, ihg, ihh]
  | inv g _ ih =>
    intro z
    simpa only [smul_inv_smul] using (ih (g⁻¹ • z)).symm

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

/-- The actual Eisenstein generator obeys the negative first homogeneous law. -/
theorem generator_generatorOne
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ) (z : ℍ) :
    r.generator (Triangle.generatorOneSL • z) = -r.generator z / (τ z : ℂ) := by
  have h4 : E₄ (τ (Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 4 * E₄ (τ z) := by
    simpa only [zpow_ofNat] using modularForm_generatorOne E₄ hτc z
  have hD : discriminant (τ (Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ 12 * discriminant (τ z) := by
    have h :=
      modularForm_generatorOne (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change discriminant (τ (Triangle.generatorOneSL • z)) =
      (τ z : ℂ) ^ (12 : ℤ) * discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD, eisensteinSix_root_generatorOne hτ hτc r.holomorphic r.square z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, discriminant_ne_zero (τ z)]

/-- A simple root zero at the second center forces the positive second
homogeneous law of the actual Eisenstein generator. -/
theorem generator_generatorTwo
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (horder : analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1) (z : ℍ) :
    r.generator (Triangle.generatorTwoSL • z) = r.generator z / (τ z : ℂ) := by
  have h4 : E₄ (τ (Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 4 * E₄ (τ z) := by
    simpa only [zpow_ofNat] using modularForm_generatorTwo E₄ hτc z
  have hD : discriminant (τ (Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ 12 * discriminant (τ z) := by
    have h :=
      modularForm_generatorTwo (CuspForm.discriminant : ModularForm 𝒮ℒ 12) hτc z
    change discriminant (τ (Triangle.generatorTwoSL • z)) =
      (τ z : ℂ) ^ (12 : ℤ) * discriminant (τ z) at h
    simpa only [zpow_ofNat] using h
  rw [generator, h4, hD,
    eisensteinSix_root_generatorTwo hτ hτc r.holomorphic r.square horder z]
  dsimp only [generator]
  field_simp [(τ z).ne_zero, discriminant_ne_zero (τ z)]

/-- The quotient of a section by the genuine generator is first-generator
invariant, without removing any zeros of the generator. -/
theorem quotient_generatorOne {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) (z : ℍ) :
    ν (Triangle.generatorOneSL • z) / r.generator (Triangle.generatorOneSL • z) =
      ν z / r.generator z := by
  rw [hν₁, r.generator_generatorOne hτ hτc,
    div_div_div_cancel_right₀ (τ z).ne_zero, neg_div_neg_eq]

/-- The analogous pointwise quotient invariance for the second generator. -/
theorem quotient_generatorTwo {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (horder : analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1)
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) (z : ℍ) :
    ν (Triangle.generatorTwoSL • z) / r.generator (Triangle.generatorTwoSL • z) =
      ν z / r.generator z := by
  rw [hν₂, r.generator_generatorTwo hτ hτc horder,
    div_div_div_cancel_right₀ (τ z).ne_zero]

/-- The pointwise quotient of any homogeneous section by the actual
Eisenstein generator is invariant under every actual triangle-group element. -/
theorem quotient_triangle {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hτc : TauCovariant τ)
    (horder : analyticOrderAt (r ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ))
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ))
    (g : TriangleGroup) (z : ℍ) :
    ν (triangleGeometricRepresentation g z) /
        r.generator (triangleGeometricRepresentation g z) = ν z / r.generator z :=
  triangle_invariant_of_generators (fun w => ν w / r.generator w)
    (r.quotient_generatorOne hτ hτc hν₁)
    (r.quotient_generatorTwo hτ hτc horder hν₂) g z

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
