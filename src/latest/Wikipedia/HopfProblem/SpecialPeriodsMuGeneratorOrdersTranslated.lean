import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorConstruction
import Wikipedia.HopfProblem.SpecialPeriodsTriangleQuotientOrdersTranslated

/-!
# Exact orders of homogeneous sections along actual triangle orbits

The homogeneous generator multipliers are analytic and nowhere zero.
Multiplication by them preserves analytic order, while the actual source
matrices give analytic changes of coordinate. Thus the order of every
holomorphic homogeneous section is constant along each triangle orbit,
including when that order is infinite.

Applied to the constructed Eisenstein generator, this transports its exact
orders two and one to every translate of the two elliptic centers. No
classification of other fibers or existence of a global special map is
presumed.
-/

noncomputable section

open UpperHalfPlane
open scoped Topology ContDiff Manifold MatrixGroups

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- Division by a holomorphic upper-half-plane-valued function is division
by an analytic unit, and therefore leaves the order unchanged. -/
theorem scalar_order_div_upperHalfPlane {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (a : ℍ) :
    analyticOrderAt (fun z : ℂ => ν (ofComplex z) / (τ (ofComplex z) : ℂ)) (a : ℂ) =
      analyticOrderAt (ν ∘ ofComplex) (a : ℂ) := by
  let T : ℂ → ℂ := fun z => (τ (ofComplex z) : ℂ)
  have hT : AnalyticAt ℂ T (a : ℂ) :=
    scalar_analyticAt (UpperHalfPlane.contMDiff_coe.comp hτ) a
  have hT0 : T (a : ℂ) ≠ 0 := by
    simpa only [T, ofComplex_apply] using (τ a).ne_zero
  have hI : AnalyticAt ℂ T⁻¹ (a : ℂ) := hT.inv hT0
  have hIo : analyticOrderAt T⁻¹ (a : ℂ) = 0 :=
    hI.analyticOrderAt_eq_zero.mpr (inv_ne_zero hT0)
  have he : (fun z : ℂ => ν (ofComplex z) / (τ (ofComplex z) : ℂ)) =
      (ν ∘ ofComplex) * T⁻¹ := by
    funext z
    exact div_eq_mul_inv _ _
  rw [he, analyticOrderAt_mul (scalar_analyticAt hν a) hI, hIo, add_zero]

/-- The negative first-generator homogeneous law preserves the exact
ambient analytic order at every point. -/
theorem homogeneous_order_generatorOne {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₁ : ∀ z : ℍ, ν (Triangle.generatorOneSL • z) = -ν z / (τ z : ℂ)) (a : ℍ) :
    analyticOrderAt (ν ∘ ofComplex) ((Triangle.generatorOneSL • a : ℍ) : ℂ) =
      analyticOrderAt (ν ∘ ofComplex) (a : ℂ) := by
  have he : (fun z : ℂ => ν (Triangle.generatorOneSL • ofComplex z)) =
      -(fun z : ℂ => ν (ofComplex z) / (τ (ofComplex z) : ℂ)) := by
    funext z
    simpa only [Pi.neg_apply, neg_div] using hν₁ (ofComplex z)
  rw [← Triangle.sl_analyticOrderAt_comp_smul ν Triangle.generatorOneSL a,
    he, analyticOrderAt_neg]
  exact scalar_order_div_upperHalfPlane hτ hν a

/-- The positive second-generator homogeneous law also preserves order. -/
theorem homogeneous_order_generatorTwo {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hν₂ : ∀ z : ℍ, ν (Triangle.generatorTwoSL • z) = ν z / (τ z : ℂ)) (a : ℍ) :
    analyticOrderAt (ν ∘ ofComplex) ((Triangle.generatorTwoSL • a : ℍ) : ℂ) =
      analyticOrderAt (ν ∘ ofComplex) (a : ℂ) := by
  have he : (fun z : ℂ => ν (Triangle.generatorTwoSL • ofComplex z)) =
      (fun z : ℂ => ν (ofComplex z) / (τ (ofComplex z) : ℂ)) := by
    funext z
    exact hν₂ (ofComplex z)
  rw [← Triangle.sl_analyticOrderAt_comp_smul ν Triangle.generatorTwoSL a, he]
  exact scalar_order_div_upperHalfPlane hτ hν a

private theorem triangle_invariant_of_generators_any {Y : Type*} (f : ℍ → Y)
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

/-- The exact analytic order of a holomorphic homogeneous section is
constant on every actual triangle-group orbit, including infinite orders. -/
theorem homogeneous_order_triangle {τ : ℍ → ℍ} {ν : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν)
    (hνc : Homogeneous τ ν) (g : TriangleGroup) (a : ℍ) :
    analyticOrderAt (ν ∘ ofComplex) (triangleGeometricRepresentation g a : ℂ) =
      analyticOrderAt (ν ∘ ofComplex) (a : ℂ) :=
  triangle_invariant_of_generators_any
    (fun w : ℍ => analyticOrderAt (ν ∘ ofComplex) (w : ℂ))
    (homogeneous_order_generatorOne hτ hν hνc.1)
    (homogeneous_order_generatorTwo hτ hν hνc.2) g a

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

/-- The actual Eisenstein generator has invariant order along every
triangle orbit once its proved second-generator sign is available. -/
theorem generator_order_triangle
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) (g : TriangleGroup) (a : ℍ) :
    analyticOrderAt (r.generator ∘ ofComplex) (triangleGeometricRepresentation g a : ℂ) =
      analyticOrderAt (r.generator ∘ ofComplex) (a : ℂ) :=
  homogeneous_order_triangle hτ (r.generator_holomorphic hτ)
    (r.generator_homogeneous hτ hc ho₂) g a

/-- Every actual translate of the first elliptic center is a zero of
exact order two of the constructed Eisenstein generator. -/
theorem generator_order_translated_centerOne
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₁ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) (g : TriangleGroup) :
    analyticOrderAt (r.generator ∘ ofComplex)
      (triangleGeometricRepresentation g Triangle.centerOne : ℂ) = 2 :=
  (r.generator_order_triangle hτ hc ho₂ g Triangle.centerOne).trans
    (r.generator_order_centerOne_of_tau_order hτ hc ho₁)

/-- Every actual translate of the second elliptic center is a simple
zero of the constructed Eisenstein generator. -/
theorem generator_order_translated_centerTwo
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) (g : TriangleGroup) :
    analyticOrderAt (r.generator ∘ ofComplex)
      (triangleGeometricRepresentation g Triangle.centerTwo : ℂ) = 1 :=
  (r.generator_order_triangle hτ hc ho₂ g Triangle.centerTwo).trans
    (r.generator_order_centerTwo_of_tau_order hτ hc ho₂)

end Root

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
