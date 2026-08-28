import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorOrders
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorTransform
import Wikipedia.HopfProblem.SpecialPeriodsMuGeneratorLocalDivision

/-!
# Construction of the actual homogeneous μ-generator

The proved analytic root covering, modular forms, local lift orders, and
forced root signs construct the source's homogeneous function.  The input
is a genuine holomorphic `τ` with its two covariance equations; existence
of that map is not asserted here.  A second theorem obtains all required
root and lift-order hypotheses from an actual modular lifting equation.

At both elliptic points every homogeneous holomorphic numerator admits an
analytic factorization by this very generator, not an unrelated model.
-/

noncomputable section

open Set Filter UpperHalfPlane
open scoped Topology Manifold ContDiff

namespace Wikipedia.HopfProblem.SpecialPeriods.MuGenerator

/-- The two homogeneous equations from the source, for the actual generators. -/
def Homogeneous (τ : ℍ → ℍ) (F : ℍ → ℂ) : Prop :=
  (∀ z, F (Triangle.generatorOneSL • z) = -F z / (τ z : ℂ)) ∧
  (∀ z, F (Triangle.generatorTwoSL • z) = F z / (τ z : ℂ))

namespace Root

variable {τ : ℍ → ℍ} (r : Root τ)

/-- For the source normalization `j ∘ τ = 1728π`, the zeros are exactly
the actual zero and one fibres of `π`.  Orbit identification is not inferred
from local orders alone. -/
theorem generator_eq_zero_iff_normalized_source {π : ℍ → ℂ}
    (hJ : ∀ z, modularJ (τ z) = 1728 * π z) (z : ℍ) :
    r.generator z = 0 ↔ π z = 0 ∨ π z = 1 := by
  rw [r.generator_eq_zero_iff_modularJ, hJ z]
  have h1728 : (1728 : ℂ) ≠ 0 := by norm_num
  constructor
  · rintro (h | h)
    · exact Or.inl ((mul_eq_zero.mp h).resolve_left h1728)
    · right
      apply mul_left_cancel₀ h1728
      simpa only [mul_one] using h
  · rintro (h | h)
    · left
      rw [h, mul_zero]
    · right
      rw [h, mul_one]

theorem generator_homogeneous
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) :
    Homogeneous τ r.generator :=
  ⟨r.generator_generatorOne hτ hc,
    r.generator_generatorTwo hτ hc (r.order_centerTwo_of_tau_order hτ hc ho₂)⟩

/-- Every homogeneous numerator has a genuine analytic quotient germ by
the constructed generator at the order-three centre. -/
theorem local_division_centerOne
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₁ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    {ν : ℍ → ℂ} (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hνc : Homogeneous τ ν) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerOne : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerOne : ℂ)]
        fun z => (r.generator ∘ ofComplex) z * h z :=
  exists_division_at_centerOne hτ hc hν hνc.1 (r.generator_holomorphic hτ)
    (r.generator_order_centerOne_of_tau_order hτ hc ho₁)

/-- The analogous analytic quotient germ at the order-four centre. -/
theorem local_division_centerTwo
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2)
    {ν : ℍ → ℂ} (hν : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω ν) (hνc : Homogeneous τ ν) :
    ∃ h : ℂ → ℂ, AnalyticAt ℂ h (Triangle.centerTwo : ℂ) ∧
      (ν ∘ ofComplex) =ᶠ[𝓝 (Triangle.centerTwo : ℂ)]
        fun z => (r.generator ∘ ofComplex) z * h z :=
  exists_division_at_centerTwo hν hνc.2 (r.generator_holomorphic hτ)
    (r.generator_order_centerTwo_of_tau_order hτ hc ho₂)

/-- The actual quotient by the generator is invariant under every group
element; this pointwise statement is separate from removable extension. -/
theorem quotient_invariant
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2)
    {ν : ℍ → ℂ} (hνc : Homogeneous τ ν) (g : TriangleGroup) (z : ℍ) :
    ν (triangleGeometricRepresentation g z) /
        r.generator (triangleGeometricRepresentation g z) = ν z / r.generator z :=
  r.quotient_triangle hτ hc (r.order_centerTwo_of_tau_order hτ hc ho₂) hνc.1 hνc.2 g z

end Root

/-- The source's homogeneous function is constructed from the actual
modular forms and a proved global square root. -/
theorem exists_homogeneous_generator {τ : ℍ → ℍ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (heven : FiniteEvenZeros τ)
    (ho₁ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - rho)
      (Triangle.centerOne : ℂ) = 1)
    (ho₂ : analyticOrderAt (fun z : ℂ => (τ (ofComplex z) : ℂ) - Complex.I)
      (Triangle.centerTwo : ℂ) = 2) :
    ∃ F : ℍ → ℂ, (∃ r : Root τ, F = r.generator) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧ Homogeneous τ F ∧
      (∀ z, F z = 0 ↔ modularJ (τ z) = 0 ∨ modularJ (τ z) = 1728) ∧
      analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2 ∧
      analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1 := by
  let r := root τ (hτ.mdifferentiable (by simp)) heven
  exact ⟨r.generator, ⟨r, rfl⟩, r.generator_holomorphic hτ,
    r.generator_homogeneous hτ hc ho₂, r.generator_eq_zero_iff_modularJ,
    r.generator_order_centerOne_of_tau_order hτ hc ho₁,
    r.generator_order_centerTwo_of_tau_order hτ hc ho₂⟩

/-- An actual modular equation with source orders three and four supplies
the finite even zeros and both lift orders needed in the construction. -/
theorem exists_homogeneous_generator_of_modular_equation
    {τ : ℍ → ℍ} {J : ℍ → ℂ}
    (hτ : ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω τ) (hc : TauCovariant τ)
    (hJ : ∀ a : ℍ, modularJ (τ a) = J a)
    (hzero : ∀ a : ℍ, J a = 0 → analyticOrderAt (J ∘ ofComplex) (a : ℂ) = 3)
    (h1728 : ∀ a : ℍ, J a = 1728 →
      analyticOrderAt (fun z : ℂ => J (ofComplex z) - 1728) (a : ℂ) = 4) :
    ∃ F : ℍ → ℂ, (∃ r : Root τ, F = r.generator) ∧
      ContMDiff 𝓘(ℂ) 𝓘(ℂ) ω F ∧ Homogeneous τ F ∧
      (∀ z, F z = 0 ↔ J z = 0 ∨ J z = 1728) ∧
      analyticOrderAt (F ∘ ofComplex) (Triangle.centerOne : ℂ) = 2 ∧
      analyticOrderAt (F ∘ ofComplex) (Triangle.centerTwo : ℂ) = 1 := by
  have hτd := hτ.mdifferentiable (by simp)
  have heven : FiniteEvenZeros τ :=
    finiteEvenZeros_of_modular_equation hτd hJ
      (fun a ha => ⟨1, by simpa only [Nat.mul_one, Nat.cast_ofNat] using h1728 a ha⟩)
  have hJ₁ : J Triangle.centerOne = 0 := by
    rw [← hJ, (tau_covariant_values hc).1, modularJ_rhoPoint]
  have hJ₂ : J Triangle.centerTwo = 1728 := by
    rw [← hJ, (tau_covariant_values hc).2, modularJ_I]
  have ho₁ := ModularGermLift.native_modularJ_lift_order_of_zero hτd hJ
    (a := Triangle.centerOne) (n := 1) hJ₁
    (by simpa only [Nat.mul_one, Nat.cast_ofNat] using hzero Triangle.centerOne hJ₁)
  rw [(tau_covariant_values hc).1, coe_rhoPoint] at ho₁
  have ho₂ := ModularGermLift.native_modularJ_lift_order_of_1728 hτd hJ
    (a := Triangle.centerTwo) (n := 2) hJ₂ (by simpa using h1728 Triangle.centerTwo hJ₂)
  rw [(tau_covariant_values hc).2, coe_I] at ho₂
  obtain ⟨F, hFroot, hF, hFc, hFzero, hF₁, hF₂⟩ :=
    exists_homogeneous_generator hτ hc heven ho₁ ho₂
  exact ⟨F, hFroot, hF, hFc, fun z => by rw [hFzero z, hJ z], hF₁, hF₂⟩

end Wikipedia.HopfProblem.SpecialPeriods.MuGenerator
