import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData

/-!
# An actual partial resolution and its genuine kernel truncation

Exactness is required at the original augmentation and at all three
intermediate objects. The last target of the bounded resolution is the
actual kernel of the final differential. Surjectivity onto that kernel
is proved from the original exactness, not included as a comparison premise.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafCupProductResolution

open CuspNormalization.SheafCohomologyResolution

universe v u

/-- Genuine partial resolution data, before imposing injectivity of its terms. -/
structure PartialResolution (C : Type u) [Category.{v} C] [Abelian C] where
  F : C
  I₀ : C
  I₁ : C
  I₂ : C
  I₃ : C
  ι : F ⟶ I₀
  d₀ : I₀ ⟶ I₁
  d₁ : I₁ ⟶ I₂
  d₂ : I₂ ⟶ I₃
  ι_d₀ : ι ≫ d₀ = 0
  d₀_d₁ : d₀ ≫ d₁ = 0
  d₁_d₂ : d₁ ≫ d₂ = 0
  exact₀ : (ShortComplex.mk ι d₀ ι_d₀).Exact
  exact₁ : (ShortComplex.mk d₀ d₁ d₀_d₁).Exact
  exact₂ : (ShortComplex.mk d₁ d₂ d₁_d₂).Exact
  mono_ι : Mono ι

namespace PartialResolution

variable {C : Type u} [Category.{v} C] [Abelian C] (R : PartialResolution C)

attribute [instance] mono_ι

/-- The original three terms computing degree one. -/
abbrev oneComplex : ShortComplex C := ShortComplex.mk R.d₀ R.d₁ R.d₀_d₁

/-- The original three terms computing degree two. -/
abbrev twoComplex : ShortComplex C := ShortComplex.mk R.d₁ R.d₂ R.d₁_d₂

/-- The genuine sheaf of degree-two cocycles. -/
abbrev Z₂ : C := kernel R.d₂

/-- The original differential factored through its actual cycle object. -/
def toCyclesTwo : R.I₁ ⟶ R.Z₂ := kernel.lift R.d₂ R.d₁ R.d₁_d₂

@[reassoc (attr := simp)] theorem toCyclesTwo_ι :
    R.toCyclesTwo ≫ kernel.ι R.d₂ = R.d₁ := kernel.lift_ι _ _ _

theorem d₀_toCyclesTwo : R.d₀ ≫ R.toCyclesTwo = 0 := by
  rw [← cancel_mono (kernel.ι R.d₂), Category.assoc, toCyclesTwo_ι,
    R.d₀_d₁, zero_comp]

/-- Actual exactness at the last original term makes this kernel factor an epimorphism. -/
instance toCyclesTwo_epi : Epi R.toCyclesTwo := R.exact₂.epi_kernelLift

/-- The original first differential and the actual kernel factor of the second. -/
def truncatedComplex : ShortComplex C :=
  ShortComplex.mk R.d₀ R.toCyclesTwo R.d₀_toCyclesTwo

/-- Exactness survives the actual monomorphic change of the last target. -/
theorem truncatedComplex_exact : R.truncatedComplex.Exact := by
  let φ : R.truncatedComplex ⟶ R.oneComplex :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := kernel.ι R.d₂
      comm₁₂ := by simp [truncatedComplex]
      comm₂₃ := by simp [truncatedComplex] }
  have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 R.I₀))
  have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 R.I₁))
  have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι R.d₂))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr R.exact₁

/-- The genuine bounded augmented resolution produced by kernel truncation. -/
def toAugmented : AugmentedResolution C where
  F := R.F
  complex := R.truncatedComplex
  ι := R.ι
  zero := R.ι_d₀
  initial_exact := R.exact₀
  exact := R.truncatedComplex_exact
  mono_ι := R.mono_ι
  epi_g := R.toCyclesTwo_epi

end PartialResolution

end Wikipedia.HopfProblem.SheafCupProductResolution
