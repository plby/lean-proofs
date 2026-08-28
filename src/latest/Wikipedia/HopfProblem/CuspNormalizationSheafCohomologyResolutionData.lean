import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExt

/-!
# Splitting a length-two augmented resolution

The only data are actual objects, arrows and exactness. Splitting at
the kernel of the last arrow produces two genuine short exact sequences.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution

universe v u

/-- An actual exact sequence `0 → F → A → B → D → 0`. -/
structure AugmentedResolution (C : Type u) [Category.{v} C] [Abelian C] where
  F : C
  complex : ShortComplex C
  ι : F ⟶ complex.X₁
  zero : ι ≫ complex.f = 0
  initial_exact : (ShortComplex.mk ι complex.f zero).Exact
  exact : complex.Exact
  mono_ι : Mono ι
  epi_g : Epi complex.g

namespace AugmentedResolution

variable {C : Type u} [Category.{v} C] [Abelian C] (R : AugmentedResolution C)

attribute [instance] mono_ι epi_g

/-- The actual intermediate sheaf, the kernel of the last differential. -/
abbrev K : C := kernel R.complex.g

/-- The first differential with codomain restricted to the actual kernel. -/
def toK : R.complex.X₁ ⟶ R.K :=
  kernel.lift R.complex.g R.complex.f R.complex.zero

@[reassoc (attr := simp)] theorem toK_ι :
    R.toK ≫ kernel.ι R.complex.g = R.complex.f :=
  kernel.lift_ι _ _ _

theorem ι_toK : R.ι ≫ R.toK = 0 := by
  rw [← cancel_mono (kernel.ι R.complex.g), Category.assoc, toK_ι,
    R.zero, zero_comp]

/-- The first of the two actual short exact sequences. -/
abbrev first : ShortComplex C :=
  ShortComplex.mk R.ι R.toK R.ι_toK

/-- The second of the two actual short exact sequences. -/
abbrev second : ShortComplex C :=
  ShortComplex.mk (kernel.ι R.complex.g) R.complex.g (kernel.condition R.complex.g)

theorem first_shortExact : R.first.ShortExact where
  exact := by
    let φ : R.first ⟶ ShortComplex.mk R.ι R.complex.f R.zero :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := kernel.ι R.complex.g
        comm₁₂ := by simp [first]
        comm₂₃ := by simp [first] }
    have : Epi φ.τ₁ := inferInstanceAs (Epi (𝟙 R.F))
    have : IsIso φ.τ₂ := inferInstanceAs (IsIso (𝟙 R.complex.X₁))
    have : Mono φ.τ₃ := inferInstanceAs (Mono (kernel.ι R.complex.g))
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mpr R.initial_exact
  mono_f := R.mono_ι
  epi_g := R.exact.epi_kernelLift

theorem second_shortExact : R.second.ShortExact where
  exact := (R.second).exact_of_f_is_kernel (kernelIsKernel R.complex.g)
  mono_f := by dsimp [second]; infer_instance
  epi_g := R.epi_g

end AugmentedResolution

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyResolution
