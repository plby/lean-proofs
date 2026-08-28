import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionData
import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Truncating an actual cochain resolution in degree two

The last term is the categorical kernel of the genuine degree-two
differential. Exactness makes the incoming differential epimorphic.
No cohomology comparison or acyclicity is part of the data below.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt

open CuspNormalization.SheafCohomologyResolution

universe v u

/-- An augmented cochain complex, exact in the degrees needed for the
degree-one and degree-two sheaf-cohomology comparisons. -/
structure CochainResolution (C : Type u) [Category.{v} C] [Abelian C] where
  F : C
  K : CochainComplex C ℕ
  ι : F ⟶ K.X 0
  zero : ι ≫ K.d 0 1 = 0
  initial_exact : (ShortComplex.mk ι (K.d 0 1) zero).Exact
  exact_one : K.ExactAt 1
  exact_two : K.ExactAt 2
  mono_ι : Mono ι

namespace CochainResolution

variable {C : Type u} [Category.{v} C] [Abelian C] (R : CochainResolution C)

attribute [instance] mono_ι

/-- The actual cycles in degree two, presented as a categorical kernel. -/
abbrev cycles₂ : C := kernel (R.K.d 2 3)

/-- The differential with codomain restricted to its genuine cycles. -/
def toCycles₂ : R.K.X 1 ⟶ R.cycles₂ :=
  kernel.lift (R.K.d 2 3) (R.K.d 1 2) (R.K.d_comp_d 1 2 3)

@[reassoc (attr := simp)] theorem toCycles₂_ι :
    R.toCycles₂ ≫ kernel.ι (R.K.d 2 3) = R.K.d 1 2 :=
  kernel.lift_ι _ _ _

theorem d_toCycles₂ : R.K.d 0 1 ≫ R.toCycles₂ = 0 := by
  apply (cancel_mono (kernel.ι (R.K.d 2 3))).mp
  simp only [Category.assoc, toCycles₂_ι, R.K.d_comp_d, zero_comp]

/-- The actual three terms `K⁰ → K¹ → ker(d²)`. -/
def shortComplex : ShortComplex C :=
  ShortComplex.mk (R.K.d 0 1) R.toCycles₂ R.d_toCycles₂

/-- The truncation includes into the genuine three-term cochain complex. -/
def shortInclusion : R.shortComplex ⟶ R.K.sc' 0 1 2 where
  τ₁ := 𝟙 _
  τ₂ := 𝟙 _
  τ₃ := kernel.ι (R.K.d 2 3)
  comm₁₂ := (Category.id_comp _).trans (Category.comp_id _).symm
  comm₂₃ := (Category.id_comp _).trans R.toCycles₂_ι.symm

theorem shortComplex_exact : R.shortComplex.Exact := by
  have : Epi R.shortInclusion.τ₁ := inferInstanceAs (Epi (𝟙 (R.K.X 0)))
  have : IsIso R.shortInclusion.τ₂ := inferInstanceAs (IsIso (𝟙 (R.K.X 1)))
  have : Mono R.shortInclusion.τ₃ := inferInstanceAs (Mono (kernel.ι (R.K.d 2 3)))
  apply (ShortComplex.exact_iff_of_epi_of_isIso_of_mono R.shortInclusion).mpr
  exact (R.K.exactAt_iff' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))).mp R.exact_one

instance toCycles₂_epi : Epi R.toCycles₂ := by
  have h : (R.K.sc' 1 2 3).Exact :=
    (R.K.exactAt_iff' 1 2 3
      ((ComplexShape.up ℕ).prev_eq' (by rfl))
      ((ComplexShape.up ℕ).next_eq' (by rfl))).mp R.exact_two
  exact h.epi_kernelLift

/-- A genuine exact length-two resolution obtained by truncation. -/
def truncation : AugmentedResolution C where
  F := R.F
  complex := R.shortComplex
  ι := R.ι
  zero := R.zero
  initial_exact := R.initial_exact
  exact := R.shortComplex_exact
  mono_ι := R.mono_ι
  epi_g := R.toCycles₂_epi

end CochainResolution

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.LowExt
