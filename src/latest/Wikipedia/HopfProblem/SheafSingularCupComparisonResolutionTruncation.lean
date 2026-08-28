import Wikipedia.HopfProblem.SheafSingularCupComparisonResolutionBasic
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonLowExtMaps

/-!
# The original first four terms of an actual cochain resolution

The partial resolution contains exactly the original augmentation and
the first four original terms and differentials. Its kernel truncation
is definitionally the already constructed cochain-resolution truncation.
Original augmented cochain maps likewise retain every original component.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution

open SheafCupProductResolution ConstantSheafSingularComparison.LowExt

universe v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The first four actual terms, with no altered differential or comparison. -/
def ofCochain (R : CochainResolution C) : PartialResolution C where
  F := R.F
  I₀ := R.K.X 0
  I₁ := R.K.X 1
  I₂ := R.K.X 2
  I₃ := R.K.X 3
  ι := R.ι
  d₀ := R.K.d 0 1
  d₁ := R.K.d 1 2
  d₂ := R.K.d 2 3
  ι_d₀ := R.zero
  d₀_d₁ := R.K.d_comp_d 0 1 2
  d₁_d₂ := R.K.d_comp_d 1 2 3
  exact₀ := R.initial_exact
  exact₁ := (R.K.exactAt_iff' 0 1 2
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))).mp R.exact_one
  exact₂ := (R.K.exactAt_iff' 1 2 3
    ((ComplexShape.up ℕ).prev_eq' (by rfl))
    ((ComplexShape.up ℕ).next_eq' (by rfl))).mp R.exact_two
  mono_ι := R.mono_ι

@[simp] theorem ofCochain_oneComplex (R : CochainResolution C) :
    (ofCochain R).oneComplex = R.K.sc' 0 1 2 := rfl

@[simp] theorem ofCochain_twoComplex (R : CochainResolution C) :
    (ofCochain R).twoComplex = R.K.sc' 1 2 3 := rfl

@[simp] theorem ofCochain_toCyclesTwo (R : CochainResolution C) :
    (ofCochain R).toCyclesTwo = R.toCycles₂ := rfl

/-- The two original kernel truncations are definitionally identical. -/
@[simp] theorem ofCochain_toAugmented (R : CochainResolution C) :
    (ofCochain R).toAugmented = R.truncation := rfl

@[simp] theorem ofCochain_truncationInclusion (R : CochainResolution C) :
    (ofCochain R).truncationInclusion = R.shortInclusion := rfl

/-- An original augmented cochain map, restricted to its original first four terms. -/
def ofCochainHom {R S : CochainResolution C} (φ : R.Hom S) :
    (ofCochain R).Hom (ofCochain S) where
  augmentation := φ.augmentation
  τ₀ := φ.complex.f 0
  τ₁ := φ.complex.f 1
  τ₂ := φ.complex.f 2
  τ₃ := φ.complex.f 3
  commι := φ.comm
  comm₀ := φ.complex.comm 0 1
  comm₁ := φ.complex.comm 1 2
  comm₂ := φ.complex.comm 2 3

@[simp] theorem ofCochainHom_toAugmentedHom {R S : CochainResolution C} (φ : R.Hom S) :
    (ofCochainHom φ).toAugmentedHom = φ.truncationMap := rfl

end Wikipedia.HopfProblem.SheafSingularCupComparison.Resolution
