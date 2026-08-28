import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExtClass

/-!
# Actual pullback extensions and their degree-one Ext classes

Pulling a short exact sequence back along a morphism to its quotient gives
another actual short exact sequence, with the same kernel.  Its Ext class
is computed by the naturality of mathlib's derived-category Ext class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

universe w v u

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- The actual pullback short complex, with its left endpoint unchanged. -/
abbrev pullbackComplex (S : ShortComplex C) {B : C} (a : B ⟶ S.X₃) : ShortComplex C where
  X₁ := S.X₁
  X₂ := pullback S.g a
  X₃ := B
  f := pullback.lift S.f 0 (by simp)
  g := pullback.snd S.g a
  zero := pullback.lift_snd _ _ _

/-- The canonical morphism from the pullback complex to the original one. -/
def pullbackComplexMap (S : ShortComplex C) {B : C} (a : B ⟶ S.X₃) :
    pullbackComplex S a ⟶ S where
  τ₁ := 𝟙 S.X₁
  τ₂ := pullback.fst S.g a
  τ₃ := a
  comm₁₂ := by simp only [pullbackComplex, Category.id_comp, pullback.lift_fst]
  comm₂₃ := pullback.condition

@[reassoc (attr := simp)]
theorem pullbackComplex_f_fst (S : ShortComplex C) {B : C} (a : B ⟶ S.X₃) :
    (pullbackComplex S a).f ≫ pullback.fst S.g a = S.f :=
  pullback.lift_fst _ _ _

/-- The pullback inclusion is mono whenever the original inclusion is mono. -/
theorem pullbackComplex_mono_f (S : ShortComplex C) [Mono S.f]
    {B : C} (a : B ⟶ S.X₃) : Mono (pullbackComplex S a).f :=
  mono_of_mono_fac (pullbackComplex_f_fst S a)

/-- The left endpoint is the genuine kernel of the pullback projection. -/
def pullbackComplex_fIsKernel {S : ShortComplex C} (hS : S.ShortExact)
    {B : C} (a : B ⟶ S.X₃) :
    IsLimit (KernelFork.ofι (pullbackComplex S a).f (pullbackComplex S a).zero) := by
  letI : Mono S.f := hS.mono_f
  letI : Mono (pullbackComplex S a).f := pullbackComplex_mono_f S a
  apply KernelFork.IsLimit.ofι'
  intro T k hk
  change k ≫ pullback.snd S.g a = 0 at hk
  have hk' : (k ≫ pullback.fst S.g a) ≫ S.g = 0 := by
    rw [Category.assoc, pullback.condition, ← Category.assoc, hk, zero_comp]
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hS.fIsKernel
    (k ≫ pullback.fst S.g a) hk'
  change l ≫ S.f = k ≫ pullback.fst S.g a at hl
  refine ⟨l, ?_⟩
  apply pullback.hom_ext
  · simpa only [Category.assoc, pullbackComplex, pullback.lift_fst] using hl
  · simpa only [Category.assoc, pullbackComplex, pullback.lift_snd, comp_zero] using hk.symm

/-- Pullback preserves the actual short exact sequence in an abelian category. -/
theorem pullbackComplex_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    {B : C} (a : B ⟶ S.X₃) : (pullbackComplex S a).ShortExact := by
  let : Mono S.f := hS.mono_f
  let : Epi S.g := hS.epi_g
  exact
    { exact := ShortComplex.exact_of_f_is_kernel _ (pullbackComplex_fIsKernel hS a)
      mono_f := pullbackComplex_mono_f S a
      epi_g := inferInstanceAs (Epi (pullback.snd S.g a)) }

/-- The class of the actual pullback extension is the contravariant pullback
of the original degree-one Ext class. -/
theorem pullbackComplex_extClass [HasExt.{w} C] {S : ShortComplex C}
    (hS : S.ShortExact) {B : C} (a : B ⟶ S.X₃) :
    ((pullbackComplex_shortExact hS a).extClass : Ext.{w} B S.X₁ 1) =
      (Ext.mk₀ a).comp hS.extClass (zero_add 1) := by
  have h := (pullbackComplex_shortExact hS a).extClass_naturality hS
    (pullbackComplexMap S a)
  change (pullbackComplex_shortExact hS a).extClass.comp (Ext.mk₀ (𝟙 S.X₁))
    (add_zero 1) = (Ext.mk₀ a).comp hS.extClass (zero_add 1) at h
  simpa only [Ext.comp_mk₀_id] using h

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
