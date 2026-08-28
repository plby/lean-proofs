import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences

/-!
# Vanishing of the actual extension class and splitting

The degree-zero terms of the genuine long exact Ext sequences detect whether
the identity of either endpoint lifts.  Consequently the actual Ext class of
a short exact sequence vanishes exactly when the sequence has a section, a
retraction, or a splitting.  No enough-injectives hypothesis is needed.
-/

universe w v u

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]
  {S : ShortComplex C}

/-- Vanishing of the actual extension class is equivalent to a section of
the epimorphism in the given short exact sequence. -/
theorem extClass_eq_zero_iff_exists_section (hS : S.ShortExact) :
    (hS.extClass : Ext.{w} S.X₃ S.X₁ 1) = 0 ↔
      ∃ s : S.X₃ ⟶ S.X₂, s ≫ S.g = 𝟙 S.X₃ := by
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ S.X₃ hS
      (Ext.mk₀ (𝟙 S.X₃)) (zero_add 1) (by simp only [h, Ext.comp_zero])
    obtain ⟨s, rfl⟩ := (Ext.mk₀_bijective S.X₃ S.X₂).surjective x₂
    refine ⟨s, ?_⟩
    apply (Ext.mk₀_bijective S.X₃ S.X₃).injective
    simpa only [Ext.mk₀_comp_mk₀] using hx₂
  · rintro ⟨s, hs⟩
    have h := congrArg
      (fun e : Ext.{w} S.X₂ S.X₁ 1 => (Ext.mk₀ s).comp e (zero_add 1))
      hS.comp_extClass
    simpa only [Ext.mk₀_comp_mk₀_assoc, hs, Ext.mk₀_id_comp, Ext.comp_zero] using h

/-- The dual criterion uses the actual contravariant Ext connecting map. -/
theorem extClass_eq_zero_iff_exists_retraction (hS : S.ShortExact) :
    (hS.extClass : Ext.{w} S.X₃ S.X₁ 1) = 0 ↔
      ∃ r : S.X₂ ⟶ S.X₁, S.f ≫ r = 𝟙 S.X₁ := by
  constructor
  · intro h
    obtain ⟨x₂, hx₂⟩ := Ext.contravariant_sequence_exact₁ hS S.X₁
      (Ext.mk₀ (𝟙 S.X₁)) (add_zero 1) (by simp only [h, Ext.zero_comp])
    obtain ⟨r, rfl⟩ := (Ext.mk₀_bijective S.X₂ S.X₁).surjective x₂
    refine ⟨r, ?_⟩
    apply (Ext.mk₀_bijective S.X₁ S.X₁).injective
    simpa only [Ext.mk₀_comp_mk₀] using hx₂
  · rintro ⟨r, hr⟩
    have h := hS.extClass_comp_assoc (Ext.mk₀ r) (h := add_zero 1)
    simpa only [Ext.mk₀_comp_mk₀, hr, Ext.comp_mk₀_id] using h

/-- The splitting is Mathlib's actual compatible section-and-retraction
data for the original short complex. -/
theorem extClass_eq_zero_iff_nonempty_splitting (hS : S.ShortExact) :
    (hS.extClass : Ext.{w} S.X₃ S.X₁ 1) = 0 ↔ Nonempty S.Splitting := by
  constructor
  · intro h
    obtain ⟨s, hs⟩ := (extClass_eq_zero_iff_exists_section hS).mp h
    exact ⟨ShortComplex.Splitting.ofExactOfSection S hS.exact s hs hS.mono_f⟩
  · rintro ⟨σ⟩
    exact (extClass_eq_zero_iff_exists_section hS).mpr ⟨σ.s, σ.s_g⟩

end Wikipedia.HopfProblem.HolomorphicPicard.ExtExtensions
