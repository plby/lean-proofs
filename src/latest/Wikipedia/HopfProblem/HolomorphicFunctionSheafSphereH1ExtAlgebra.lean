import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives

/-!
# An Ext vanishing criterion for an injective short exact sequence

For a short exact sequence with injective middle object, surjectivity
on morphisms from a fixed object forces its first covariant Ext group
to vanish.  This is the actual Ext long exact sequence, independently
of any sheaf or Čech comparison.
-/

universe w v u

open CategoryTheory
open CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

/-- If every morphism from `X` to the last object lifts to the injective
middle object, then every degree-one Ext class from `X` to the first
object is zero.  The `HasExt` universe is the given one. -/
theorem subsingleton_ext_one_of_shortExact (X : C) {S : ShortComplex C}
    (hS : S.ShortExact) [Injective S.X₂]
    (hsurj : Function.Surjective (fun f : X ⟶ S.X₂ => f ≫ S.g)) :
    Subsingleton (Ext.{w} X S.X₁ 1) := by
  refine subsingleton_of_forall_eq 0 ?_
  intro e
  obtain ⟨e₀, he₀⟩ := Ext.covariant_sequence_exact₁ X hS e
    (Ext.eq_zero_of_injective _) (n₀ := 0) rfl
  obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective X S.X₃).surjective e₀
  obtain ⟨g, rfl⟩ := hsurj f
  rw [← he₀, ← Ext.mk₀_comp_mk₀, Ext.comp_assoc_of_second_deg_zero,
    ShortComplex.ShortExact.comp_extClass, Ext.comp_zero]

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
