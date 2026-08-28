import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionExt

/-!
# Actual Ext comparisons from short exact sequences

These elementary consequences of the genuine Ext long exact sequence
will be applied to cycles and boundaries of the pushed injective complex.
All maps are induced by the original short-exact-sequence arrows.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.SheafLerayCurve.ExtComparison

universe u

variable {C : Type u} [Category.{0} C] [Abelian C] [HasExt.{0} C]
  (A : C) {S : ShortComplex C} (hS : S.ShortExact) (p : ℕ)

include hS in
/-- Vanishing of the left Ext group makes the actual right map injective. -/
theorem rightMap_injective [Subsingleton (Ext A S.X₁ p)] :
    Function.Injective ((Ext.mk₀ S.g).postcomp A (add_zero p)) := by
  rw [← AddMonoidHom.ker_eq_bot_iff, AddSubgroup.eq_bot_iff_forall]
  intro x hx
  obtain ⟨y, hy⟩ := Ext.covariant_sequence_exact₂ A hS x hx
  have hy0 : y = 0 := Subsingleton.elim _ _
  simpa only [hy0, Ext.zero_comp] using hy.symm

include hS in
/-- Vanishing of the next left Ext group makes the actual right map surjective. -/
theorem rightMap_surjective [Subsingleton (Ext A S.X₁ (p + 1))] :
    Function.Surjective ((Ext.mk₀ S.g).postcomp A (add_zero p)) := by
  intro x
  exact Ext.covariant_sequence_exact₃ A hS x rfl (Subsingleton.elim _ _)

/-- When both adjacent left Ext groups vanish, the original map becomes
an additive equivalence, without changing either Ext group. -/
def rightMapEquiv [Subsingleton (Ext A S.X₁ p)]
    [Subsingleton (Ext A S.X₁ (p + 1))] : Ext A S.X₂ p ≃+ Ext A S.X₃ p :=
  AddEquiv.ofBijective ((Ext.mk₀ S.g).postcomp A (add_zero p))
    ⟨rightMap_injective A hS p, rightMap_surjective A hS p⟩

@[simp] theorem rightMapEquiv_apply [Subsingleton (Ext A S.X₁ p)]
    [Subsingleton (Ext A S.X₁ (p + 1))] (x : Ext A S.X₂ p) :
    rightMapEquiv A hS p x = x.comp (Ext.mk₀ S.g) (add_zero p) := rfl

include hS in
/-- Vanishing of the two outer Ext groups forces the middle one to vanish. -/
theorem middle_subsingleton [Subsingleton (Ext A S.X₁ p)]
    [Subsingleton (Ext A S.X₃ p)] : Subsingleton (Ext A S.X₂ p) := by
  let f := (Ext.mk₀ S.g).postcomp A (add_zero p)
  exact ⟨fun x y => rightMap_injective A hS p (Subsingleton.elim (f x) (f y))⟩

/-- Actual isomorphisms of coefficients preserve vanishing of native Ext. -/
theorem subsingleton_of_iso {B D : C} (e : B ≅ D) (p : ℕ)
    [Subsingleton (Ext A D p)] : Subsingleton (Ext A B p) := by
  let e' : Ext A B p ≃+ Ext A D p :=
    ((extFunctorObj A p).mapIso e).addCommGroupIsoToAddEquiv
  exact ⟨fun x y => e'.injective (Subsingleton.elim (e' x) (e' y))⟩

end Wikipedia.HopfProblem.SheafLerayCurve.ExtComparison
