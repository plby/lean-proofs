import Mathlib.Algebra.Homology.DerivedCategory.Ext.MapBijective

/-!
# An exact injective-preserving functor compares genuine Ext groups

Suppose an exact functor `R` preserves injectives and a morphism
`η : A ⟶ R(V)` identifies morphisms out of `V` with morphisms out of `A`.
The canonical map on Mathlib's actual Ext groups is then bijective in
every degree. The proof uses injective presentations, the genuine Ext
long exact sequence, and the additive five lemma.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

universe u v u' v' w w'

namespace Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward.ExtComparison

variable {C : Type u} [Category.{v} C] [Abelian C]
  {D : Type u'} [Category.{v'} D] [Abelian D]
  (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasExt.{w} C] [HasExt.{w'} D]
  {V : C} {A : D} (η : A ⟶ R.obj V)

/-- The genuine exact-functor map on Ext, preceded by the actual
degree-zero class of `η`. -/
def comparison (Y : C) (n : ℕ) : Ext.{w} V Y n →+ Ext.{w'} A (R.obj Y) n where
  toFun e := (Ext.mk₀ η).comp (e.mapExactFunctor R) (zero_add n)
  map_zero' := by simp
  map_add' e e' := by simp

/-- In degree zero the comparison is the literal map of morphisms. -/
theorem comparison_mk₀ {Y : C} (f : V ⟶ Y) :
    comparison R η Y 0 (Ext.mk₀ f) = Ext.mk₀ (η ≫ R.map f) := by
  change (Ext.mk₀ η).comp ((Ext.mk₀ f).mapExactFunctor R) (zero_add 0) = _
  rw [Ext.mapExactFunctor_mk₀, Ext.mk₀_comp_mk₀]

/-- The comparison commutes with the genuine covariant Ext maps. -/
theorem comparison_naturality {Y Z : C} (f : Y ⟶ Z) {n : ℕ} (e : Ext.{w} V Y n) :
    comparison R η Z n (e.comp (Ext.mk₀ f) (add_zero n)) =
      (comparison R η Y n e).comp (Ext.mk₀ (R.map f)) (add_zero n) := by
  simp only [comparison, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀, Ext.comp_assoc_of_third_deg_zero]

/-- The comparison commutes with the actual connecting Ext class of
every genuine short exact sequence. -/
theorem comparison_connecting {S : ShortComplex C} (hS : S.ShortExact)
    {n : ℕ} (e : Ext.{w} V S.X₃ n) :
    comparison R η S.X₁ (n + 1) (e.comp hS.extClass rfl) =
      (comparison R η S.X₃ n e).comp (hS.map_of_exact R).extClass rfl := by
  simp only [comparison, AddMonoidHom.coe_mk, ZeroHom.coe_mk,
    Ext.mapExactFunctor_comp, Ext.mapExactFunctor_extClass]
  exact (Ext.comp_assoc (Ext.mk₀ η) (e.mapExactFunctor R)
    (hS.map_of_exact R).extClass (zero_add n) rfl (by omega)).symm

/-- The actual degree-zero comparison is bijective whenever its
literal morphism map is bijective. -/
theorem comparison_zero_bijective
    (hη : ∀ Y : C, Function.Bijective (fun f : V ⟶ Y => η ≫ R.map f)) (Y : C) :
    Function.Bijective (comparison R η Y 0) := by
  constructor
  · intro e e' he
    obtain ⟨f, rfl⟩ := (Ext.mk₀_bijective V Y).surjective e
    obtain ⟨f', rfl⟩ := (Ext.mk₀_bijective V Y).surjective e'
    apply congrArg Ext.mk₀
    apply (hη Y).injective
    exact (Ext.mk₀_bijective A (R.obj Y)).injective
      ((comparison_mk₀ R η f).symm.trans (he.trans (comparison_mk₀ R η f')))
  · intro e
    obtain ⟨g, rfl⟩ := (Ext.mk₀_bijective A (R.obj Y)).surjective e
    obtain ⟨f, hf⟩ := (hη Y).surjective g
    exact ⟨Ext.mk₀ f, (comparison_mk₀ R η f).trans (congrArg Ext.mk₀ hf)⟩

attribute [local instance] Ext.subsingleton_of_injective in
/-- A degree-zero representing-object comparison extends to all actual
Ext groups when the exact functor preserves injectives. -/
theorem comparison_bijective [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (hη : ∀ Y : C, Function.Bijective (fun f : V ⟶ Y => η ≫ R.map f))
    (Y : C) (n : ℕ) : Function.Bijective (comparison R η Y n) := by
  induction n generalizing Y with
  | zero => exact comparison_zero_bijective R η hη Y
  | succ n hn =>
    let I : InjectivePresentation Y := Classical.arbitrary _
    let S := ShortComplex.mk _ _ (cokernel.condition I.f)
    have : Injective (S.map R).X₂ := R.injective_obj_of_injective I.injective
    have hS : S.ShortExact := { exact := ShortComplex.exact_cokernel I.f }
    exact AddMonoidHom.bijective_of_surjective_of_bijective_of_right_exact _ _ _ _
      (comparison R η S.X₂ n) (comparison R η S.X₃ n) (comparison R η S.X₁ (n + 1))
      (by ext e; exact (comparison_naturality R η S.g e).symm)
      (by ext e; exact (comparison_connecting R η hS e).symm)
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' V hS n (n + 1) rfl))
      ((ShortComplex.ab_exact_iff_function_exact _).mp
        (Ext.covariant_sequence_exact₃' A (hS.map_of_exact R) n (n + 1) rfl))
      (hn _).surjective (hn _)
      (fun x₁ => Ext.covariant_sequence_exact₁ _ hS x₁ (by subsingleton) rfl)
      (fun y₁ => Ext.covariant_sequence_exact₁ _ (hS.map_of_exact R) y₁
        (by subsingleton) rfl)

/-- The comparison is an additive equivalence of genuine Ext groups. -/
def equiv [EnoughInjectives C] [R.PreservesInjectiveObjects]
    (hη : ∀ Y : C, Function.Bijective (fun f : V ⟶ Y => η ≫ R.map f))
    (Y : C) (n : ℕ) : Ext.{w} V Y n ≃+ Ext.{w'} A (R.obj Y) n :=
  AddEquiv.ofBijective (comparison R η Y n) (comparison_bijective R η hη Y n)

end Wikipedia.HopfProblem.CuspNormalization.SheafCohomologyFinitePushforward.ExtComparison
