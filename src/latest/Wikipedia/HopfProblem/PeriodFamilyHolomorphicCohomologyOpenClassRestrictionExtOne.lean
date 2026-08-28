import Wikipedia.HopfProblem.HolomorphicPicardExtRepresentation
import Mathlib.Algebra.Homology.DerivedCategory.Ext.Map

/-!
# Functoriality of native degree-one Ext under exact functors

Every original degree-one class is represented by a constructed short
exact sequence with its literal endpoints. Preservation of its native
extension class proves composition and identity for the original exact
functor maps. A genuine natural transformation of the mapped short
complexes proves the endpoint naturality formula.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne

open HolomorphicPicard.ExtExtensions

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [EnoughInjectives C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w} E]
  {A B : C}

/-- Sequential native exact-functor maps on degree-one Ext are the
native map of the composite functor. Only the source needs enough injectives. -/
theorem mapExactFunctor_comp_functor
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (G : D ⥤ E) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (α : Ext.{w} B A 1) :
    (α.mapExactFunctor F).mapExactFunctor G = α.mapExactFunctor (F ⋙ G) := by
  let hS := representativeComplex_shortExact α
  let α₀ : Ext.{w} B A 1 := hS.extClass
  let αF : Ext.{w} (F.obj B) (F.obj A) 1 := (hS.map_of_exact F).extClass
  let αFG : Ext.{w} (G.obj (F.obj B)) (G.obj (F.obj A)) 1 :=
    ((hS.map_of_exact F).map_of_exact G).extClass
  have hα : α₀ = α := representativeComplex_extClass α
  have hF : α₀.mapExactFunctor F = αF := Ext.mapExactFunctor_extClass F hS
  have hG : αF.mapExactFunctor G = αFG :=
    Ext.mapExactFunctor_extClass G (hS.map_of_exact F)
  have hFG : α₀.mapExactFunctor (F ⋙ G) = αFG :=
    Ext.mapExactFunctor_extClass (F ⋙ G) hS
  exact (congrArg (fun β : Ext.{w} B A 1 =>
      (β.mapExactFunctor F).mapExactFunctor G) hα).symm.trans
    ((congrArg (fun β : Ext.{w} (F.obj B) (F.obj A) 1 => β.mapExactFunctor G) hF).trans
      (hG.trans (hFG.symm.trans
        (congrArg (fun β : Ext.{w} B A 1 => β.mapExactFunctor (F ⋙ G)) hα))))

/-- The original degree-one Ext map induced by the identity functor is
the identity on each original class. -/
theorem mapExactFunctor_id (α : Ext.{w} B A 1) :
    α.mapExactFunctor (𝟭 C) = α := by
  rw [← representativeComplex_extClass α, Ext.mapExactFunctor_extClass]
  rfl

/-- A natural transformation between exact functors gives the actual
contravariant/covariant endpoint square on every native degree-one Ext class. -/
theorem mapExactFunctor_naturality
    (F G : C ⥤ D)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : F ⟶ G) (α : Ext.{w} B A 1) :
    (α.mapExactFunctor F).comp (Ext.mk₀ (η.app A)) (add_zero 1) =
      (Ext.mk₀ (η.app B)).comp (α.mapExactFunctor G) (zero_add 1) := by
  rw [← representativeComplex_extClass α, Ext.mapExactFunctor_extClass,
    Ext.mapExactFunctor_extClass]
  exact ((representativeComplex_shortExact α).map_of_exact F).extClass_naturality
    ((representativeComplex_shortExact α).map_of_exact G)
    ((representativeComplex α).mapNatTrans η)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne
