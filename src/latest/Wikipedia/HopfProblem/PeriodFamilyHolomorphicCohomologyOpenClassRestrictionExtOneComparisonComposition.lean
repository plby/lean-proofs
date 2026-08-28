import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassRestrictionExtOneComparison

/-!
# Endpoint-compatible composition of the native Ext comparisons

Exact-functor comparisons respect precomposition in every degree.
In degree one, their proved functoriality combines with an actual
natural transformation and a proved endpoint identity. These generic
identities keep the original Ext carriers and need no representation
or comparison premise for the particular input class.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne

open CuspNormalization.SheafCohomologyFinitePushforward

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

universe w v₁ v₂ v₃ u₁ u₂ u₃

variable {C : Type u₁} [Category.{v₁} C] [Abelian C] [HasExt.{w} C]
  {D : Type u₂} [Category.{v₂} D] [Abelian D] [HasExt.{w} D]
  {E : Type u₃} [Category.{v₃} E] [Abelian E] [HasExt.{w} E]

/-- In every degree, actual precomposition is carried to precomposition
through the mapped source morphism. No enough-injectives hypothesis is used. -/
theorem comparison_precompose
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    {V' V : C} {A : D} (η : A ⟶ R.obj V') (g : V' ⟶ V)
    (F : C) (q : ℕ) (α : Ext.{w} V F q) :
    ExtComparison.comparison R η F q ((Ext.mk₀ g).comp α (zero_add q)) =
      ExtComparison.comparison R (η ≫ R.map g) F q α := by
  change (Ext.mk₀ η).comp
    (((Ext.mk₀ g).comp α (zero_add q)).mapExactFunctor R) (zero_add q) = _
  rw [Ext.mapExactFunctor_comp, Ext.mapExactFunctor_mk₀]
  exact Ext.mk₀_comp_mk₀_assoc η (R.map g) (α.mapExactFunctor R)

variable [EnoughInjectives C]

/-- Sequential native degree-one comparisons, followed by the given
coefficient component, equal the actual comparison at the proved endpoint. -/
theorem comparison_comp_natTrans
    (R : C ⥤ D) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (S : D ⥤ E) [S.Additive] [PreservesFiniteLimits S] [PreservesFiniteColimits S]
    (Q : C ⥤ E) [Q.Additive] [PreservesFiniteLimits Q] [PreservesFiniteColimits Q]
    (ρ : R ⋙ S ⟶ Q) {V F : C} {A : D} {B : E}
    (η : A ⟶ R.obj V) (ν : B ⟶ S.obj A) (μ : B ⟶ Q.obj V)
    (h : ν ≫ S.map η ≫ ρ.app V = μ) (α : Ext.{w} V F 1) :
    (ExtComparison.comparison S ν (R.obj F) 1
      (ExtComparison.comparison R η F 1 α)).comp (Ext.mk₀ (ρ.app F)) (add_zero 1) =
        ExtComparison.comparison Q μ F 1 α := by
  have he : (ν ≫ S.map η) ≫ ρ.app V = μ := (Category.assoc _ _ _).trans h
  exact (congrArg (fun β : Ext.{w} B ((R ⋙ S).obj F) 1 =>
      β.comp (Ext.mk₀ (ρ.app F)) (add_zero 1)) (comparison_comp R S η ν α)).trans
    ((comparison_natTrans (R ⋙ S) Q ρ (ν ≫ S.map η) α).trans
      (congrArg (fun e : B ⟶ Q.obj V => ExtComparison.comparison Q e F 1 α) he))

/-- A natural transformation to the actual identity functor gives the
original degree-one class when its source endpoint is the actual identity. -/
theorem comparison_natTrans_id
    (R : C ⥤ C) [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
    (ρ : R ⟶ 𝟭 C) {V F : C} (η : V ⟶ R.obj V)
    (hη : η ≫ ρ.app V = 𝟙 V) (α : Ext.{w} V F 1) :
    (ExtComparison.comparison R η F 1 α).comp (Ext.mk₀ (ρ.app F)) (add_zero 1) = α := by
  have hid : ExtComparison.comparison (𝟭 C) (𝟙 V) F 1 α = α := by
    change (Ext.mk₀ (𝟙 V)).comp (α.mapExactFunctor (𝟭 C)) (zero_add 1) = α
    exact (Ext.mk₀_id_comp (α.mapExactFunctor (𝟭 C))).trans (mapExactFunctor_id α)
  exact (comparison_natTrans R (𝟭 C) ρ η α).trans
    ((congrArg (fun e : V ⟶ V => ExtComparison.comparison (𝟭 C) e F 1 α) hη).trans hid)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenClassRestriction.ExtOne
