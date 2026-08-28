import Wikipedia.HopfProblem.CuspNormalizationSheafBiproduct
import Wikipedia.HopfProblem.SheafSingularCupComparisonTotalCategoryProducts
import Mathlib.Topology.Sheaves.SheafCondition.UniqueGluing

/-!
# Literal coefficient pairs in the torus cup comparison

The pair sheaf has the original pairs of sections and coordinatewise
restrictions. Its canonical comparison with the categorical biproduct
retains the actual two projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs

abbrev AbSheaf (X : TopCat.{0}) := TopCat.Sheaf AddCommGrpCat.{0} X

variable {X : TopCat.{0}}

/-- Literal pairs of sections of the original additive sheaf. -/
def presheaf (F : AbSheaf X) : TopCat.Presheaf AddCommGrpCat.{0} X where
  obj U := AddCommGrpCat.of (F.obj.obj U × F.obj.obj U)
  map f := AddCommGrpCat.ofHom ((F.obj.map f).hom.prodMap (F.obj.map f).hom)
  map_id U := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact Prod.ext (ConcreteCategory.congr_hom (F.obj.map_id U) s.1)
      (ConcreteCategory.congr_hom (F.obj.map_id U) s.2)
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply AddMonoidHom.ext
    intro s
    exact Prod.ext (ConcreteCategory.congr_hom (F.obj.map_comp f g) s.1)
      (ConcreteCategory.congr_hom (F.obj.map_comp f g) s.2)

/-- The original gluing theorem applies separately to the two actual coefficients. -/
theorem presheaf_isSheaf (F : AbSheaf X) : (presheaf F).IsSheaf := by
  apply (TopCat.Presheaf.isSheaf_iff_isSheafUniqueGluing (presheaf F)).mpr
  intro ι U s hs
  have h₀ : TopCat.Presheaf.IsCompatible F.obj U (fun i => (s i).1) :=
    fun i j => congrArg Prod.fst (hs i j)
  have h₁ : TopCat.Presheaf.IsCompatible F.obj U (fun i => (s i).2) :=
    fun i j => congrArg Prod.snd (hs i j)
  obtain ⟨a, ha, hua⟩ := F.existsUnique_gluing U (fun i => (s i).1) h₀
  obtain ⟨b, hb, hub⟩ := F.existsUnique_gluing U (fun i => (s i).2) h₁
  refine ⟨(a, b), fun i => Prod.ext (ha i) (hb i), ?_⟩
  intro t ht
  exact Prod.ext (hua t.1 (fun i => congrArg Prod.fst (ht i)))
    (hub t.2 (fun i => congrArg Prod.snd (ht i)))

/-- The genuine sheaf of pairs, retaining the literal section types. -/
def sheaf (F : AbSheaf X) : AbSheaf X := ⟨presheaf F, presheaf_isSheaf F⟩

/-- Apply an actual sheaf morphism to both original coefficients. -/
def map {F G : AbSheaf X} (f : F ⟶ G) : sheaf F ⟶ sheaf G where
  hom :=
    { app U := AddCommGrpCat.ofHom ((f.hom.app U).hom.prodMap (f.hom.app U).hom)
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact Prod.ext (ConcreteCategory.congr_hom (f.hom.naturality h) s.1)
          (ConcreteCategory.congr_hom (f.hom.naturality h) s.2) }

/-- The actual first coefficient projection. -/
def fst (F : AbSheaf X) : sheaf F ⟶ F where
  hom := { app _ := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
           naturality _ _ _ := rfl }

/-- The actual second coefficient projection. -/
def snd (F : AbSheaf X) : sheaf F ⟶ F where
  hom := { app _ := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
           naturality _ _ _ := rfl }

/-- Pair two actual sectionwise maps. -/
def lift {F G : AbSheaf X} (f g : F ⟶ G) : F ⟶ sheaf G where
  hom :=
    { app U := AddCommGrpCat.ofHom ((f.hom.app U).hom.prod (g.hom.app U).hom)
      naturality U V h := by
        apply AddCommGrpCat.hom_ext
        apply AddMonoidHom.ext
        intro s
        exact Prod.ext (ConcreteCategory.congr_hom (f.hom.naturality h) s)
          (ConcreteCategory.congr_hom (g.hom.naturality h) s) }

@[reassoc (attr := simp)] theorem lift_fst {F G : AbSheaf X} (f g : F ⟶ G) :
    lift f g ≫ fst G = f := rfl

@[reassoc (attr := simp)] theorem lift_snd {F G : AbSheaf X} (f g : F ⟶ G) :
    lift f g ≫ snd G = g := rfl

@[reassoc (attr := simp)] theorem map_fst {F G : AbSheaf X} (f : F ⟶ G) :
    map f ≫ fst G = fst F ≫ f := rfl

@[reassoc (attr := simp)] theorem map_snd {F G : AbSheaf X} (f : F ⟶ G) :
    map f ≫ snd G = snd F ≫ f := rfl

/-- Actual coefficient projections detect equality of pair-valued maps. -/
theorem hom_ext {F G : AbSheaf X} {f g : F ⟶ sheaf G}
    (h₀ : f ≫ fst G = g ≫ fst G) (h₁ : f ≫ snd G = g ≫ snd G) : f = g := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  exact Prod.ext
    (ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) h₀) s)
    (ConcreteCategory.congr_hom (congrArg (fun k => k.hom.app U) h₁) s)

/-- The literal pair sheaf is the actual categorical biproduct. -/
def biprodIso (F : AbSheaf X) : sheaf F ≅ F ⊞ F where
  hom := biprod.lift (fst F) (snd F)
  inv := lift biprod.fst biprod.snd
  hom_inv_id := by
    apply hom_ext
    · simp
    · simp
  inv_hom_id := by
    apply biprod.hom_ext
    · simp
    · simp

@[reassoc (attr := simp)] theorem biprodIso_hom_fst (F : AbSheaf X) :
    (biprodIso F).hom ≫ biprod.fst = fst F := by simp [biprodIso]

@[reassoc (attr := simp)] theorem biprodIso_hom_snd (F : AbSheaf X) :
    (biprodIso F).hom ≫ biprod.snd = snd F := by simp [biprodIso]

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.Pairs
