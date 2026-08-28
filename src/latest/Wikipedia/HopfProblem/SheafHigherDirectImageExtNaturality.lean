import Wikipedia.HopfProblem.SheafHigherDirectImageExtHomComplex
import Wikipedia.HopfProblem.SheafHigherDirectImageExtExtend

/-!
# Naturality of the Ext and resolution-homology comparison

Precomposition in Ext is checked on its actual injective-resolution
cocycles.  The result compares Ext to homology of the original
natural-number-indexed injective resolution and is natural in the
represented object.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite
open CochainComplex.HomComplex

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- Precomposition on the evaluated complex acts on a literal cycle by precomposition. -/
theorem coyonedaHomologyMap_cycleClass {ι : Type*} {c : ComplexShape ι}
    {A A' : C} (a : A' ⟶ A) (K : HomologicalComplex C c) (n : ι)
    (f : A ⟶ K.X n)
    (hf : ((((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex c).obj K).sc n).g f = 0)
    (haf : ((((preadditiveCoyoneda.obj (op A')).mapHomologicalComplex c).obj K).sc n).g
      (a ≫ f) = 0) :
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) c).app K) n
      (cycleClass (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex c).obj K)
        n f hf) =
      cycleClass (((preadditiveCoyoneda.obj (op A')).mapHomologicalComplex c).obj K)
        n (a ≫ f) haf :=
  homologyMap_cycleClass
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) c).app K) n f hf haf

variable [HasExt.{0} C] {F : C} (R : InjectiveResolution F)

/-- Naturality for the integer-indexed resolution comparison. -/
@[reassoc]
theorem extExtendedHomologyIso_hom_naturality {A A' : C} (a : A' ⟶ A) (n : ℕ) :
    ((extFunctor n).map a.op).app F ≫ (extExtendedHomologyIso R A' n).hom =
      (extExtendedHomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
            R.cochainComplex) (n : ℤ) := by
  apply AddCommGrpCat.ext
  intro α
  obtain ⟨f, hf, rfl⟩ := R.extMk_surjective α (n + 1) rfl
  have haf : (a ≫ f) ≫ R.cocomplex.d n (n + 1) = 0 := by simp [hf]
  have hfext := extMk_extended_isCycle R f (n + 1) rfl hf
  have hafext := extMk_extended_isCycle R (a ≫ f) (n + 1) rfl haf
  change (extExtendedHomologyIso R A' n).hom
      ((Ext.mk₀ a).comp (R.extMk f (n + 1) rfl hf) (zero_add n)) =
    HomologicalComplex.homologyMap
      ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
        R.cochainComplex) (n : ℤ)
      ((extExtendedHomologyIso R A n).hom (R.extMk f (n + 1) rfl hf))
  rw [R.mk₀_comp_extMk,
    extExtendedHomologyIso_hom_extMk R (a ≫ f) (n + 1) rfl haf hafext,
    extExtendedHomologyIso_hom_extMk R f (n + 1) rfl hf hfext]
  symm
  simpa only [Category.assoc] using
    coyonedaHomologyMap_cycleClass a R.cochainComplex (n : ℤ)
      (f ≫ (R.cochainComplexXIso n n rfl).inv) hfext
      (by simpa only [Category.assoc] using hafext)

/-- The zero-extension comparison with the named resolution complex as its source. -/
def resolutionExtendHomologyIso (A : C) (n : ℕ) :
    (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℤ)).obj
      R.cochainComplex).homology (n : ℤ) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        R.cocomplex).homology n :=
  coyonedaExtendHomologyIso A R.cocomplex n

omit [HasExt C] in
/-- Naturality of the zero-extension comparison for the named resolution complex. -/
@[reassoc]
theorem resolutionExtendHomologyIso_hom_naturality {A A' : C} (a : A' ⟶ A) (n : ℕ) :
    HomologicalComplex.homologyMap
        ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℤ)).app
          R.cochainComplex) (n : ℤ) ≫ (resolutionExtendHomologyIso R A' n).hom =
      (resolutionExtendHomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℕ)).app
            R.cocomplex) n :=
  coyonedaExtendHomologyIso_hom_naturality a R.cocomplex n

/-- Ext is the native homology of coyoneda applied to the original injective resolution. -/
def extHomologyIso (A : C) (n : ℕ) :
    AddCommGrpCat.of (Ext A F n) ≅
      (((preadditiveCoyoneda.obj (op A)).mapHomologicalComplex (.up ℕ)).obj
        R.cocomplex).homology n :=
  extExtendedHomologyIso R A n ≪≫ resolutionExtendHomologyIso R A n

/-- Naturality uses the genuine Ext precomposition and genuine coyoneda complex map. -/
@[reassoc]
theorem extHomologyIso_hom_naturality {A A' : C} (a : A' ⟶ A) (n : ℕ) :
    ((extFunctor n).map a.op).app F ≫ (extHomologyIso R A' n).hom =
      (extHomologyIso R A n).hom ≫
        HomologicalComplex.homologyMap
          ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a.op) (.up ℕ)).app
            R.cocomplex) n := by
  apply AddCommGrpCat.ext
  intro α
  have h₁ := ConcreteCategory.congr_hom (extExtendedHomologyIso_hom_naturality R a n) α
  have h₂ := ConcreteCategory.congr_hom (resolutionExtendHomologyIso_hom_naturality R a n)
    ((extExtendedHomologyIso R A n).hom α)
  exact (congrArg (resolutionExtendHomologyIso R A' n).hom h₁).trans h₂

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
