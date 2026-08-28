import Wikipedia.HopfProblem.SheafHigherDirectImageExtNaturality

/-!
# Ext as the homology of an evaluated injective resolution

This is a natural isomorphism in the represented object, with actual
Ext precomposition on one side and actual coyoneda precomposition on
the other.  Consequently the comparison can be used for presheaves,
not merely for their separate groups of sections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Abelian Opposite

namespace Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge

universe u

variable {C : Type u} [Category.{0} C] [Abelian C]

/-- Homology of the literally evaluated complex, functorial in its coyoneda variable. -/
def coyonedaHomologyFunctor (K : CochainComplex C ℕ) (n : ℕ) : Cᵒᵖ ⥤ AddCommGrpCat where
  obj A := (((preadditiveCoyoneda.obj A).mapHomologicalComplex (.up ℕ)).obj K).homology n
  map a := HomologicalComplex.homologyMap
    ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map a) (.up ℕ)).app K) n
  map_id A := by
    have h : ((NatTrans.mapHomologicalComplex (preadditiveCoyoneda.map (𝟙 A))
        (.up ℕ)).app K) = 𝟙 _ := by
      ext i f
      exact Category.id_comp f
    exact (congrArg (fun φ => HomologicalComplex.homologyMap φ n) h).trans
      (HomologicalComplex.homologyMap_id _ _)
  map_comp a b := by
    simp only [Functor.map_comp, NatTrans.mapHomologicalComplex_comp,
      NatTrans.comp_app, HomologicalComplex.homologyMap_comp]

variable [HasExt.{0} C] {F : C} (R : InjectiveResolution F)

/-- The genuine injective-resolution computation of Ext is natural in its first argument. -/
def extHomologyNatIso (n : ℕ) :
    (extFunctor n).flip.obj F ≅ coyonedaHomologyFunctor R.cocomplex n :=
  NatIso.ofComponents (fun A => extHomologyIso R A.unop n)
    (fun a => extHomologyIso_hom_naturality R a.unop n)

@[simp] theorem extHomologyNatIso_hom_app (n : ℕ) (A : Cᵒᵖ) :
    (extHomologyNatIso R n).hom.app A = (extHomologyIso R A.unop n).hom := rfl

@[simp] theorem extHomologyNatIso_inv_app (n : ℕ) (A : Cᵒᵖ) :
    (extHomologyNatIso R n).inv.app A = (extHomologyIso R A.unop n).inv := rfl

end Wikipedia.HopfProblem.SheafHigherDirectImage.ExtBridge
