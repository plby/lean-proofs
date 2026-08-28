import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# Actual stalks of finite direct sums of additive sheaves

The finite direct sums used in the normalization resolution are categorical
biproducts. Their stalks are identified with the literal finite products of
stalk groups by the actual additive stalk functor and Mathlib's biproduct
comparison. The coordinate formulas retain the actual projection maps.
-/

noncomputable section

open TopologicalSpace CategoryTheory CategoryTheory.Limits Opposite
open TopCat.Presheaf
open scoped AlgebraicGeometry

namespace Wikipedia.HopfProblem.CuspNormalization.SheafBiproduct

attribute [local instance] CategoryTheory.Abelian.hasFiniteBiproducts

variable {ι : Type} [Finite ι]

/-- The standard additive-group biproduct comparison has the actual
categorical projections as its coordinates. -/
@[reassoc] theorem biproductIsoPi_hom_comp_eval (A : ι → AddCommGrpCat) (i : ι) :
    (AddCommGrpCat.biproductIsoPi A).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => A j) i) =
      biproduct.π A i := by
  apply (cancel_epi (AddCommGrpCat.biproductIsoPi A).inv).mp
  simp only [Iso.inv_hom_id_assoc, AddCommGrpCat.biproductIsoPi_inv_comp_π]

variable (X : TopCat.{0})

/-- The actual stalk functor on additive sheaves. -/
abbrev stalkFunctor (x : X) : TopCat.Sheaf AddCommGrpCat X ⥤ AddCommGrpCat :=
  TopCat.Sheaf.forget AddCommGrpCat X ⋙ TopCat.Presheaf.stalkFunctor AddCommGrpCat x

/-- The genuine categorical comparison of a finite direct-sum stalk with
the product of its actual stalk groups. -/
def finiteStalkIso (A : ι → TopCat.Sheaf AddCommGrpCat X) (x : X) :
    (⨁ A).presheaf.stalk x ≅ AddCommGrpCat.of (∀ i, (A i).presheaf.stalk x) :=
  ((stalkFunctor X x).mapBiproduct A) ≪≫
    AddCommGrpCat.biproductIsoPi ((stalkFunctor X x).obj ∘ A)

/-- The actual finite direct-sum stalk as an additive equivalence. -/
def finiteStalkEquiv (A : ι → TopCat.Sheaf AddCommGrpCat X) (x : X) :
    (⨁ A).presheaf.stalk x ≃+ (∀ i, (A i).presheaf.stalk x) :=
  (finiteStalkIso X A x).addCommGroupIsoToAddEquiv

@[reassoc] theorem finiteStalkIso_hom_comp_eval
    (A : ι → TopCat.Sheaf AddCommGrpCat X) (x : X) (i : ι) :
    (finiteStalkIso X A x).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => (A j).presheaf.stalk x) i) =
      (stalkFunctor X x).map (biproduct.π A i) := by
  change (((stalkFunctor X x).mapBiproduct A).hom ≫
      (AddCommGrpCat.biproductIsoPi ((stalkFunctor X x).obj ∘ A)).hom) ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => (stalkFunctor X x).obj (A j)) i) = _
  rw [Category.assoc, biproductIsoPi_hom_comp_eval, Functor.mapBiproduct_hom]
  exact biproduct.lift_π (f := (stalkFunctor X x).obj ∘ A)
    (fun j => (stalkFunctor X x).map (biproduct.π A j)) i

/-- The comparison is the tuple of actual stalk maps of the projections. -/
@[simp] theorem finiteStalkEquiv_apply (A : ι → TopCat.Sheaf AddCommGrpCat X)
    (x : X) (s : (⨁ A).presheaf.stalk x) (i : ι) :
    finiteStalkEquiv X A x s i = (stalkFunctor X x).map (biproduct.π A i) s := by
  exact ConcreteCategory.congr_hom (finiteStalkIso_hom_comp_eval X A x i) s

/-- Each component of a genuine germ is the germ of the actual direct-sum
projection of the original section. -/
@[simp] theorem finiteStalkEquiv_germ (A : ι → TopCat.Sheaf AddCommGrpCat X)
    (U : Opens X) (x : X) (hx : x ∈ U) (s : (⨁ A).obj.obj (op U)) (i : ι) :
    finiteStalkEquiv X A x ((⨁ A).presheaf.germ U x hx s) i =
      (A i).presheaf.germ U x hx ((biproduct.π A i).hom.app (op U) s) := by
  rw [finiteStalkEquiv_apply]
  exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx (biproduct.π A i).hom s

end Wikipedia.HopfProblem.CuspNormalization.SheafBiproduct
