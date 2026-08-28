import Mathlib.Topology.Sheaves.Flasque
import Mathlib.CategoryTheory.Sites.Limits
import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
import Mathlib.Algebra.Category.Grp.Biproducts

/-!
# Products of genuine flasque abelian sheaves

The section functor preserves the actual categorical product. Its
comparison with tuples is the tuple of the original sheaf projections.
Extending each component section therefore proves that an arbitrary
small product of flasque abelian sheaves is flasque.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque

variable {X : TopCat.{0}} {ι : Type}
variable (F : ι → TopCat.Sheaf AddCommGrpCat.{0} X)

/-- Sections of the actual sheaf product are the product of the actual
component section groups. -/
def productSectionsIso (U : (Opens X)ᵒᵖ) :
    (∏ᶜ F).obj.obj U ≅ AddCommGrpCat.of (∀ i, (F i).obj.obj U) :=
  (isLimitOfHasProductOfPreservesLimit
      (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat.{0} ⋙
        (evaluation (Opens X)ᵒᵖ AddCommGrpCat.{0}).obj U) F).conePointUniqueUpToIso
    (AddCommGrpCat.HasLimit.productLimitCone (fun i => (F i).obj.obj U)).isLimit

/-- The section comparison preserves the native additive groups. -/
def productSectionsEquiv (U : (Opens X)ᵒᵖ) :
    (∏ᶜ F).obj.obj U ≃+ (∀ i, (F i).obj.obj U) :=
  (productSectionsIso F U).addCommGroupIsoToAddEquiv

@[reassoc] theorem productSectionsIso_hom_comp_eval (U : (Opens X)ᵒᵖ) (i : ι) :
    (productSectionsIso F U).hom ≫
        AddCommGrpCat.ofHom (Pi.evalAddMonoidHom (fun j => (F j).obj.obj U) i) =
      (Pi.π F i).hom.app U :=
  IsLimit.conePointUniqueUpToIso_hom_comp _ _ (Discrete.mk i)

/-- Every coordinate of the comparison is the original sheaf product
projection evaluated on the given open set. -/
@[simp] theorem productSectionsEquiv_apply (U : (Opens X)ᵒᵖ)
    (s : (∏ᶜ F).obj.obj U) (i : ι) :
    productSectionsEquiv F U s i = (Pi.π F i).hom.app U s :=
  ConcreteCategory.congr_hom (productSectionsIso_hom_comp_eval F U i) s

/-- Restriction of a product section restricts its original components. -/
theorem productSectionsEquiv_restrict {U V : (Opens X)ᵒᵖ} (r : U ⟶ V)
    (s : (∏ᶜ F).obj.obj U) (i : ι) :
    productSectionsEquiv F V ((∏ᶜ F).obj.map r s) i =
      (F i).obj.map r (productSectionsEquiv F U s i) := by
  simp only [productSectionsEquiv_apply]
  exact ConcreteCategory.congr_hom ((Pi.π F i).hom.naturality r) s

/-- An arbitrary small product of genuine flasque abelian sheaves is
flasque; no condition on the underlying topological space is needed. -/
theorem product_isFlasque [∀ i, TopCat.Sheaf.IsFlasque (F i)] :
    TopCat.Sheaf.IsFlasque (∏ᶜ F) where
  epi {U V} r := by
    classical
    refine (AddCommGrpCat.epi_iff_surjective _).mpr ?_
    intro s
    have h : ∀ i, ∃ t : (F i).obj.obj U,
        (F i).obj.map r t = productSectionsEquiv F V s i := fun i =>
      (AddCommGrpCat.epi_iff_surjective ((F i).obj.map r)).mp inferInstance
        (productSectionsEquiv F V s i)
    choose t ht using h
    refine ⟨(productSectionsEquiv F U).symm t, ?_⟩
    apply (productSectionsEquiv F V).injective
    funext i
    rw [productSectionsEquiv_restrict, AddEquiv.apply_symm_apply]
    exact ht i

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.Flasque
