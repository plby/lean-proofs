import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalars
import Mathlib.Topology.Sheaves.Abelian
import Mathlib.Algebra.Category.Grp.Biproducts
import Mathlib.CategoryTheory.Preadditive.AdditiveFunctor

/-!
# The native binary-biproduct comparison for sheaf cohomology

The scalar action on a binary direct sum is the actual diagonal sheaf
endomorphism.  The additive cohomology comparison is the comparison of the
native additive cohomology functor with the categorical binary biproduct.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
namespace NegativeOneCohomology.GenericBiproduct

section ScalarEndomorphisms

universe u v

variable {D : Type u} [Category.{v} D] [Preadditive D]
  {F G : D} [HasBinaryBiproduct F G]
  (ρ : ℂ →+* End F) (σ : ℂ →+* End G)

/-- Scalar multiplication on the actual binary biproduct, induced by the
given scalar endomorphisms of its two summands. -/
def diagonalScalarEnd : ℂ →+* End (F ⊞ G) where
  toFun c := biprod.map (ρ c) (σ c)
  map_one' := by
    apply biprod.hom_ext <;>
      simp only [biprod.map_fst, biprod.map_snd, map_one, End.one_def,
        Category.comp_id, Category.id_comp]
  map_mul' c d := by
    change biprod.map (ρ (c * d)) (σ (c * d)) =
      biprod.map (ρ d) (σ d) ≫ biprod.map (ρ c) (σ c)
    apply biprod.hom_ext <;>
      simp only [biprod.map_fst, biprod.map_snd, map_mul, End.mul_def,
        Category.assoc, biprod.map_fst_assoc, biprod.map_snd_assoc]
  map_zero' := by
    apply biprod.hom_ext <;>
      simp only [biprod.map_fst, biprod.map_snd, map_zero, comp_zero, zero_comp]
  map_add' c d := by
    change biprod.map (ρ (c + d)) (σ (c + d)) =
      biprod.map (ρ c) (σ c) + biprod.map (ρ d) (σ d)
    apply biprod.hom_ext
    · have hadd : (ρ (c + d)).asHom = (ρ c).asHom + (ρ d).asHom := ρ.map_add c d
      simp only [Preadditive.add_comp, biprod.map_fst]
      exact (congrArg (fun f : F ⟶ F => biprod.fst ≫ f) hadd).trans
        (Preadditive.comp_add _ _ _ _ _ _)
    · have hadd : (σ (c + d)).asHom = (σ c).asHom + (σ d).asHom := σ.map_add c d
      simp only [Preadditive.add_comp, biprod.map_snd]
      exact (congrArg (fun f : G ⟶ G => biprod.snd ≫ f) hadd).trans
        (Preadditive.comp_add _ _ _ _ _ _)

@[reassoc] theorem diagonalScalarEnd_fst (c : ℂ) :
    diagonalScalarEnd ρ σ c ≫ biprod.fst = biprod.fst ≫ ρ c :=
  biprod.map_fst _ _

@[reassoc] theorem diagonalScalarEnd_snd (c : ℂ) :
    diagonalScalarEnd ρ σ c ≫ biprod.snd = biprod.snd ≫ σ c :=
  biprod.map_snd _ _

@[reassoc] theorem inl_diagonalScalarEnd (c : ℂ) :
    biprod.inl ≫ diagonalScalarEnd ρ σ c = ρ c ≫ biprod.inl :=
  biprod.inl_map _ _

@[reassoc] theorem inr_diagonalScalarEnd (c : ℂ) :
    biprod.inr ≫ diagonalScalarEnd ρ σ c = σ c ≫ biprod.inr :=
  biprod.inr_map _ _

end ScalarEndomorphisms

section AdditiveComparison

/-- The native cohomology functor with its topological sheaf category and
coefficient universe made explicit. -/
abbrev cohomologyFunctor (X : TopCat.{0}) (n : ℕ) :
    TopCat.Sheaf AddCommGrpCat.{0} X ⥤ AddCommGrpCat.{0} :=
  CategoryTheory.Sheaf.functorH _ n

instance cohomologyFunctor_additive (X : TopCat.{0}) (n : ℕ) :
    (cohomologyFunctor X n).Additive := by
  change (CategoryTheory.Sheaf.functorH (Opens.grothendieckTopology X) n).Additive
  infer_instance

instance cohomologyFunctor_preservesBinaryBiproducts (X : TopCat.{0}) (n : ℕ) :
    PreservesBinaryBiproducts (cohomologyFunctor X n) :=
  preservesBinaryBiproducts_of_preservesBinaryProducts (cohomologyFunctor X n)

variable {X : TopCat.{0}} (F G : TopCat.Sheaf AddCommGrpCat.{0} X) (n : ℕ)

/-- The native cohomology functor's binary-biproduct comparison followed by
the usual comparison of an abelian-group biproduct with the product type. -/
def cohomologyIso :
    (cohomologyFunctor X n).obj (F ⊞ G) ≅
      AddCommGrpCat.of ((cohomologyFunctor X n).obj F × (cohomologyFunctor X n).obj G) :=
  (cohomologyFunctor X n).mapBiprod F G ≪≫
    AddCommGrpCat.biprodIsoProd _ _

/-- The corresponding equivalence of the actual Ext cohomology groups. -/
def cohomologyAddEquiv :
    CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n ≃+
      (CategoryTheory.Sheaf.H.{0} F n × CategoryTheory.Sheaf.H.{0} G n) :=
  (cohomologyIso F G n).addCommGroupIsoToAddEquiv

private theorem biprodIsoProd_hom_comp_fst (A B : AddCommGrpCat.{0}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst A B) = biprod.fst := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).mp
  simp only [Iso.inv_hom_id_assoc, AddCommGrpCat.biprodIsoProd_inv_comp_fst]

private theorem biprodIsoProd_hom_comp_snd (A B : AddCommGrpCat.{0}) :
    (AddCommGrpCat.biprodIsoProd A B).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd A B) = biprod.snd := by
  apply (cancel_epi (AddCommGrpCat.biprodIsoProd A B).inv).mp
  simp only [Iso.inv_hom_id_assoc, AddCommGrpCat.biprodIsoProd_inv_comp_snd]

@[reassoc] theorem cohomologyIso_hom_comp_fst :
    (cohomologyIso F G n).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.fst
          ((cohomologyFunctor X n).obj F) ((cohomologyFunctor X n).obj G)) =
      (cohomologyFunctor X n).map (biprod.fst : F ⊞ G ⟶ F) := by
  change (((cohomologyFunctor X n).mapBiprod F G).hom ≫
      (AddCommGrpCat.biprodIsoProd _ _).hom) ≫ _ = _
  rw [Category.assoc, biprodIsoProd_hom_comp_fst, Functor.mapBiprod_hom,
    biprod.lift_fst]

@[reassoc] theorem cohomologyIso_hom_comp_snd :
    (cohomologyIso F G n).hom ≫
        AddCommGrpCat.ofHom (AddMonoidHom.snd
          ((cohomologyFunctor X n).obj F) ((cohomologyFunctor X n).obj G)) =
      (cohomologyFunctor X n).map (biprod.snd : F ⊞ G ⟶ G) := by
  change (((cohomologyFunctor X n).mapBiprod F G).hom ≫
      (AddCommGrpCat.biprodIsoProd _ _).hom) ≫ _ = _
  rw [Category.assoc, biprodIsoProd_hom_comp_snd, Functor.mapBiprod_hom,
    biprod.lift_snd]

/-- The first coordinate is exactly the cohomology map of the original
categorical first projection. -/
@[simp] theorem cohomologyAddEquiv_fst
    (a : CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n) :
    (cohomologyAddEquiv F G n a).1 =
      CategoryTheory.Sheaf.H.map (biprod.fst : F ⊞ G ⟶ F) n a := by
  have h := ConcreteCategory.congr_hom (cohomologyIso_hom_comp_fst F G n) a
  change ((cohomologyIso F G n).hom a).1 =
    CategoryTheory.Sheaf.H.map (biprod.fst : F ⊞ G ⟶ F) n a at h
  change ((cohomologyIso F G n).hom a).1 =
    CategoryTheory.Sheaf.H.map (biprod.fst : F ⊞ G ⟶ F) n a
  exact h

/-- The second coordinate is exactly the cohomology map of the original
categorical second projection. -/
@[simp] theorem cohomologyAddEquiv_snd
    (a : CategoryTheory.Sheaf.H.{0} (F ⊞ G : TopCat.Sheaf AddCommGrpCat.{0} X) n) :
    (cohomologyAddEquiv F G n a).2 =
      CategoryTheory.Sheaf.H.map (biprod.snd : F ⊞ G ⟶ G) n a := by
  have h := ConcreteCategory.congr_hom (cohomologyIso_hom_comp_snd F G n) a
  change ((cohomologyIso F G n).hom a).2 =
    CategoryTheory.Sheaf.H.map (biprod.snd : F ⊞ G ⟶ G) n a at h
  change ((cohomologyIso F G n).hom a).2 =
    CategoryTheory.Sheaf.H.map (biprod.snd : F ⊞ G ⟶ G) n a
  exact h

end AdditiveComparison

end NegativeOneCohomology.GenericBiproduct
end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1
