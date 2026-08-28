import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenBaseActionBasic
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesActions
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyOpenClassesScalarRestriction

/-!
# The canonical coefficient-induced base-open action on native neighborhood cohomology

Apply the original cohomology functor to literal holomorphic multipliers
on the original full-preimage coefficient sheaf. The genuine canonical
open-restriction comparison expresses this action on the original `H'`.
No restricted-family comparison or cohomology coordinates occur in the
definition. The action agrees with the original complex scalar action
on constant base functions, by actual coefficient naturality.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction

open PeriodFamilyHigherDirectImage CuspNormalization.SheafCohomology

/-- Express actual coefficient endomorphisms through an actual abelian-group isomorphism. -/
def coefficientConjugateEnd {M N : AddCommGrpCat.{0}} (e : M ≅ N) :
    End N →+* End M where
  toFun f := e.hom ≫ f ≫ e.inv
  map_one' := by simp
  map_mul' f g := by
    simp only [End.mul_def, Category.assoc, Iso.inv_hom_id_assoc]
  map_zero' := by simp
  map_add' f g := by
    change e.hom ≫ (f.asHom + g.asHom) ≫ e.inv =
      (e.hom ≫ f.asHom ≫ e.inv) + (e.hom ≫ g.asHom ≫ e.inv)
    simp only [Preadditive.comp_add, Preadditive.add_comp]

variable {V : Type*} {B : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B]

local notation "IT" => modelWithCornersSelf ℂ (V × ComplexPlane₂)

/-- The actual open-restriction comparison as an isomorphism of the original groups. -/
def openCohomologyIso (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    OpenClasses.neighborhoodCohomology P U q ≅
      (CategoryTheory.Sheaf.functorH _ q).obj (OpenClasses.preimageHolomorphicSheaf P U) :=
  (OpenClasses.openCohomologyEquiv P U q).toAddCommGrpIso

variable [IsManifold (modelWithCornersSelf ℂ V) ω B]

/-- The original cohomology functor sends literal base-open multipliers
to the genuine action on the full-preimage sheaf's native cohomology. -/
def preimageBaseEnd (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    Zero.BaseSection P U →+*
      End ((CategoryTheory.Sheaf.functorH _ q).obj (OpenClasses.preimageHolomorphicSheaf P U)) :=
  (mapEndRingHom (CategoryTheory.Sheaf.functorH _ q)
    (OpenClasses.preimageHolomorphicSheaf P U)).comp (preimageMultiplyRingHom P U)

/-- The module structure is induced by actual coefficient multiplication
on the original open-submanifold holomorphic sheaf. -/
@[instance_reducible] def preimageCohomologyModule
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    Module (Zero.BaseSection P U)
      (CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P U) q) :=
  moduleOfScalarEnd
    ((CategoryTheory.Sheaf.functorH _ q).obj (OpenClasses.preimageHolomorphicSheaf P U))
    (preimageBaseEnd P U q)

/-- The action on actual preimage cohomology is its literal coefficient map. -/
theorem preimageCohomologyModule_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (g : Zero.BaseSection P U)
    (x : CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P U) q) :
    letI := preimageCohomologyModule P U q
    g • x = CategoryTheory.Sheaf.H.map (preimageMultiplyEnd P U g) q x := rfl

/-- The genuine open-restriction isomorphism expresses the coefficient
action on the original ambient-open cohomology-presheaf group. -/
def neighborhoodBaseEnd (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    Zero.BaseSection P U →+* End (OpenClasses.neighborhoodCohomology P U q) :=
  (coefficientConjugateEnd (openCohomologyIso P U q)).comp (preimageBaseEnd P U q)

/-- The actual base-open module on the original native `H'` group,
defined through coefficient multipliers and canonical open restriction. -/
@[instance_reducible] def neighborhoodCohomologyModule
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    Module (Zero.BaseSection P U) (OpenClasses.neighborhoodCohomology P U q) :=
  moduleOfScalarEnd (OpenClasses.neighborhoodCohomology P U q) (neighborhoodBaseEnd P U q)

/-- The action is precisely the original coefficient map under the
actual open-restriction comparison, not the restricted-family comparison. -/
theorem neighborhoodCohomologyModule_smul (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (g : Zero.BaseSection P U) (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    g • x = (OpenClasses.openCohomologyEquiv P U q).symm
      (CategoryTheory.Sheaf.H.map (preimageMultiplyEnd P U g) q
        (OpenClasses.openCohomologyEquiv P U q x)) := rfl

/-- Canonical open restriction retains the exact coefficient-induced action. -/
theorem openCohomologyEquiv_smul_map (P : HolomorphicPeriodMap V B) (U : Opens B)
    (q : ℕ) (g : Zero.BaseSection P U) (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := neighborhoodCohomologyModule P U q
    OpenClasses.openCohomologyEquiv P U q (g • x) =
      CategoryTheory.Sheaf.H.map (preimageMultiplyEnd P U g) q
        (OpenClasses.openCohomologyEquiv P U q x) := by
  let := neighborhoodCohomologyModule P U q
  exact (congrArg (OpenClasses.openCohomologyEquiv P U q)
    (neighborhoodCohomologyModule_smul P U q g x)).trans
      ((OpenClasses.openCohomologyEquiv P U q).apply_symm_apply _)

/-- The genuine open-restriction comparison is linear for its actual
coefficient-induced actions on both original native groups. -/
def openCohomologyBaseLinearEquiv (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    letI := neighborhoodCohomologyModule P U q
    letI := preimageCohomologyModule P U q
    OpenClasses.neighborhoodCohomology P U q ≃ₗ[Zero.BaseSection P U]
      CategoryTheory.Sheaf.H.{0} (OpenClasses.preimageHolomorphicSheaf P U) q := by
  letI := neighborhoodCohomologyModule P U q
  letI := preimageCohomologyModule P U q
  exact { OpenClasses.openCohomologyEquiv P U q with
    map_smul' := openCohomologyEquiv_smul_map P U q }

/-- Constant holomorphic base functions recover the original complex
action induced independently by the ambient cohomology-presheaf functor. -/
theorem neighborhoodCohomologyModule_algebraMap_smul
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) (c : ℂ)
    (x : OpenClasses.neighborhoodCohomology P U q) :
    letI := OpenClasses.neighborhoodCohomologyModule P U q
    letI := neighborhoodCohomologyModule P U q
    algebraMap ℂ (Zero.BaseSection P U) c • x = c • x := by
  let := P.totalChartedSpace
  let := OpenClasses.neighborhoodCohomologyModule P U q
  let := neighborhoodCohomologyModule P U q
  apply (OpenClasses.openCohomologyEquiv P U q).injective
  have hc := congrArg
    (fun f : OpenClasses.preimageHolomorphicSheaf P U ⟶
        OpenClasses.preimageHolomorphicSheaf P U =>
      CategoryTheory.Sheaf.H.map f q (OpenClasses.openCohomologyEquiv P U q x))
    (preimageMultiplyEnd_algebraMap P U c)
  exact (openCohomologyEquiv_smul_map P U q (algebraMap ℂ (Zero.BaseSection P U) c) x).trans
    (hc.trans (OpenClasses.holomorphicRestriction_cohomologyEquiv_scalar IT
      (Zero.basePreimage P U) q c x).symm)

/-- The unchanged complex action and the genuine base-open action
form the actual scalar tower on native neighborhood cohomology. -/
theorem neighborhoodCohomologyScalarTower
    (P : HolomorphicPeriodMap V B) (U : Opens B) (q : ℕ) :
    letI := OpenClasses.neighborhoodCohomologyModule P U q
    letI := neighborhoodCohomologyModule P U q
    IsScalarTower ℂ (Zero.BaseSection P U) (OpenClasses.neighborhoodCohomology P U q) := by
  let := OpenClasses.neighborhoodCohomologyModule P U q
  let := neighborhoodCohomologyModule P U q
  exact IsScalarTower.of_algebraMap_smul (neighborhoodCohomologyModule_algebraMap_smul P U q)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.OpenBaseAction
