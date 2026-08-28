import Wikipedia.HopfProblem.ConstantSheafSingularComparisonGlobalSections
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyResolutionSections

/-!
# The actual comparison map of global cochain complexes

This is the original singular cochain complex mapped by the native
sheafification unit into literal global sections of the cochain sheaves.
Its commutativity comes from the original cochain pullback and the native
unit's differential naturality.
-/

noncomputable section

open CategoryTheory Opposite TopologicalSpace

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison

open CuspNormalization.SheafCohomologyResolution

variable (X : TopCat.{0}) (A : AddCommGrpCat.{0})

/-- Literal global sections of the actual sheafified cochain complex. -/
abbrev globalSheafCochainComplex : CochainComplex AddCommGrpCat.{0} ℕ :=
  ((globalSectionsFunctor X).mapHomologicalComplex (.up ℕ)).obj
    (cochainSheafComplex X A)

/-- The actual native comparison, retaining the original singular complex. -/
def globalCochainComparison : singularCochainComplex X A ⟶
    globalSheafCochainComplex X A where
  f n := globalCochainUnit X A n
  comm' i j _ := by
    apply AddCommGrpCat.hom_ext
    ext φ
    let f : C((⊤ : Opens X), X) := ⟨Subtype.val, continuous_subtype_val⟩
    have hp := congrArg
      (fun g : (singularCochainComplex X A).X i ⟶
        (singularCochainComplex (⊤ : Opens X) A).X j => g φ)
      ((singularPullback A f).comm i j)
    have hu := congrArg
      (fun g : (cochainPresheaf X A i).obj (op ⊤) ⟶
        (cochainSheaf X A j).obj.obj (op ⊤) =>
          g (restrictGlobalCochain A i φ ⊤))
      (NatTrans.congr_app (cochainSheafUnit_d X A i j) (op ⊤))
    exact hu.trans (congrArg ((cochainSheafUnit X A j).app (op ⊤)) hp)

@[simp]
theorem globalCochainComparison_f (n : ℕ) :
    (globalCochainComparison X A).f n = globalCochainUnit X A n := rfl

/-- Actual global comparison commutes with every original differential. -/
theorem globalCochainComparison_d_apply (i j : ℕ) (φ : Cochains X A i) :
    globalCochainUnit X A j ((singularCochainComplex X A).d i j φ) =
      (globalSheafCochainComplex X A).d i j (globalCochainUnit X A i φ) :=
  (congrArg (fun g => g φ) ((globalCochainComparison X A).comm i j)).symm

end Wikipedia.HopfProblem.ConstantSheafSingularComparison
