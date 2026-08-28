import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyScalars
import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereNegativeOneCohomologyBiproductComparison

/-!
# The actual direct sum of the sphere sheaf and the infinity ideal

The sheaf below is the native categorical direct sum of the original
holomorphic-function sheaf and its original ideal of functions vanishing
at infinity. Its scalar action is the diagonal of their actual pointwise
scalar maps. The cohomology comparison preserves the genuine summand
inclusions and projections.
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

open CuspNormalization.SheafCohomology

/-- The genuine sheaf `𝒪 ⊕ 𝒪(-∞)` on the constructed analytic sphere. -/
def splitSheaf : TopCat.Sheaf AddCommGrpCat.{0} (TopCat.of RiemannSphere) :=
  sphereSheaf ⊞ negativeOneSheaf

/-- The original first summand projection. -/
abbrev splitFirstProjection : splitSheaf ⟶ sphereSheaf := biprod.fst

/-- The original second summand projection. -/
abbrev splitSecondProjection : splitSheaf ⟶ negativeOneSheaf := biprod.snd

/-- The original first summand inclusion. -/
abbrev splitFirstInclusion : sphereSheaf ⟶ splitSheaf := biprod.inl

/-- The original second summand inclusion. -/
abbrev splitSecondInclusion : negativeOneSheaf ⟶ splitSheaf := biprod.inr

/-- The actual diagonal pointwise scalar action on this sheaf. -/
def splitScalarEnd : ℂ →+* End splitSheaf :=
  GenericBiproduct.diagonalScalarEnd sphereScalarEnd negativeOneScalarEnd

@[reassoc] theorem splitScalarEnd_firstProjection (c : ℂ) :
    splitScalarEnd c ≫ splitFirstProjection = splitFirstProjection ≫ sphereScalarEnd c :=
  GenericBiproduct.diagonalScalarEnd_fst sphereScalarEnd negativeOneScalarEnd c

@[reassoc] theorem splitScalarEnd_secondProjection (c : ℂ) :
    splitScalarEnd c ≫ splitSecondProjection =
      splitSecondProjection ≫ negativeOneScalarEnd c :=
  GenericBiproduct.diagonalScalarEnd_snd sphereScalarEnd negativeOneScalarEnd c

@[reassoc] theorem splitFirstInclusion_scalar (c : ℂ) :
    splitFirstInclusion ≫ splitScalarEnd c = sphereScalarEnd c ≫ splitFirstInclusion :=
  GenericBiproduct.inl_diagonalScalarEnd sphereScalarEnd negativeOneScalarEnd c

@[reassoc] theorem splitSecondInclusion_scalar (c : ℂ) :
    splitSecondInclusion ≫ splitScalarEnd c =
      negativeOneScalarEnd c ≫ splitSecondInclusion :=
  GenericBiproduct.inr_diagonalScalarEnd sphereScalarEnd negativeOneScalarEnd c

/-- The additive group is the original native Ext group. -/
instance splitCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} splitSheaf n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The module comes from applying native cohomology to the diagonal
of the original scalar sheaf endomorphisms. -/
@[instance_reducible] def splitCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} splitSheaf n) :=
  cohomologyModule splitSheaf splitScalarEnd n

theorem splitCohomologyModule_smul (n : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} splitSheaf n) :
    letI := splitCohomologyModule n
    c • x = CategoryTheory.Sheaf.H.map (splitScalarEnd c) n x := rfl

/-- The actual native direct-sum cohomology comparison in every degree. -/
def splitCohomologyLinearEquiv (n : ℕ) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    CategoryTheory.Sheaf.H.{0} splitSheaf n ≃ₗ[ℂ]
      (CategoryTheory.Sheaf.H.{0} sphereSheaf n ×
        CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :=
  GenericBiproduct.cohomologyLinearEquiv sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd

/-- The first coordinate is the map of the original first projection. -/
@[simp] theorem splitCohomologyLinearEquiv_fst (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} splitSheaf n) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    (splitCohomologyLinearEquiv n x).1 =
      CategoryTheory.Sheaf.H.map splitFirstProjection n x :=
  GenericBiproduct.cohomologyLinearEquiv_fst sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd x

/-- The second coordinate is the map of the original second projection. -/
@[simp] theorem splitCohomologyLinearEquiv_snd (n : ℕ)
    (x : CategoryTheory.Sheaf.H.{0} splitSheaf n) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    (splitCohomologyLinearEquiv n x).2 =
      CategoryTheory.Sheaf.H.map splitSecondProjection n x :=
  GenericBiproduct.cohomologyLinearEquiv_snd sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd x

/-- The inverse is the sum of the two original inclusion maps on cohomology. -/
theorem splitCohomologyLinearEquiv_symm_apply (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} sphereSheaf n)
    (b : CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    (splitCohomologyLinearEquiv n).symm (a, b) =
      CategoryTheory.Sheaf.H.map splitFirstInclusion n a +
        CategoryTheory.Sheaf.H.map splitSecondInclusion n b :=
  GenericBiproduct.cohomologyLinearEquiv_symm_apply sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd a b

@[simp] theorem splitCohomologyLinearEquiv_symm_inl (n : ℕ)
    (a : CategoryTheory.Sheaf.H.{0} sphereSheaf n) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    (splitCohomologyLinearEquiv n).symm (a, 0) =
      CategoryTheory.Sheaf.H.map splitFirstInclusion n a :=
  GenericBiproduct.cohomologyLinearEquiv_symm_inl sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd a

@[simp] theorem splitCohomologyLinearEquiv_symm_inr (n : ℕ)
    (b : CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :
    letI := sphereCohomologyModule n
    letI := negativeOneCohomologyModule n
    letI := splitCohomologyModule n
    (splitCohomologyLinearEquiv n).symm (0, b) =
      CategoryTheory.Sheaf.H.map splitSecondInclusion n b :=
  GenericBiproduct.cohomologyLinearEquiv_symm_inr sphereSheaf negativeOneSheaf n
    sphereScalarEnd negativeOneScalarEnd b

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
