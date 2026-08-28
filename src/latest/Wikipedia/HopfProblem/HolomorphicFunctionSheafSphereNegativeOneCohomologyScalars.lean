import Wikipedia.HopfProblem.HolomorphicFunctionSheafSphereH1NegativeOneSheaf
import Wikipedia.HopfProblem.CuspNormalizationSheafCohomologyScalarResolutionBasic

/-!
# Actual complex scalar actions on the sphere and its infinity ideal

The scalar endomorphisms act by literal pointwise multiplication on the
existing section groups. Their images under the native cohomology
functor define the modules on genuine Ext-defined sheaf cohomology.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology

open CuspNormalization.SheafCohomology
open CuspNormalization.SheafCohomologyScalarResolution

/-- Actual restrictions of sections of the infinity ideal are complex linear. -/
theorem negativeOne_restriction_smul {U V} (h : U ⟶ V) (c : ℂ)
    (s : negativeOneSheaf.presheaf.obj U) :
    negativeOneSheaf.presheaf.map h (c • s) =
      c • negativeOneSheaf.presheaf.map h s :=
  (negativeOneRestrictionLinearMap (leOfHom h.unop)).map_smul c s

/-- The scalar ring homomorphism on the actual ideal sheaf. -/
def negativeOneScalarEnd : ℂ →+* End negativeOneSheaf :=
  pointwiseScalarEnd negativeOneSheaf negativeOne_restriction_smul

/-- These scalar maps multiply actual ideal sections pointwise. -/
@[simp] theorem negativeOneScalarEnd_apply (c : ℂ) (U : Opens RiemannSphere)
    (s : NegativeOneSection U) :
    (negativeOneScalarEnd c).hom.app (op U) s = c • s := rfl

/-- The original pointwise scalar action on the holomorphic sphere sheaf. -/
def sphereScalarEnd : ℂ →+* End sphereSheaf :=
  holomorphicScalarEnd 𝓘(ℂ) RiemannSphere

@[simp] theorem sphereScalarEnd_apply (c : ℂ) (U : Opens RiemannSphere)
    (s : HolomorphicFunctionSheaf.Section 𝓘(ℂ) RiemannSphere U) :
    (sphereScalarEnd c).hom.app (op U) s = c • s := rfl

/-- The genuine ideal inclusion respects the original scalar actions. -/
@[reassoc] theorem negativeOneInclusion_scalar (c : ℂ) :
    negativeOneScalarEnd c ≫ negativeOneInclusion =
      negativeOneInclusion ≫ sphereScalarEnd c := by
  apply CategoryTheory.Sheaf.hom_ext
  apply NatTrans.ext
  funext U
  apply AddCommGrpCat.hom_ext
  apply AddMonoidHom.ext
  intro s
  rfl

/-- The additive group is the original one on the actual Ext group. -/
instance negativeOneCohomologyAddCommGroup (n : ℕ) :
    AddCommGroup (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :=
  CategoryTheory.Abelian.Ext.instAddCommGroup

/-- The native sheaf-induced module on each genuine ideal cohomology group. -/
@[instance_reducible] def negativeOneCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :=
  cohomologyModule negativeOneSheaf negativeOneScalarEnd n

/-- Scalar multiplication is the cohomology map of the original scalar sheaf map. -/
theorem negativeOneCohomologyModule_smul (n : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} negativeOneSheaf n) :
    letI := negativeOneCohomologyModule n
    c • x = CategoryTheory.Sheaf.H.map (negativeOneScalarEnd c) n x := rfl

/-- The native sheaf-induced module on each sphere cohomology group. -/
@[instance_reducible] def sphereCohomologyModule (n : ℕ) :
    Module ℂ (CategoryTheory.Sheaf.H.{0} sphereSheaf n) :=
  cohomologyModule sphereSheaf sphereScalarEnd n

/-- The scalar action uses the original holomorphic scalar endomorphism. -/
theorem sphereCohomologyModule_smul (n : ℕ) (c : ℂ)
    (x : CategoryTheory.Sheaf.H.{0} sphereSheaf n) :
    letI := sphereCohomologyModule n
    c • x = CategoryTheory.Sheaf.H.map (sphereScalarEnd c) n x := rfl

end Wikipedia.HopfProblem.HolomorphicFunctionSheaf.SphereH1.NegativeOneCohomology
