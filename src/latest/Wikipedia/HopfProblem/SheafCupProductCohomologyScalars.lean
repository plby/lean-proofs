import Wikipedia.HopfProblem.SheafCupProductNativeNaturality
import Wikipedia.HopfProblem.SheafCupProductScalarsNaturality

/-!
# Original complex scalars on native ring-sheaf cohomology

The module structure is induced by the actual scalar endomorphisms of
the original additive sheaf through Mathlib's cohomology functor.
Consequently an original coefficient-preserving ring-sheaf morphism
induces a complex-linear map in every degree. No module structure is
transported through a cohomology calculation.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing

variable {X : TopCat.{0}} {F G : RingSheaf X}

/-- Original scalar endomorphisms induce the genuine cohomology module. -/
@[instance_reducible] def cohomologyModule (c : Coefficients F) (n : ℕ) :
    Module ℂ (H F n) :=
  CuspNormalization.SheafCohomology.cohomologyModule
    ((forgetSheaf X).obj F) (scalarEnd c) n

/-- Scalar multiplication is literally the map of the original scalar sheaf map. -/
theorem cohomology_smul (c : Coefficients F) (n : ℕ) (z : ℂ) (a : H F n) :
    letI := cohomologyModule c n
    z • a = CategoryTheory.Sheaf.H.map (scalarEnd c z).asHom n a := rfl

theorem cohomologyMap_scalar (f : F ⟶ G) (c : Coefficients F) (d : Coefficients G)
    (h : pushCoefficients f c = d) (n : ℕ) (z : ℂ) (a : H F n) :
    cohomologyMap f n (CategoryTheory.Sheaf.H.map (scalarEnd c z).asHom n a) =
      CategoryTheory.Sheaf.H.map (scalarEnd d z).asHom n (cohomologyMap f n a) := by
  have hl := CategoryTheory.Sheaf.H.map_comp_apply (scalarEnd c z).asHom
    ((forgetSheaf X).map f) a
  have hr := CategoryTheory.Sheaf.H.map_comp_apply ((forgetSheaf X).map f)
    (scalarEnd d z).asHom a
  have hm := congrArg
    (fun k : (forgetSheaf X).obj F ⟶ (forgetSheaf X).obj G =>
      CategoryTheory.Sheaf.H.map k n a)
    (scalarEnd_naturality_of_compatible f c d h z)
  exact hl.symm.trans (hm.trans hr)

/-- The original cohomology map is complex-linear for the original scalar actions. -/
def cohomologyMapLinear (f : F ⟶ G) (c : Coefficients F) (d : Coefficients G)
    (h : pushCoefficients f c = d) (n : ℕ) :
    letI := cohomologyModule c n
    letI := cohomologyModule d n
    H F n →ₗ[ℂ] H G n := by
  letI := cohomologyModule c n
  letI := cohomologyModule d n
  exact
    { toFun := cohomologyMap f n
      map_add' := (cohomologyMap f n).map_add
      map_smul' := cohomologyMap_scalar f c d h n }

@[simp] theorem cohomologyMapLinear_apply (f : F ⟶ G)
    (c : Coefficients F) (d : Coefficients G) (h : pushCoefficients f c = d)
    (n : ℕ) (a : H F n) :
    cohomologyMapLinear f c d h n a = cohomologyMap f n a := rfl

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
