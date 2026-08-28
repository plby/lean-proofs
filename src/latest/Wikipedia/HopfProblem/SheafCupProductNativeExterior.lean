import Wikipedia.HopfProblem.SheafCupProductNativeLinear
import Wikipedia.HopfProblem.SheafCupProductExteriorBasic

/-!
# The native exterior-square cup map

The actual alternating native degree-one product factors through
Mathlib's original exterior square. Its generator formula and its
coefficient naturality are proved for the original cohomology maps.
No nonvanishing or isomorphism assertion is made here.
-/

noncomputable section

open CategoryTheory

namespace Wikipedia.HopfProblem.SheafCupProduct

open GodementRing

variable {X : TopCat.{0}} {F : RingSheaf X} (c : Scalars.Coefficients F)

/-- The genuine exterior-square map induced by the native sheaf cup product. -/
def exteriorCup :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    ⋀[ℂ]^2 (H F 1) →ₗ[ℂ] H F 2 := by
  letI := Scalars.cohomologyModule c 1
  letI := Scalars.cohomologyModule c 2
  exact exteriorPairing (linearCup c) (linearCup_self c)

@[simp] theorem exteriorCup_ιMulti (v : Fin 2 → H F 1) :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    exteriorCup c (exteriorPower.ιMulti ℂ 2 v) =
      cup F (Scalars.scalarEnd c) (v 0) (v 1) := by
  let := Scalars.cohomologyModule c 1
  let := Scalars.cohomologyModule c 2
  exact exteriorPairing_ιMulti (linearCup c) (linearCup_self c) v

variable {G : RingSheaf X} (f : F ⟶ G) (d : Scalars.Coefficients G)
  (h : Scalars.pushCoefficients f c = d)

/-- The original linear coefficient maps commute with the native exterior cup. -/
theorem exteriorCup_naturality :
    letI := Scalars.cohomologyModule c 1
    letI := Scalars.cohomologyModule c 2
    letI := Scalars.cohomologyModule d 1
    letI := Scalars.cohomologyModule d 2
    (Scalars.cohomologyMapLinear f c d h 2).comp (exteriorCup c) =
      (exteriorCup d).comp
        (exteriorPower.map 2 (Scalars.cohomologyMapLinear f c d h 1)) := by
  let := Scalars.cohomologyModule c 1
  let := Scalars.cohomologyModule c 2
  let := Scalars.cohomologyModule d 1
  let := Scalars.cohomologyModule d 2
  exact exteriorPairing_naturality
    (linearCup c) (linearCup_self c) (linearCup d) (linearCup_self d)
    (Scalars.cohomologyMapLinear f c d h 1)
    (Scalars.cohomologyMapLinear f c d h 2)
    (fun a b => cup_naturality f (Scalars.scalarEnd c) (Scalars.scalarEnd d) a b)

end Wikipedia.HopfProblem.SheafCupProduct
