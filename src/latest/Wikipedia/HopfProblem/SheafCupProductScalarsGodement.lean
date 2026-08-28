import Wikipedia.HopfProblem.SheafCupProductScalarsNaturality
import Wikipedia.HopfProblem.SheafCupProductGodementCofaces

/-!
# The actual Godement faces preserve the original constants

At each successive term the global constants are inserted by the
original germ inclusion. Its naturality proves that every coface,
including each interior insertion, sends these constants to the next
ones. Thus all actual section cofaces are complex-linear.
-/

noncomputable section

open CategoryTheory TopologicalSpace Opposite

namespace Wikipedia.HopfProblem.SheafCupProduct.Scalars

open GodementRing

variable {X : TopCat.{0}} {F G : RingSheaf X}

/-- The next constants are the actual germs of the previous global constants. -/
def nextCoefficients (c : Coefficients F) : Coefficients (sheaf F) :=
  pushCoefficients (inclusion F) c

theorem nextCoefficients_naturality (f : F ⟶ G) (c : Coefficients F) :
    pushCoefficients (map f) (nextCoefficients c) =
      nextCoefficients (pushCoefficients f c) := by
  change pushCoefficients (map f) (pushCoefficients (inclusion F) c) =
    pushCoefficients (inclusion G) (pushCoefficients f c)
  rw [← pushCoefficients_comp, inclusion_naturality, pushCoefficients_comp]

abbrev coefficients0 (c : Coefficients F) : Coefficients (term0 F) := nextCoefficients c
abbrev coefficients1 (c : Coefficients F) : Coefficients (term1 F) :=
  nextCoefficients (coefficients0 c)
abbrev coefficients2 (c : Coefficients F) : Coefficients (term2 F) :=
  nextCoefficients (coefficients1 c)
abbrev coefficients3 (c : Coefficients F) : Coefficients (term3 F) :=
  nextCoefficients (coefficients2 c)

theorem face0_coefficients (c : Coefficients F) (i : Fin 2) :
    pushCoefficients (face0 F i) (coefficients0 c) = coefficients1 c := by
  fin_cases i
  · rfl
  · exact nextCoefficients_naturality (inclusion F) c

theorem face1_coefficients (c : Coefficients F) (i : Fin 3) :
    pushCoefficients (face1 F i) (coefficients1 c) = coefficients2 c := by
  fin_cases i
  · rfl
  · exact nextCoefficients_naturality (inclusion (term0 F)) (coefficients0 c)
  · change pushCoefficients (map (face0 F 1)) (nextCoefficients (coefficients0 c)) =
      nextCoefficients (coefficients1 c)
    rw [nextCoefficients_naturality, face0_coefficients]

theorem face2_coefficients (c : Coefficients F) (i : Fin 4) :
    pushCoefficients (face2 F i) (coefficients2 c) = coefficients3 c := by
  fin_cases i
  · rfl
  · exact nextCoefficients_naturality (inclusion (term1 F)) (coefficients1 c)
  · change pushCoefficients (map (face1 F 1)) (nextCoefficients (coefficients1 c)) =
      nextCoefficients (coefficients2 c)
    rw [nextCoefficients_naturality, face1_coefficients]
  · change pushCoefficients (map (face1 F 2)) (nextCoefficients (coefficients1 c)) =
      nextCoefficients (coefficients2 c)
    rw [nextCoefficients_naturality, face1_coefficients]

theorem face0_scalar (c : Coefficients F) (i : Fin 2) (z : ℂ) :
    (scalarEnd (coefficients0 c) z).asHom ≫ (forgetSheaf X).map (face0 F i) =
      (forgetSheaf X).map (face0 F i) ≫ (scalarEnd (coefficients1 c) z).asHom :=
  scalarEnd_naturality_of_compatible _ _ _ (face0_coefficients c i) z

theorem face1_scalar (c : Coefficients F) (i : Fin 3) (z : ℂ) :
    (scalarEnd (coefficients1 c) z).asHom ≫ (forgetSheaf X).map (face1 F i) =
      (forgetSheaf X).map (face1 F i) ≫ (scalarEnd (coefficients2 c) z).asHom :=
  scalarEnd_naturality_of_compatible _ _ _ (face1_coefficients c i) z

theorem face2_scalar (c : Coefficients F) (i : Fin 4) (z : ℂ) :
    (scalarEnd (coefficients2 c) z).asHom ≫ (forgetSheaf X).map (face2 F i) =
      (forgetSheaf X).map (face2 F i) ≫ (scalarEnd (coefficients3 c) z).asHom :=
  scalarEnd_naturality_of_compatible _ _ _ (face2_coefficients c i) z

/-- The first actual section cofaces as complex-linear maps. -/
def face0Linear (c : Coefficients F) (U : (Opens X)ᵒᵖ) (i : Fin 2) :
    letI := sectionModule (coefficients0 c) U
    letI := sectionModule (coefficients1 c) U
    (term0 F).presheaf.obj U →ₗ[ℂ] (term1 F).presheaf.obj U :=
  sectionMapLinear _ _ _ (face0_coefficients c i) U

def face1Linear (c : Coefficients F) (U : (Opens X)ᵒᵖ) (i : Fin 3) :
    letI := sectionModule (coefficients1 c) U
    letI := sectionModule (coefficients2 c) U
    (term1 F).presheaf.obj U →ₗ[ℂ] (term2 F).presheaf.obj U :=
  sectionMapLinear _ _ _ (face1_coefficients c i) U

def face2Linear (c : Coefficients F) (U : (Opens X)ᵒᵖ) (i : Fin 4) :
    letI := sectionModule (coefficients2 c) U
    letI := sectionModule (coefficients3 c) U
    (term2 F).presheaf.obj U →ₗ[ℂ] (term3 F).presheaf.obj U :=
  sectionMapLinear _ _ _ (face2_coefficients c i) U

end Wikipedia.HopfProblem.SheafCupProduct.Scalars
