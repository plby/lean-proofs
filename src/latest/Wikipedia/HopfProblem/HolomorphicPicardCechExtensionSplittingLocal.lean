import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionSplittingBasic
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionLocalLift

/-!
# Actual local degree-one sections and their differences

The explicit local degree lifts are sent through the genuine
sheafification unit. Their restriction and difference formulas retain
the original positive Čech sign. These formulas do not require
injectivity of the constant-sheaf unit.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory

namespace Wikipedia.HopfProblem.HolomorphicPicard.CechExtension

open HolomorphicFunctionSheaf.SphereH1

variable {X : TopCat.{0}} {F : TopCat.Sheaf AddCommGrpCat.{0} X}
  {ι : Type} {U : ι → Opens X} (c : CechOneCocycle F U)

/-- Literal integer representatives restrict to the same integer
under the actual constant-sheaf unit. -/
theorem res_degreeUnit {V W : Opens X} (hWV : W ≤ V) (n : ULift.{0} ℤ) :
    res (degreeSheaf X) hWV ((degreeUnit X).app (op V) n) =
      (degreeUnit X).app (op W) n :=
  (ConcreteCategory.congr_hom ((degreeUnit X).naturality (homOfLE hWV).op) n).symm

/-- The constructed degree-one local section of the actual extension sheaf. -/
def localDegreeOneSection (i : ι) : Section (extensionSheaf c) (U i) :=
  (unit c).app (op (U i)) (localLiftHom c i le_rfl (ULift.up (1 : ℤ)))

@[simp] theorem projection_localDegreeOneSection (i : ι) :
    (projection c).hom.app (op (U i)) (localDegreeOneSection c i) =
      (degreeUnit X).app (op (U i)) (ULift.up (1 : ℤ)) := by
  rw [localDegreeOneSection, projection_app_unit, localLiftHom_degree]

/-- The local degree-one section restricts to the same explicit lift
in the concrete extension presheaf. -/
theorem restrict_localDegreeOneSection (i : ι) {V : Opens X} (hVi : V ≤ U i) :
    res (extensionSheaf c) hVi (localDegreeOneSection c i) =
      (unit c).app (op V) (localLiftHom c i hVi (ULift.up (1 : ℤ))) := by
  change (extensionSheaf c).obj.map (homOfLE hVi).op
    ((unit c).app (op (U i)) (localLiftHom c i le_rfl (ULift.up (1 : ℤ)))) = _
  rw [unit_restrict, restrict_localLiftHom]

/-- The `j` local degree-one section minus the `i` section is exactly
the inclusion of the original cocycle on their actual intersection. -/
theorem localDegreeOneSection_difference (i j : ι) :
    res (extensionSheaf c) inf_le_right (localDegreeOneSection c j) -
      res (extensionSheaf c) inf_le_left (localDegreeOneSection c i) =
        (inclusion c).hom.app (op (U i ⊓ U j)) (c.value i j) := by
  let a : ExtensionSection c (U i ⊓ U j) :=
    localLiftHom c j inf_le_right (ULift.up (1 : ℤ))
  let b : ExtensionSection c (U i ⊓ U j) :=
    localLiftHom c i inf_le_left (ULift.up (1 : ℤ))
  let φ : ExtensionSection c (U i ⊓ U j) →+ Section (extensionSheaf c) (U i ⊓ U j) :=
    ((unit c).app (op (U i ⊓ U j))).hom
  have hab : a - b = includeHom c (U i ⊓ U j) (c.value i j) := by
    have h := localLiftHom_difference c i j inf_le_left inf_le_right (ULift.up (1 : ℤ))
    change a - b = includeHom c (U i ⊓ U j) ((1 : ℤ) • res F le_rfl (c.value i j)) at h
    simpa only [one_zsmul, res_refl] using h
  calc
    res (extensionSheaf c) inf_le_right (localDegreeOneSection c j) -
        res (extensionSheaf c) inf_le_left (localDegreeOneSection c i) = φ a - φ b := by
      rw [restrict_localDegreeOneSection, restrict_localDegreeOneSection]
      rfl
    _ = φ (a - b) := (φ.map_sub a b).symm
    _ = φ (includeHom c (U i ⊓ U j) (c.value i j)) := congrArg φ hab
    _ = (inclusion c).hom.app (op (U i ⊓ U j)) (c.value i j) := rfl

/-- A global degree-one section differs from each explicit local lift
by a section in the actual kernel of the projection. -/
theorem projection_globalSection_sub_localDegreeOne
    (s : Section (extensionSheaf c) (⊤ : Opens X))
    (hs : (projection c).hom.app (op (⊤ : Opens X)) s =
      (degreeUnit X).app (op (⊤ : Opens X)) (ULift.up (1 : ℤ))) (i : ι) :
    (projection c).hom.app (op (U i))
      (res (extensionSheaf c) le_top s - localDegreeOneSection c i) = 0 := by
  rw [map_sub, ← res_map (projection c) le_top s, hs,
    res_degreeUnit, projection_localDegreeOneSection, sub_self]

end Wikipedia.HopfProblem.HolomorphicPicard.CechExtension
