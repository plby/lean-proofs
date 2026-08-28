import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyRanks
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGroupMaps
import Wikipedia.HopfProblem.TrianglePeriodFamilyCanonicalRegular

/-!
# Singular homology of the constructed special regular family

Every period, covariance, covering, and monodromy input is the previously
constructed special one. Thus these statements concern the actual regular
family used in the threefold construction without additional geometric or
homological hypotheses. The displayed groups and maps are Mathlib's actual
integral singular homology, transported through proved equivalences.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical

open SpecialPeriods SingularMayerVietoris Homology
open CategoryTheory CategoryTheory.Limits

/-- The literal normalized fibre inclusion on actual singular homology. -/
def specialRegularFibreHomologyMap (n : ℕ) :
    SingularHomology RealTorus₄ n →ₗ[ℤ] SingularHomology SpecialRegularFamily n :=
  singularHomologyMap (familyFibreInclusion specialRegularData normalizedSlitBaseLift) n

/-- The actual all-degree integral homology marking of the constructed regular family. -/
def specialRegularHomologyEquiv (n : ℕ) :
    SingularHomology SpecialRegularFamily n ≃ₗ[ℤ] (Fin (familyBetti n) → ℤ) :=
  familyHomologyEquiv specialRegularData n

/-- Actual singular homology of the constructed regular family is free in every degree. -/
theorem specialRegularHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology SpecialRegularFamily n) :=
  family_homology_free specialRegularData n

theorem specialRegularHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology SpecialRegularFamily n) :=
  family_homology_finite specialRegularData n

theorem specialRegularHomology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology SpecialRegularFamily n) :=
  family_homology_torsionFree specialRegularData n

/-- The actual integral homology ranks, not just their rational counterparts. -/
theorem specialRegularHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology SpecialRegularFamily n) = familyBetti n :=
  family_homology_finrank specialRegularData n

theorem specialRegularHomology_rank_table :
    (fun n : Fin 6 => Module.finrank ℤ (SingularHomology SpecialRegularFamily n.val)) =
      ![1, 3, 6, 8, 6, 2] :=
  family_homology_rank_table specialRegularData

theorem specialRegularHomology_isZero_of_lt {n : ℕ} (hn : 5 < n) :
    IsZero (SingularHomology SpecialRegularFamily n) :=
  family_homology_isZero_of_lt specialRegularData hn

theorem specialRegularHomology_euler :
    ∑ n ∈ Finset.range 6,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology SpecialRegularFamily n) : ℤ) = 0 :=
  family_homology_euler specialRegularData

/-- The genuine singular-homology extension in the two source-meridian markings. -/
def specialRegularSourceExtension (n : ℕ) : ShortComplex (ModuleCat.{0} ℤ) :=
  familySourceExtension specialRegularData n

@[simp] theorem specialRegularSourceExtension_middle (n : ℕ) :
    (specialRegularSourceExtension n).X₂ = SingularHomology SpecialRegularFamily (n + 1) := rfl

theorem specialRegularSourceExtension_shortExact (n : ℕ) :
    (specialRegularSourceExtension n).ShortExact :=
  familySourceExtension_shortExact specialRegularData n

/-- The actual fibre map kills exactly the two integral monodromy differences. -/
theorem specialRegularFibreHomologyMap_kernel (n : ℕ) :
    LinearMap.ker (specialRegularFibreHomologyMap n) = LinearMap.range (sourceDifference n) :=
  familyFibreInclusion_kernel specialRegularData n

/-- The constructed regular family's first fibre map in its actual integral coordinates. -/
@[simp] theorem specialRegularHomology_fibre_one (a : SingularHomology RealTorus₄ 1) :
    specialRegularHomologyEquiv 1 (specialRegularFibreHomologyMap 1 a) =
      ![FlatTorus.singularH1Equiv a 0, 0, 0] :=
  familyH1Equiv_fibre specialRegularData a

/-- The actual primitive degree-two fibre map used by the later attachment calculation. -/
@[simp] theorem specialRegularHomology_fibre_two (a : SingularHomology RealTorus₄ 2) :
    specialRegularHomologyEquiv 2 (specialRegularFibreHomologyMap 2 a) =
      ![6 * FlatTorus.singularH2Coordinates a 2 + FlatTorus.singularH2Coordinates a 3,
        0, 0, 0, 0, 0] :=
  familyH2Equiv_fibre specialRegularData a

@[simp] theorem specialRegularHomology_fibre_three (a : SingularHomology RealTorus₄ 3) :
    specialRegularHomologyEquiv 3 (specialRegularFibreHomologyMap 3 a) =
      ![FlatTorus.singularH3Coordinates a 0, 0, 0, 0, 0, 0, 0, 0] :=
  familyH3Equiv_fibre specialRegularData a

@[simp] theorem specialRegularHomology_fibre_four (a : SingularHomology RealTorus₄ 4) :
    specialRegularHomologyEquiv 4 (specialRegularFibreHomologyMap 4 a) =
      ![PeriodTorusHigherHomology.realTorusH4Equiv a, 0, 0, 0, 0, 0] :=
  familyH4Equiv_fibre specialRegularData a

end Wikipedia.HopfProblem.TrianglePeriodFamily.Canonical
