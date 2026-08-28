import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceGroups
import Wikipedia.HopfProblem.EllipticHigherHomologyRetractionSpecial

/-!
# Higher integral homology of the actual special elliptic fillings

The actual special local periods and the source's actual main twists
instantiate the proved surface and mapping-torus constructions.  Thus
the central surface, its literal reduced fibre, and the entire special
filling have the stated actual singular homology groups, with no period
family, topological comparison, or homology calculation supplied as an
extra input.  The coordinate formulas preserve the genuine inclusion
and the genuine finite period-torus covering.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology
open SingularMayerVietoris PeriodTorusHigherHomology

/-- The actual special central surface has integral second homology `ℤ²`. -/
def specialCentralSurfaceH2Equiv (j : Kind) :
    SingularHomology (SpecialCentralSurface j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  surfaceH2Equiv j (specialLocalData j).centralPeriod

/-- The actual special central surface has integral third homology `ℤ²`. -/
def specialCentralSurfaceH3Equiv (j : Kind) :
    SingularHomology (SpecialCentralSurface j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  surfaceH3Equiv j (specialLocalData j).centralPeriod

/-- The actual special central surface has integral fourth homology `ℤ`. -/
def specialCentralSurfaceH4Equiv (j : Kind) :
    SingularHomology (SpecialCentralSurface j) 4 ≃ₗ[ℤ] ℤ :=
  surfaceH4Equiv j (specialLocalData j).centralPeriod

/-- The literal reduced central fibre has the same actual second homology. -/
def specialCentralFibreH2Equiv (j : Kind) :
    SingularHomology (SpecialCentralFibre j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (specialCentralFibreHomologyEquiv j 2).symm.trans (specialCentralSurfaceH2Equiv j)

/-- The literal reduced central fibre has the same actual third homology. -/
def specialCentralFibreH3Equiv (j : Kind) :
    SingularHomology (SpecialCentralFibre j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  (specialCentralFibreHomologyEquiv j 3).symm.trans (specialCentralSurfaceH3Equiv j)

/-- The literal reduced central fibre has the same integral orientation group. -/
def specialCentralFibreH4Equiv (j : Kind) :
    SingularHomology (SpecialCentralFibre j) 4 ≃ₗ[ℤ] ℤ :=
  (specialCentralFibreHomologyEquiv j 4).symm.trans (specialCentralSurfaceH4Equiv j)

/-- The actual entire special filling has second integral homology `ℤ²`. -/
def specialFullFillingH2Equiv (j : Kind) :
    SingularHomology (SpecialFullFilling j) 2 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  fillingH2Equiv (specialLocalData j)

/-- The actual entire special filling has third integral homology `ℤ²`. -/
def specialFullFillingH3Equiv (j : Kind) :
    SingularHomology (SpecialFullFilling j) 3 ≃ₗ[ℤ] (Fin 2 → ℤ) :=
  fillingH3Equiv (specialLocalData j)

/-- The actual entire special filling has fourth integral homology `ℤ`. -/
def specialFullFillingH4Equiv (j : Kind) :
    SingularHomology (SpecialFullFilling j) 4 ≃ₗ[ℤ] ℤ :=
  fillingH4Equiv (specialLocalData j)

/-- The actual central inclusion is the identity in the displayed degree-two markings. -/
theorem specialFullFillingH2Equiv_centralInclusion (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 2) :
    specialFullFillingH2Equiv j
      (singularHomologyMap (specialCentralSurfaceIntoFilling j) 2 a) =
      specialCentralSurfaceH2Equiv j a :=
  fillingH2Equiv_centralInclusion (specialLocalData j) a

/-- The actual central inclusion preserves the displayed degree-three markings. -/
theorem specialFullFillingH3Equiv_centralInclusion (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 3) :
    specialFullFillingH3Equiv j
      (singularHomologyMap (specialCentralSurfaceIntoFilling j) 3 a) =
      specialCentralSurfaceH3Equiv j a :=
  fillingH3Equiv_centralInclusion (specialLocalData j) a

/-- The actual central inclusion preserves the displayed degree-four marking. -/
theorem specialFullFillingH4Equiv_centralInclusion (j : Kind)
    (a : SingularHomology (SpecialCentralSurface j) 4) :
    specialFullFillingH4Equiv j
      (singularHomologyMap (specialCentralSurfaceIntoFilling j) 4 a) =
      specialCentralSurfaceH4Equiv j a :=
  fillingH4Equiv_centralInclusion (specialLocalData j) a

/-- The genuine finite torus cover and the genuine inclusion have this actual degree-two map. -/
theorem specialFullFillingH2Equiv_periodCover (j : Kind)
    (a : SingularHomology (SpecialCentralPeriodTorus j) 2) :
    specialFullFillingH2Equiv j
      (singularHomologyMap (specialPeriodTorusIntoFilling j) 2 a) =
      specialCentralSurfaceH2Equiv j
        (singularHomologyMap (specialCentralPeriodCover j) 2 a) := by
  rw [← specialCentralSurfaceHomologyEquiv_periodCover]
  change specialCentralSurfaceH2Equiv j
    ((specialCentralSurfaceHomologyEquiv j 2).symm
      (specialCentralSurfaceHomologyEquiv j 2 _)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The same genuine finite-cover/inclusion diagram holds in degree three. -/
theorem specialFullFillingH3Equiv_periodCover (j : Kind)
    (a : SingularHomology (SpecialCentralPeriodTorus j) 3) :
    specialFullFillingH3Equiv j
      (singularHomologyMap (specialPeriodTorusIntoFilling j) 3 a) =
      specialCentralSurfaceH3Equiv j
        (singularHomologyMap (specialCentralPeriodCover j) 3 a) := by
  rw [← specialCentralSurfaceHomologyEquiv_periodCover]
  change specialCentralSurfaceH3Equiv j
    ((specialCentralSurfaceHomologyEquiv j 3).symm
      (specialCentralSurfaceHomologyEquiv j 3 _)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The same genuine finite-cover/inclusion diagram holds in top degree. -/
theorem specialFullFillingH4Equiv_periodCover (j : Kind)
    (a : SingularHomology (SpecialCentralPeriodTorus j) 4) :
    specialFullFillingH4Equiv j
      (singularHomologyMap (specialPeriodTorusIntoFilling j) 4 a) =
      specialCentralSurfaceH4Equiv j
        (singularHomologyMap (specialCentralPeriodCover j) 4 a) := by
  rw [← specialCentralSurfaceHomologyEquiv_periodCover]
  change specialCentralSurfaceH4Equiv j
    ((specialCentralSurfaceHomologyEquiv j 4).symm
      (specialCentralSurfaceHomologyEquiv j 4 _)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- No actual higher singular homology survives above degree four in the special surface. -/
theorem specialCentralSurface_homology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularHomology (SpecialCentralSurface j) n) :=
  surface_homology_subsingleton_of_lt j (specialLocalData j).centralPeriod hn

/-- The literal reduced central fibre has the same vanishing. -/
theorem specialCentralFibre_homology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularHomology (SpecialCentralFibre j) n) := by
  have := specialCentralSurface_homology_subsingleton_of_lt j hn
  exact (specialCentralFibreHomologyEquiv j n).symm.injective.subsingleton

/-- The entire special filling has the same vanishing. -/
theorem specialFullFilling_homology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularHomology (SpecialFullFilling j) n) :=
  filling_homology_subsingleton_of_lt (specialLocalData j) hn

/-- The actual special surface's higher integral homology is free. -/
theorem specialCentralSurface_higher_homology_free (j : Kind) {n : ℕ} (hn : 2 ≤ n) :
    Module.Free ℤ (SingularHomology (SpecialCentralSurface j) n) :=
  surface_higher_homology_free j (specialLocalData j).centralPeriod hn

/-- The entire special filling's higher integral homology is free. -/
theorem specialFullFilling_higher_homology_free (j : Kind) {n : ℕ} (hn : 2 ≤ n) :
    Module.Free ℤ (SingularHomology (SpecialFullFilling j) n) := by
  let := specialCentralSurface_higher_homology_free j hn
  exact Module.Free.of_equiv (specialCentralSurfaceHomologyEquiv j n)

/-- Consequently the actual special filling has no higher integral homology torsion. -/
theorem specialFullFilling_higher_homology_torsionFree (j : Kind) {n : ℕ} (hn : 2 ≤ n) :
    Module.IsTorsionFree ℤ (SingularHomology (SpecialFullFilling j) n) := by
  let := specialFullFilling_higher_homology_free j hn
  infer_instance

/-- The higher Betti numbers of the actual central surface. -/
theorem specialCentralSurface_higher_Betti_numbers (j : Kind) :
    Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) 2) = 2 ∧
    Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) 3) = 2 ∧
    Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) 4) = 1 :=
  ⟨surface_h2_finrank j _, surface_h3_finrank j _, surface_h4_finrank j _⟩

/-- The same higher Betti numbers hold for the actual entire special filling. -/
theorem specialFullFilling_higher_Betti_numbers (j : Kind) :
    Module.finrank ℤ (SingularHomology (SpecialFullFilling j) 2) = 2 ∧
    Module.finrank ℤ (SingularHomology (SpecialFullFilling j) 3) = 2 ∧
    Module.finrank ℤ (SingularHomology (SpecialFullFilling j) 4) = 1 := by
  rw [(specialFullFillingH2Equiv j).finrank_eq, (specialFullFillingH3Equiv j).finrank_eq,
    (specialFullFillingH4Equiv j).finrank_eq]
  simp

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
