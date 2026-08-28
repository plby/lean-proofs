import Wikipedia.HopfProblem.EllipticHigherHomologyProperties
import Wikipedia.HopfProblem.EllipticHigherHomologySpecial

/-!
# Every-degree integral homology of the actual special elliptic fillings

The constructed special periods instantiate the all-degree homology
coordinates.  The central surface, its literal reduced fibre, and the
entire filling have free, finitely generated, torsion-free integral
homology with Betti profile `(1, 2, 2, 2, 1)` and zero Euler sum.
The coordinates retain the actual central inclusion and finite torus
covering in every degree.
-/

noncomputable section

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology
open SingularMayerVietoris PeriodTorusHigherHomology
open scoped BigOperators

/-- Coordinates for every actual integral singular homology group of
the special central surface. -/
def specialCentralSurfaceHomologyCoordinates (j : Kind) (n : ℕ) :
    SingularHomology (SpecialCentralSurface j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  surfaceHomologyCoordinates j (specialLocalData j).centralPeriod n

/-- The literal reduced central fibre is identified through its actual
homeomorphism with the native central surface. -/
def specialCentralFibreHomologyCoordinates (j : Kind) (n : ℕ) :
    SingularHomology (SpecialCentralFibre j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  (specialCentralFibreHomologyEquiv j n).symm.trans
    (specialCentralSurfaceHomologyCoordinates j n)

/-- Coordinates for every actual integral singular homology group of
the full special filling. -/
def specialFullFillingHomologyCoordinates (j : Kind) (n : ℕ) :
    SingularHomology (SpecialFullFilling j) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  fillingHomologyCoordinates (specialLocalData j) n

theorem specialCentralSurface_homology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularHomology (SpecialCentralSurface j) n) :=
  Module.Free.of_equiv (specialCentralSurfaceHomologyCoordinates j n).symm

theorem specialCentralSurface_homology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (SpecialCentralSurface j) n) :=
  Module.Finite.of_surjective (specialCentralSurfaceHomologyCoordinates j n).symm.toLinearMap
    (specialCentralSurfaceHomologyCoordinates j n).symm.surjective

theorem specialCentralSurface_homology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (SpecialCentralSurface j) n) := by
  let := specialCentralSurface_homology_free j n
  infer_instance

theorem specialCentralSurface_homology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) n) =
      ellipticBettiNumber n := by
  rw [(specialCentralSurfaceHomologyCoordinates j n).finrank_eq]
  simp

theorem specialCentralFibre_homology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularHomology (SpecialCentralFibre j) n) :=
  Module.Free.of_equiv (specialCentralFibreHomologyCoordinates j n).symm

theorem specialCentralFibre_homology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (SpecialCentralFibre j) n) :=
  Module.Finite.of_surjective (specialCentralFibreHomologyCoordinates j n).symm.toLinearMap
    (specialCentralFibreHomologyCoordinates j n).symm.surjective

theorem specialCentralFibre_homology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (SpecialCentralFibre j) n) := by
  let := specialCentralFibre_homology_free j n
  infer_instance

theorem specialCentralFibre_homology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (SpecialCentralFibre j) n) =
      ellipticBettiNumber n := by
  rw [(specialCentralFibreHomologyCoordinates j n).finrank_eq]
  simp

theorem specialFullFilling_homology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularHomology (SpecialFullFilling j) n) :=
  Module.Free.of_equiv (specialFullFillingHomologyCoordinates j n).symm

theorem specialFullFilling_homology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (SpecialFullFilling j) n) :=
  Module.Finite.of_surjective (specialFullFillingHomologyCoordinates j n).symm.toLinearMap
    (specialFullFillingHomologyCoordinates j n).symm.surjective

theorem specialFullFilling_homology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (SpecialFullFilling j) n) := by
  let := specialFullFilling_homology_free j n
  infer_instance

theorem specialFullFilling_homology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (SpecialFullFilling j) n) =
      ellipticBettiNumber n := by
  rw [(specialFullFillingHomologyCoordinates j n).finrank_eq]
  simp

/-- The complete Betti vector of the actual central surface. -/
theorem specialCentralSurface_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialCentralSurface_homology_finrank]
  exact ellipticBettiNumber_firstFive

/-- The literal reduced central fibre has the same complete Betti vector. -/
theorem specialCentralFibre_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularHomology (SpecialCentralFibre j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialCentralFibre_homology_finrank]
  exact ellipticBettiNumber_firstFive

/-- The entire special filling has the same complete Betti vector. -/
theorem specialFullFilling_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularHomology (SpecialFullFilling j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialFullFilling_homology_finrank]
  exact ellipticBettiNumber_firstFive

/-- The native surface-to-reduced-fibre identification preserves these
integral coordinates in every degree. -/
theorem specialCentralFibreHomologyCoordinates_centralSurface (j : Kind) (n : ℕ)
    (a : SingularHomology (SpecialCentralSurface j) n) :
    specialCentralFibreHomologyCoordinates j n
      (specialCentralFibreHomologyEquiv j n a) =
      specialCentralSurfaceHomologyCoordinates j n a := by
  change specialCentralSurfaceHomologyCoordinates j n
    ((specialCentralFibreHomologyEquiv j n).symm
      (specialCentralFibreHomologyEquiv j n a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The actual central inclusion is the identity in the displayed
all-degree integral coordinates. -/
theorem specialFullFillingHomologyCoordinates_centralInclusion (j : Kind) (n : ℕ)
    (a : SingularHomology (SpecialCentralSurface j) n) :
    specialFullFillingHomologyCoordinates j n
      (singularHomologyMap (specialCentralSurfaceIntoFilling j) n a) =
      specialCentralSurfaceHomologyCoordinates j n a := by
  change specialCentralSurfaceHomologyCoordinates j n
    ((specialCentralSurfaceHomologyEquiv j n).symm
      (specialCentralSurfaceHomologyEquiv j n a)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The genuine finite period-torus covering and the central inclusion
give the same map in the all-degree integral coordinates. -/
theorem specialFullFillingHomologyCoordinates_periodCover (j : Kind) (n : ℕ)
    (a : SingularHomology (SpecialCentralPeriodTorus j) n) :
    specialFullFillingHomologyCoordinates j n
      (singularHomologyMap (specialPeriodTorusIntoFilling j) n a) =
      specialCentralSurfaceHomologyCoordinates j n
        (singularHomologyMap (specialCentralPeriodCover j) n a) := by
  rw [← specialCentralSurfaceHomologyEquiv_periodCover j n a]
  change specialCentralSurfaceHomologyCoordinates j n
    ((specialCentralSurfaceHomologyEquiv j n).symm
      (specialCentralSurfaceHomologyEquiv j n _)) = _
  rw [LinearEquiv.symm_apply_apply]

/-- The alternating sum of the actual central-surface homology ranks is zero. -/
theorem specialCentralSurface_homology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) n) : ℤ)) = 0 := by
  simp only [specialCentralSurface_homology_finrank]
  exact ellipticBettiNumber_euler_sum

/-- The literal reduced central fibre has the same zero Euler sum. -/
theorem specialCentralFibre_homology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialCentralFibre j) n) : ℤ)) = 0 := by
  simp only [specialCentralFibre_homology_finrank]
  exact ellipticBettiNumber_euler_sum

/-- The entire actual special filling has zero Euler sum. -/
theorem specialFullFilling_homology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialFullFilling j) n) : ℤ)) = 0 := by
  simp only [specialFullFilling_homology_finrank]
  exact ellipticBettiNumber_euler_sum

/-- Every cutoff beyond the top degree gives the same zero Euler sum
for the actual central surface. -/
theorem specialCentralSurface_homology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialCentralSurface j) n) : ℤ)) = 0 := by
  simp only [specialCentralSurface_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

/-- Every cutoff beyond the top degree gives the same zero Euler sum
for the literal reduced central fibre. -/
theorem specialCentralFibre_homology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialCentralFibre j) n) : ℤ)) = 0 := by
  simp only [specialCentralFibre_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

/-- Every cutoff beyond the top degree gives the same zero Euler sum
for the entire actual filling. -/
theorem specialFullFilling_homology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (SpecialFullFilling j) n) : ℤ)) = 0 := by
  simp only [specialFullFilling_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
