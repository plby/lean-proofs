import Wikipedia.HopfProblem.EllipticHigherHomologySpecialCohomologyCoordinates

/-!
# Every-degree native cohomology of the special elliptic spaces

The native integral singular cohomology of the actual special central
surface, its literal reduced fibre, and the full filling is free,
finitely generated, and torsion-free in every degree.  Its ranks are
`(1, 2, 2, 2, 1)`, with vanishing above degree four and zero Euler sum.
All statements use the proved native-cochain evaluation equivalence.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling

open Elliptic Elliptic.HigherHomology SingularCohomologyFree

/-- Native integral cohomology of the actual special central surface is free in every degree. -/
theorem specialCentralSurface_cohomology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (SpecialCentralSurface j) n) :=
  cohomology_free_of_homology_coordinates (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n

theorem specialCentralSurface_cohomology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (SpecialCentralSurface j) n) :=
  cohomology_finite_of_homology_coordinates (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n

theorem specialCentralSurface_cohomology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (SpecialCentralSurface j) n) :=
  cohomology_torsionFree_of_homology_coordinates (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n

theorem specialCentralSurface_cohomology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (SpecialCentralSurface j) n) = ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n

/-- Every native cohomology class above degree four vanishes. -/
theorem specialCentralSurface_cohomology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularCohomology (SpecialCentralSurface j) n) :=
  cohomology_subsingleton_of_homology_coordinates (SpecialCentralSurface j) ellipticBettiNumber
    (specialCentralSurfaceHomologyCoordinates j) n (ellipticBettiNumber_eq_zero_of_lt hn)

theorem specialCentralSurface_cohomology_eq_zero_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) (a : SingularCohomology (SpecialCentralSurface j) n) : a = 0 := by
  let := specialCentralSurface_cohomology_subsingleton_of_lt j hn
  exact Subsingleton.elim _ _

/-- The complete finite Betti profile of the native cohomology groups. -/
theorem specialCentralSurface_cohomology_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularCohomology (SpecialCentralSurface j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialCentralSurface_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem specialCentralSurface_cohomology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialCentralSurface j) n) : ℤ)) = 0 := by
  simp only [specialCentralSurface_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem specialCentralSurface_cohomology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialCentralSurface j) n) : ℤ)) = 0 := by
  simp only [specialCentralSurface_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

/-- Native integral cohomology of the literal reduced central fibre is free in every degree. -/
theorem specialCentralFibre_cohomology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (SpecialCentralFibre j) n) :=
  cohomology_free_of_homology_coordinates (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n

theorem specialCentralFibre_cohomology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (SpecialCentralFibre j) n) :=
  cohomology_finite_of_homology_coordinates (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n

theorem specialCentralFibre_cohomology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (SpecialCentralFibre j) n) :=
  cohomology_torsionFree_of_homology_coordinates (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n

theorem specialCentralFibre_cohomology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (SpecialCentralFibre j) n) = ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n

/-- Every native cohomology class above degree four vanishes. -/
theorem specialCentralFibre_cohomology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularCohomology (SpecialCentralFibre j) n) :=
  cohomology_subsingleton_of_homology_coordinates (SpecialCentralFibre j) ellipticBettiNumber
    (specialCentralFibreHomologyCoordinates j) n (ellipticBettiNumber_eq_zero_of_lt hn)

theorem specialCentralFibre_cohomology_eq_zero_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) (a : SingularCohomology (SpecialCentralFibre j) n) : a = 0 := by
  let := specialCentralFibre_cohomology_subsingleton_of_lt j hn
  exact Subsingleton.elim _ _

/-- The complete finite Betti profile of the native cohomology groups. -/
theorem specialCentralFibre_cohomology_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularCohomology (SpecialCentralFibre j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialCentralFibre_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem specialCentralFibre_cohomology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialCentralFibre j) n) : ℤ)) = 0 := by
  simp only [specialCentralFibre_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem specialCentralFibre_cohomology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialCentralFibre j) n) : ℤ)) = 0 := by
  simp only [specialCentralFibre_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

/-- Native integral cohomology of the entire special filling is free in every degree. -/
theorem specialFullFilling_cohomology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (SpecialFullFilling j) n) :=
  cohomology_free_of_homology_coordinates (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n

theorem specialFullFilling_cohomology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (SpecialFullFilling j) n) :=
  cohomology_finite_of_homology_coordinates (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n

theorem specialFullFilling_cohomology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (SpecialFullFilling j) n) :=
  cohomology_torsionFree_of_homology_coordinates (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n

theorem specialFullFilling_cohomology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (SpecialFullFilling j) n) = ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n

/-- Every native cohomology class above degree four vanishes. -/
theorem specialFullFilling_cohomology_subsingleton_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) : Subsingleton (SingularCohomology (SpecialFullFilling j) n) :=
  cohomology_subsingleton_of_homology_coordinates (SpecialFullFilling j) ellipticBettiNumber
    (specialFullFillingHomologyCoordinates j) n (ellipticBettiNumber_eq_zero_of_lt hn)

theorem specialFullFilling_cohomology_eq_zero_of_lt (j : Kind)
    {n : ℕ} (hn : 4 < n) (a : SingularCohomology (SpecialFullFilling j) n) : a = 0 := by
  let := specialFullFilling_cohomology_subsingleton_of_lt j hn
  exact Subsingleton.elim _ _

/-- The complete finite Betti profile of the native cohomology groups. -/
theorem specialFullFilling_cohomology_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularCohomology (SpecialFullFilling j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [specialFullFilling_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem specialFullFilling_cohomology_euler_sum (j : Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialFullFilling j) n) : ℤ)) = 0 := by
  simp only [specialFullFilling_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem specialFullFilling_cohomology_euler_sum_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularCohomology (SpecialFullFilling j) n) : ℤ)) = 0 := by
  simp only [specialFullFilling_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

end Wikipedia.HopfProblem.SpecialPeriods.EllipticFilling
