import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologySpaces

/-!
# The complete native cohomology profile of the elliptic spaces

The actual mapping torus, central surface and full filling have integral
singular cohomology ranks `(1,2,2,2,1,0,...)`.  Their cohomology is finite
free and torsion-free in every degree.  Every class above degree four
vanishes.  These are consequences of the native cochain evaluation
isomorphism and the already proved actual homology computations.
-/

noncomputable section

open scoped BigOperators

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularCohomologyFree

theorem mappingTorus_cohomology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (mappingTorusModel j) n) :=
  cohomology_free_of_homology_coordinates (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n

theorem mappingTorus_cohomology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (mappingTorusModel j) n) :=
  cohomology_finite_of_homology_coordinates (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n

theorem mappingTorus_cohomology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (mappingTorusModel j) n) :=
  cohomology_torsionFree_of_homology_coordinates (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n

theorem mappingTorus_cohomology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (mappingTorusModel j) n) = ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n

theorem mappingTorus_cohomology_subsingleton (j : Kind) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularCohomology (mappingTorusModel j) n) :=
  cohomology_subsingleton_of_homology_coordinates (mappingTorusModel j) ellipticBettiNumber
    (mappingTorusHomologyCoordinates j) n
    (ellipticBettiNumber_eq_zero_of_lt hn)

theorem mappingTorus_cohomology_eq_zero (j : Kind) {n : ℕ} (hn : 4 < n)
    (a : SingularCohomology (mappingTorusModel j) n) : a = 0 := by
  let := mappingTorus_cohomology_subsingleton j hn
  exact Subsingleton.elim _ _

theorem mappingTorus_cohomology_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularCohomology (mappingTorusModel j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [mappingTorus_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem mappingTorus_cohomology_eulerCharacteristic_zero (j : Kind) :
    (∑ n ∈ Finset.range 5,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularCohomology (mappingTorusModel j) n) : ℤ)) = 0 := by
  simp_rw [mappingTorus_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem mappingTorus_cohomology_eulerCharacteristic_zero_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularCohomology (mappingTorusModel j) n) : ℤ)) = 0 := by
  simp_rw [mappingTorus_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

theorem surface_cohomology_free (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  cohomology_free_of_homology_coordinates
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n

theorem surface_cohomology_finite (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  cohomology_finite_of_homology_coordinates
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n

theorem surface_cohomology_torsionFree (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  cohomology_torsionFree_of_homology_coordinates
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n

theorem surface_cohomology_finrank (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) =
      ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n

theorem surface_cohomology_subsingleton (j : Kind) (p : FixedPeriod j) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  cohomology_subsingleton_of_homology_coordinates
    (Surface j p j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (surfaceHomologyCoordinates j p) n
    (ellipticBettiNumber_eq_zero_of_lt hn)

theorem surface_cohomology_eq_zero (j : Kind) (p : FixedPeriod j) {n : ℕ} (hn : 4 < n)
    (a : SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) : a = 0 := by
  let := surface_cohomology_subsingleton j p hn
  exact Subsingleton.elim _ _

theorem surface_cohomology_Betti_numbers (j : Kind) (p : FixedPeriod j) :
    (fun n : Fin 5 => Module.finrank ℤ
      (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [surface_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem surface_cohomology_eulerCharacteristic_zero (j : Kind) (p : FixedPeriod j) :
    (∑ n ∈ Finset.range 5,
      (-1 : ℤ) ^ n * (Module.finrank ℤ
        (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [surface_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem surface_cohomology_eulerCharacteristic_zero_of_ge (j : Kind) (p : FixedPeriod j)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank ℤ
        (SingularCohomology (Surface j p j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [surface_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

theorem filling_cohomology_free {j : Kind} (D : Equivariant.Data j) (n : ℕ) :
    Module.Free ℤ (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  cohomology_free_of_homology_coordinates
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n

theorem filling_cohomology_finite {j : Kind} (D : Equivariant.Data j) (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  cohomology_finite_of_homology_coordinates
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n

theorem filling_cohomology_torsionFree {j : Kind} (D : Equivariant.Data j) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  cohomology_torsionFree_of_homology_coordinates
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n

theorem filling_cohomology_finrank {j : Kind} (D : Equivariant.Data j) (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) =
      ellipticBettiNumber n :=
  cohomology_finrank_of_homology_coordinates
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n

theorem filling_cohomology_subsingleton {j : Kind} (D : Equivariant.Data j) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  cohomology_subsingleton_of_homology_coordinates
    (D.Space j.twist (mainTwist_admissible j)) ellipticBettiNumber
    (fillingHomologyCoordinates D) n
    (ellipticBettiNumber_eq_zero_of_lt hn)

theorem filling_cohomology_eq_zero {j : Kind} (D : Equivariant.Data j) {n : ℕ} (hn : 4 < n)
    (a : SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) : a = 0 := by
  let := filling_cohomology_subsingleton D hn
  exact Subsingleton.elim _ _

theorem filling_cohomology_Betti_numbers {j : Kind} (D : Equivariant.Data j) :
    (fun n : Fin 5 => Module.finrank ℤ
      (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [filling_cohomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem filling_cohomology_eulerCharacteristic_zero {j : Kind} (D : Equivariant.Data j) :
    (∑ n ∈ Finset.range 5,
      (-1 : ℤ) ^ n * (Module.finrank ℤ
        (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [filling_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem filling_cohomology_eulerCharacteristic_zero_of_ge {j : Kind} (D : Equivariant.Data j)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank ℤ
        (SingularCohomology (D.Space j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [filling_cohomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

end Wikipedia.HopfProblem.Elliptic.HigherHomology
