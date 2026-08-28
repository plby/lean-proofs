import Wikipedia.HopfProblem.EllipticHigherHomologyMappingTorusLowDegrees
import Wikipedia.HopfProblem.EllipticHigherHomologySurfaceGroups

/-!
# The full integral homology profile of the actual elliptic fillings

The actual marked homology equivalences in degrees zero through four,
and the proved higher vanishing, give one all-degree coordinate system.
It has ranks `(1,2,2,2,1,0,...)`.  Freeness, finite generation and absence
of integral torsion follow from these actual linear equivalences.

The surface coordinates are induced by the genuine surface-to-mapping-
torus homeomorphism.  The filling coordinates are induced by the genuine
deformation retraction and retain the actual central inclusion.  The
low-degree point-class, fibre-inclusion and signed Wang-boundary markings
are those already constructed, rather than replacement choices.
-/

noncomputable section

namespace Wikipedia.HopfProblem.Elliptic.HigherHomology

open SingularMayerVietoris PeriodTorusHigherHomology MappingTorusHomology

/-- The actual homology ranks, including vanishing in every higher degree. -/
def ellipticBettiNumber : ℕ → ℕ
  | 0 => 1
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 1
  | _ + 5 => 0

@[simp] theorem ellipticBettiNumber_zero : ellipticBettiNumber 0 = 1 := rfl
@[simp] theorem ellipticBettiNumber_one : ellipticBettiNumber 1 = 2 := rfl
@[simp] theorem ellipticBettiNumber_two : ellipticBettiNumber 2 = 2 := rfl
@[simp] theorem ellipticBettiNumber_three : ellipticBettiNumber 3 = 2 := rfl
@[simp] theorem ellipticBettiNumber_four : ellipticBettiNumber 4 = 1 := rfl
@[simp] theorem ellipticBettiNumber_add_five (n : ℕ) : ellipticBettiNumber (n + 5) = 0 := rfl

theorem ellipticBettiNumber_eq_zero_of_lt {n : ℕ} (hn : 4 < n) :
    ellipticBettiNumber n = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 5 := ⟨n - 5, by omega⟩
  rfl

theorem ellipticBettiNumber_firstFive :
    (fun i : Fin 5 => ellipticBettiNumber i) = ![1, 2, 2, 2, 1] := by
  ext i
  fin_cases i <;> rfl

theorem ellipticBettiNumber_euler_sum :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n * (ellipticBettiNumber n : ℤ)) = 0 := by
  decide

/-- Every cutoff beyond the top degree gives the same full Euler sum. -/
theorem ellipticBettiNumber_euler_sum_of_ge {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (ellipticBettiNumber n : ℤ)) = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, N = 5 + k := ⟨N - 5, by omega⟩
  clear hN
  induction k with
  | zero => exact ellipticBettiNumber_euler_sum
  | succ k ih =>
    rw [Nat.add_succ, Finset.sum_range_succ, ih,
      ellipticBettiNumber_eq_zero_of_lt (show 4 < 5 + k by omega)]
    simp

/-- All-degree coordinates on actual mapping-torus integral homology.
The low-degree branches use exactly the previously proved markings. -/
def mappingTorusHomologyCoordinates (j : Kind) : (n : ℕ) →
    SingularHomology (mappingTorusModel j) n ≃ₗ[ℤ] (Fin (ellipticBettiNumber n) → ℤ)
  | 0 => (mappingTorusH0Equiv j).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => mappingTorusH1Equiv j
  | 2 => mappingTorusH2Equiv j
  | 3 => mappingTorusH3Equiv j
  | 4 => (mappingTorusH4Equiv j).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | n + 5 => by
    have := threeTorusMappingTorus_homology_subsingleton (fibreTorusHomeomorph j).symm
      (show 4 < n + 5 by omega)
    exact LinearEquiv.ofSubsingleton _ (Fin 0 → ℤ)

@[simp] theorem mappingTorusHomologyCoordinates_zero (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 0) :
    mappingTorusHomologyCoordinates j 0 a (0 : Fin 1) = mappingTorusH0Equiv j a := rfl

@[simp] theorem mappingTorusHomologyCoordinates_one (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 1) :
    mappingTorusHomologyCoordinates j 1 a = mappingTorusH1Equiv j a := rfl

@[simp] theorem mappingTorusHomologyCoordinates_two (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 2) :
    mappingTorusHomologyCoordinates j 2 a = mappingTorusH2Equiv j a := rfl

@[simp] theorem mappingTorusHomologyCoordinates_three (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 3) :
    mappingTorusHomologyCoordinates j 3 a = mappingTorusH3Equiv j a := rfl

@[simp] theorem mappingTorusHomologyCoordinates_four (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 4) :
    mappingTorusHomologyCoordinates j 4 a (0 : Fin 1) = mappingTorusH4Equiv j a := rfl

/-- The uniform coordinates retain the actual positive point class. -/
@[simp] theorem mappingTorusHomologyCoordinates_zero_pointClass
    (j : Kind) (x : ProductTorus 3) :
    mappingTorusHomologyCoordinates j 0
      (pointClass (MappingTorus.HomologyCover.fibreInclusion
        (fibreTorusHomeomorph j).symm x)) (0 : Fin 1) = 1 :=
  mappingTorusH0Equiv_fibre_pointClass j x

/-- The uniform first-homology coordinates retain the actual Wang boundary. -/
theorem mappingTorusHomologyCoordinates_one_boundary (j : Kind)
    (a : SingularHomology (mappingTorusModel j) 1) :
    mappingTorusHomologyCoordinates j 1 a (1 : Fin 2) =
      torusH0Coordinates (wangBoundary (fibreTorusHomeomorph j).symm 0 a) :=
  mappingTorusH1Equiv_boundary j a

/-- The uniform coordinates retain the actual first-homology fibre map. -/
theorem mappingTorusHomologyCoordinates_one_fibre (j : Kind)
    (a : SingularHomology (ProductTorus 3) 1) :
    mappingTorusHomologyCoordinates j 1
      (fibreHomologyMap (fibreTorusHomeomorph j).symm 1 a) =
      ![fibreCoinvariantCoordinate j (torusH1Equiv a), 0] :=
  mappingTorusH1Equiv_fibre j a

theorem mappingTorus_homology_free (j : Kind) (n : ℕ) :
    Module.Free ℤ (SingularHomology (mappingTorusModel j) n) :=
  Module.Free.of_equiv (mappingTorusHomologyCoordinates j n).symm

theorem mappingTorus_homology_finite (j : Kind) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (mappingTorusModel j) n) :=
  Module.Finite.of_surjective (mappingTorusHomologyCoordinates j n).symm.toLinearMap
    (mappingTorusHomologyCoordinates j n).symm.surjective

theorem mappingTorus_homology_torsionFree (j : Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (mappingTorusModel j) n) := by
  let := mappingTorus_homology_free j n
  infer_instance

/-- The actual Betti numbers in every degree, including all higher zeros. -/
theorem mappingTorus_homology_finrank (j : Kind) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (mappingTorusModel j) n) = ellipticBettiNumber n := by
  rw [(mappingTorusHomologyCoordinates j n).finrank_eq]
  simp

theorem mappingTorus_Betti_numbers (j : Kind) :
    (fun n : Fin 5 => Module.finrank ℤ (SingularHomology (mappingTorusModel j) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [mappingTorus_homology_finrank]
  exact ellipticBettiNumber_firstFive

/-- The alternating sum uses the ranks of the actual singular homology groups. -/
theorem mappingTorus_eulerCharacteristic_zero (j : Kind) :
    (∑ n ∈ Finset.range 5,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology (mappingTorusModel j) n) : ℤ)) = 0 := by
  simp_rw [mappingTorus_homology_finrank]
  exact ellipticBettiNumber_euler_sum

/-- The same actual Euler sum is zero for every sufficiently large cutoff. -/
theorem mappingTorus_eulerCharacteristic_zero_of_ge (j : Kind)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology (mappingTorusModel j) n) : ℤ)) = 0 := by
  simp_rw [mappingTorus_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

/-- Uniform coordinates on the actual main-twist central surface. -/
def surfaceHomologyCoordinates (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  (surfaceMappingTorusHomologyEquiv j p n).trans (mappingTorusHomologyCoordinates j n)

@[simp] theorem surfaceHomologyCoordinates_apply (j : Kind) (p : FixedPeriod j) (n : ℕ)
    (a : SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) :
    surfaceHomologyCoordinates j p n a =
      mappingTorusHomologyCoordinates j n (surfaceMappingTorusHomologyEquiv j p n a) := rfl

theorem surface_homology_free (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.Free ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  Module.Free.of_equiv (surfaceHomologyCoordinates j p n).symm

theorem surface_homology_finite (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) :=
  Module.Finite.of_surjective (surfaceHomologyCoordinates j p n).symm.toLinearMap
    (surfaceHomologyCoordinates j p n).symm.surjective

theorem surface_homology_torsionFree (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) := by
  let := surface_homology_free j p n
  infer_instance

theorem surface_homology_finrank (j : Kind) (p : FixedPeriod j) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) =
      ellipticBettiNumber n := by
  rw [(surfaceHomologyCoordinates j p n).finrank_eq]
  simp

theorem surface_Betti_numbers (j : Kind) (p : FixedPeriod j) :
    (fun n : Fin 5 => Module.finrank ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [surface_homology_finrank]
  exact ellipticBettiNumber_firstFive

theorem surface_eulerCharacteristic_zero (j : Kind) (p : FixedPeriod j) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n * (Module.finrank ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [surface_homology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem surface_eulerCharacteristic_zero_of_ge (j : Kind) (p : FixedPeriod j)
    {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.finrank ℤ
      (SingularHomology (Surface j p j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [surface_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

variable {j : Kind} (D : Equivariant.Data j)

/-- Uniform coordinates on the actual entire filling, induced by its
proved deformation retraction onto the central surface. -/
def fillingHomologyCoordinates (n : ℕ) :
    SingularHomology (D.Space j.twist (mainTwist_admissible j)) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n).symm.trans
    (surfaceHomologyCoordinates j D.centralPeriod n)

/-- The actual central inclusion preserves the uniform coordinates in every degree. -/
theorem fillingHomologyCoordinates_centralInclusion (n : ℕ)
    (a : SingularHomology (Surface j D.centralPeriod j.twist (mainTwist_admissible j)) n) :
    fillingHomologyCoordinates D n
      (singularHomologyMap (D.surfaceIntoFilling j.twist (mainTwist_admissible j)) n a) =
      surfaceHomologyCoordinates j D.centralPeriod n a := by
  change surfaceHomologyCoordinates j D.centralPeriod n
    ((centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n).symm
      (centralSurfaceHomologyEquiv D j.twist (mainTwist_admissible j) n a)) = _
  rw [LinearEquiv.symm_apply_apply]

theorem filling_homology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  Module.Free.of_equiv (fillingHomologyCoordinates D n).symm

theorem filling_homology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) :=
  Module.Finite.of_surjective (fillingHomologyCoordinates D n).symm.toLinearMap
    (fillingHomologyCoordinates D n).symm.surjective

theorem filling_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) := by
  let := filling_homology_free D n
  infer_instance

theorem filling_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) =
      ellipticBettiNumber n := by
  rw [(fillingHomologyCoordinates D n).finrank_eq]
  simp

theorem filling_Betti_numbers :
    (fun n : Fin 5 => Module.finrank ℤ
      (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [filling_homology_finrank]
  exact ellipticBettiNumber_firstFive

theorem filling_eulerCharacteristic_zero :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n * (Module.finrank ℤ
      (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [filling_homology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem filling_eulerCharacteristic_zero_of_ge {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (Module.finrank ℤ
      (SingularHomology (D.Space j.twist (mainTwist_admissible j)) n) : ℤ)) = 0 := by
  simp_rw [filling_homology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

end Wikipedia.HopfProblem.Elliptic.HigherHomology
