import Wikipedia.HopfProblem.CuspCentralHomology
import Wikipedia.HopfProblem.EllipticHigherHomologyCohomologyCoordinates
import Wikipedia.HopfProblem.SingularCohomologyFreeHomotopy

/-!
# Native integral singular cohomology of the central cusp fibre

The actual singular cochain complex, not a homology dual by definition,
is used throughout.  Its proved evaluation theorem applies because the
actual central-fibre homology and coordinate-torus homology are free in
every degree.  In particular the native central cohomology has the same
finite free rank table as the previously computed homology.
-/

noncomputable section

open scoped ContDiff ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralCohomology

open CuspRetraction CuspCentralHomology
open SingularMayerVietoris SingularCohomologyFree PeriodTorusHigherHomology

/-- Evaluation for the actual four-torus cochain complex, with its
projectivity hypotheses supplied by its actual integral homology. -/
def coordinateTorusEvaluationEquiv (n : ℕ) :
    SingularCohomology (ProductTorus 4) n ≃ₗ[ℤ]
      Module.Dual ℤ (SingularHomology (ProductTorus 4) n) := by
  letI (k : ℕ) : Module.Projective ℤ (SingularHomology (ProductTorus 4) k) := by
    let := productTorus_homology_free 4 k
    infer_instance
  exact singularEvaluationEquiv (ProductTorus 4) n

@[simp] theorem coordinateTorusEvaluationEquiv_apply (n : ℕ)
    (a : SingularCohomology (ProductTorus 4) n) :
    coordinateTorusEvaluationEquiv n a = singularEvaluation (ProductTorus 4) n a := rfl

variable (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (r : ℝ) (hr : 0 < r)
    (hC : ∀ i j, ContDiffOn ℂ ω (fun z => C z i j) (Metric.ball 0 r))

/-- Native cohomology evaluation for the literal central fibre at the
original ambient radius.  No additional small-drift condition is assumed. -/
def centralEvaluationEquiv (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n ≃ₗ[ℤ]
      Module.Dual ℤ (SingularHomology (QuotientCentralFibre C r) n) := by
  letI (k : ℕ) : Module.Projective ℤ
      (SingularHomology (QuotientCentralFibre C r) k) := by
    let := centralSingularHomology_free C r hr hC k
    infer_instance
  exact singularEvaluationEquiv (QuotientCentralFibre C r) n

@[simp] theorem centralEvaluationEquiv_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) :
    centralEvaluationEquiv C r hr hC n a =
      singularEvaluation (QuotientCentralFibre C r) n a := rfl

/-- Integral coordinates for the actual singular cohomology groups. -/
def centralCohomologyCoordinates (n : ℕ) :
    SingularCohomology (QuotientCentralFibre C r) n ≃ₗ[ℤ]
      (Fin (centralBetti n) → ℤ) :=
  Elliptic.HigherHomology.cohomologyCoordinatesOfHomology
    (QuotientCentralFibre C r) centralBetti (centralSingularHomologyEquiv C r hr hC) n

/-- These coordinates are the actual evaluations on the homology basis. -/
theorem centralCohomologyCoordinates_apply (n : ℕ)
    (a : SingularCohomology (QuotientCentralFibre C r) n) (i : Fin (centralBetti n)) :
    centralCohomologyCoordinates C r hr hC n a i =
      singularEvaluation (QuotientCentralFibre C r) n a
        ((centralSingularHomologyEquiv C r hr hC n).symm (Pi.single i 1)) :=
  Elliptic.HigherHomology.cohomologyCoordinatesOfHomology_apply_coordinate
    (QuotientCentralFibre C r) centralBetti (centralSingularHomologyEquiv C r hr hC) n a i

include hr hC

theorem centralCohomology_free (n : ℕ) :
    Module.Free ℤ (SingularCohomology (QuotientCentralFibre C r) n) :=
  Module.Free.of_equiv (centralCohomologyCoordinates C r hr hC n).symm

theorem centralCohomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularCohomology (QuotientCentralFibre C r) n) :=
  Module.Finite.of_surjective (centralCohomologyCoordinates C r hr hC n).symm.toLinearMap
    (centralCohomologyCoordinates C r hr hC n).symm.surjective

theorem centralCohomology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularCohomology (QuotientCentralFibre C r) n) := by
  let := centralCohomology_free C r hr hC n
  infer_instance

theorem centralCohomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularCohomology (QuotientCentralFibre C r) n) = centralBetti n := by
  rw [(centralCohomologyCoordinates C r hr hC n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem centralCohomology_finranks :
    (fun i : Fin 5 => Module.finrank ℤ (SingularCohomology (QuotientCentralFibre C r) i)) =
      ![1, 2, 4, 2, 1] := by
  funext i
  rw [centralCohomology_finrank C r hr hC]
  fin_cases i <;> rfl

theorem centralCohomology_subsingleton_of_four_lt (n : ℕ) (hn : 4 < n) :
    Subsingleton (SingularCohomology (QuotientCentralFibre C r) n) := by
  apply Elliptic.HigherHomology.cohomology_subsingleton_of_homology_coordinates
    (QuotientCentralFibre C r) centralBetti (centralSingularHomologyEquiv C r hr hC) n
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (by omega : 5 ≤ n)
  rw [Nat.add_comm]
  rfl

end Wikipedia.HopfProblem.CuspCentralCohomology
