import Wikipedia.HopfProblem.EllipticHigherHomologySpecialProperties
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldEllipticRetraction
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Actual homology of the two small elliptic pieces

The radial homotopy equivalence is the proved retraction of the original
small filling piece used in the threefold gluing. Composing its actual
homology map with the central-surface coordinates gives free integral
homology of ranks `(1, 2, 2, 2, 1)`, vanishing above degree four. The
coordinates retain the genuine central inclusion and retraction.

The rational dimensions and zero Euler sum follow from these proved
integral coordinates, with no hypotheses about a substitute model.
-/

noncomputable section

open CategoryTheory Limits
open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris PeriodTorusHigherHomology
open EllipticFilling Elliptic.HigherHomology

/-- Rational dimension from a proved finite free integral coordinate equivalence. -/
theorem rational_finrank_of_equiv {M : Type*} [AddCommGroup M] [Module ℤ M]
    {r : ℕ} (e : M ≃ₗ[ℤ] (Fin r → ℤ)) :
    Module.finrank ℚ (ℚ ⊗[ℤ] M) = r := by
  have : Module.Free ℤ M := Module.Free.of_equiv e.symm
  rw [Module.finrank_baseChange, e.finrank_eq]
  simp

/-- The actual retraction identifies the native small piece's homology with
the actual special central surface's homology, in every degree. -/
def ellipticPieceRetractionHomologyEquiv (j : Elliptic.Kind) (n : ℕ) :
    SingularHomology (localPiece (some (some j))) n ≃ₗ[ℤ]
      SingularHomology (SpecialCentralSurface j) n :=
  (homotopyEquivHomologyEquiv (EllipticGeometry.pieceSurfaceHomotopyEquiv j) n).symm

@[simp] theorem ellipticPieceRetractionHomologyEquiv_toLinearMap
    (j : Elliptic.Kind) (n : ℕ) :
    (ellipticPieceRetractionHomologyEquiv j n).toLinearMap =
      singularHomologyMap (EllipticGeometry.pieceSurfaceRetraction j) n := rfl

@[simp] theorem ellipticPieceRetractionHomologyEquiv_apply
    (j : Elliptic.Kind) (n : ℕ) (a : SingularHomology (localPiece (some (some j))) n) :
    ellipticPieceRetractionHomologyEquiv j n a =
      singularHomologyMap (EllipticGeometry.pieceSurfaceRetraction j) n a := rfl

@[simp] theorem ellipticPieceRetractionHomologyEquiv_symm_apply
    (j : Elliptic.Kind) (n : ℕ) (a : SingularHomology (SpecialCentralSurface j) n) :
    (ellipticPieceRetractionHomologyEquiv j n).symm a =
      singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n a := rfl

/-- All-degree coordinates on the actual local piece used in the global gluing. -/
def ellipticPieceHomologyEquiv (j : Elliptic.Kind) (n : ℕ) :
    SingularHomology (localPiece (some (some j))) n ≃ₗ[ℤ]
      (Fin (ellipticBettiNumber n) → ℤ) :=
  (ellipticPieceRetractionHomologyEquiv j n).trans
    (specialCentralSurfaceHomologyCoordinates j n)

@[simp] theorem ellipticPieceHomologyEquiv_apply
    (j : Elliptic.Kind) (n : ℕ) (a : SingularHomology (localPiece (some (some j))) n) :
    ellipticPieceHomologyEquiv j n a =
      specialCentralSurfaceHomologyCoordinates j n
        (singularHomologyMap (EllipticGeometry.pieceSurfaceRetraction j) n a) := rfl

@[simp] theorem ellipticPieceHomologyEquiv_symm_apply
    (j : Elliptic.Kind) (n : ℕ) (a : Fin (ellipticBettiNumber n) → ℤ) :
    (ellipticPieceHomologyEquiv j n).symm a =
      singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n
        ((specialCentralSurfaceHomologyCoordinates j n).symm a) := rfl

/-- The genuine central inclusion preserves the displayed homology coordinates. -/
theorem ellipticPieceHomologyEquiv_centralInclusion
    (j : Elliptic.Kind) (n : ℕ) (a : SingularHomology (SpecialCentralSurface j) n) :
    ellipticPieceHomologyEquiv j n
      (singularHomologyMap (EllipticGeometry.centralSurfaceIntoPiece j) n a) =
      specialCentralSurfaceHomologyCoordinates j n a := by
  change specialCentralSurfaceHomologyCoordinates j n
    (ellipticPieceRetractionHomologyEquiv j n
      ((ellipticPieceRetractionHomologyEquiv j n).symm a)) = _
  rw [LinearEquiv.apply_symm_apply]

theorem ellipticPieceHomology_free (j : Elliptic.Kind) (n : ℕ) :
    Module.Free ℤ (SingularHomology (localPiece (some (some j))) n) :=
  Module.Free.of_equiv (ellipticPieceHomologyEquiv j n).symm

theorem ellipticPieceHomology_finite (j : Elliptic.Kind) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (localPiece (some (some j))) n) :=
  Module.Finite.of_surjective (ellipticPieceHomologyEquiv j n).symm.toLinearMap
    (ellipticPieceHomologyEquiv j n).symm.surjective

theorem ellipticPieceHomology_torsionFree (j : Elliptic.Kind) (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology (localPiece (some (some j))) n) := by
  have := ellipticPieceHomology_free j n
  infer_instance

theorem ellipticPieceHomology_finrank (j : Elliptic.Kind) (n : ℕ) :
    Module.finrank ℤ (SingularHomology (localPiece (some (some j))) n) =
      ellipticBettiNumber n := by
  rw [(ellipticPieceHomologyEquiv j n).finrank_eq]
  simp

theorem ellipticPieceHomology_rank_table (j : Elliptic.Kind) :
    (fun n : Fin 5 =>
      Module.finrank ℤ (SingularHomology (localPiece (some (some j))) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [ellipticPieceHomology_finrank]
  exact ellipticBettiNumber_firstFive

/-- The actual small piece has no singular homology above degree four. -/
theorem ellipticPieceHomology_subsingleton (j : Elliptic.Kind) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (localPiece (some (some j))) n) := by
  have : Subsingleton (Fin (ellipticBettiNumber n) → ℤ) := by
    rw [ellipticBettiNumber_eq_zero_of_lt hn]
    infer_instance
  exact (ellipticPieceHomologyEquiv j n).injective.subsingleton

theorem ellipticPieceHomology_eq_zero (j : Elliptic.Kind) {n : ℕ} (hn : 4 < n)
    (a : SingularHomology (localPiece (some (some j))) n) : a = 0 := by
  have := ellipticPieceHomology_subsingleton j hn
  exact Subsingleton.elim a 0

theorem ellipticPieceHomology_isZero (j : Elliptic.Kind) {n : ℕ} (hn : 4 < n) :
    IsZero (SingularHomology (localPiece (some (some j))) n) :=
  ModuleCat.isZero_iff_subsingleton.mpr (ellipticPieceHomology_subsingleton j hn)

theorem ellipticPieceHomology_euler (j : Elliptic.Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (localPiece (some (some j))) n) : ℤ)) = 0 := by
  simp only [ellipticPieceHomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem ellipticPieceHomology_euler_of_le (j : Elliptic.Kind) {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℤ (SingularHomology (localPiece (some (some j))) n) : ℤ)) = 0 := by
  simp only [ellipticPieceHomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

theorem ellipticPieceRationalHomology_finite (j : Elliptic.Kind) (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some (some j))) n) := by
  have := ellipticPieceHomology_finite j n
  infer_instance

/-- Rational ranks are derived from the proved coordinates on the actual piece. -/
theorem ellipticPieceRationalHomology_finrank (j : Elliptic.Kind) (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some (some j))) n) =
      ellipticBettiNumber n :=
  rational_finrank_of_equiv (ellipticPieceHomologyEquiv j n)

theorem ellipticPieceRationalHomology_rank_table (j : Elliptic.Kind) :
    (fun n : Fin 5 =>
      Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some (some j))) n)) =
      ![1, 2, 2, 2, 1] := by
  simp_rw [ellipticPieceRationalHomology_finrank]
  exact ellipticBettiNumber_firstFive

theorem ellipticPieceRationalHomology_euler (j : Elliptic.Kind) :
    (∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some (some j))) n) : ℤ)) = 0 := by
  simp only [ellipticPieceRationalHomology_finrank]
  exact ellipticBettiNumber_euler_sum

theorem ellipticPieceRationalHomology_euler_of_le (j : Elliptic.Kind) {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some (some j))) n) : ℤ)) = 0 := by
  simp only [ellipticPieceRationalHomology_finrank]
  exact ellipticBettiNumber_euler_sum_of_ge hN

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
