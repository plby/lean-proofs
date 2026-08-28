import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessCuspHomology
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessElliptic
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessRegular
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessMappingTorusEuler
import Wikipedia.HopfProblem.ThreefoldHomologyFinitenessProducts
import Wikipedia.HopfProblem.ThreefoldOverlapMappingTorusHomology
import Wikipedia.HopfProblem.ThreefoldHomologyStarMaps

/-!
# Actual finite homology of all pieces and overlaps in the global star cover

The cusp uses the proved whole-cap central equivalence, the elliptic
pieces use their genuine small-radius central deformations, and the
overlaps use their original affine mapping tori.  These are the literal
objects in the global star sequence, not abstract groups assigned to
them.  No boundary-matrix calculations enter these finiteness bounds.
-/

noncomputable section

open scoped BigOperators TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris CuspCentralHomology
open ThreefoldHomologyFinitenessCusp

/-- The actual original cusp piece at its fixed gluing radius. -/
def cuspPieceHomologyEquiv (n : ℕ) :
    SingularHomology (localPiece (some none)) n ≃ₗ[ℤ] (Fin (centralBetti n) → ℤ) :=
  fullHomologyCoordinates ThreefoldOverlapMappingTorus.Cusp.specialData n

theorem cuspPieceHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology (localPiece (some none)) n) :=
  Module.Free.of_equiv (cuspPieceHomologyEquiv n).symm

theorem cuspPieceHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology (localPiece (some none)) n) :=
  Module.Finite.of_surjective (cuspPieceHomologyEquiv n).symm.toLinearMap
    (cuspPieceHomologyEquiv n).symm.surjective

theorem cuspPieceHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology (localPiece (some none)) n) = centralBetti n := by
  rw [(cuspPieceHomologyEquiv n).finrank_eq]
  exact Module.finrank_fin_fun ℤ

theorem cuspPieceHomology_subsingleton {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (localPiece (some none)) n) :=
  fullHomology_subsingleton_of_four_lt ThreefoldOverlapMappingTorus.Cusp.specialData hn

theorem cuspPieceRationalHomology_finrank (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some none)) n) =
      centralBetti n :=
  rational_finrank_of_equiv (cuspPieceHomologyEquiv n)

/-- The Euler characteristic is that of the actual central cusp fibre,
even though the radius used for gluing was fixed beforehand. -/
theorem cuspPieceRationalHomology_euler_of_le {N : ℕ} (hN : 5 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (localPiece (some none)) n) : ℤ)) = 2 := by
  simp only [cuspPieceRationalHomology_finrank]
  have hz (n : ℕ) (hn : 5 ≤ n) : centralBetti n = 0 := by
    rw [← Nat.sub_add_cancel hn]
    rfl
  calc
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n * (centralBetti n : ℤ)) =
        ∑ n ∈ Finset.range 5, (-1 : ℤ) ^ n * (centralBetti n : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro n _ hn
      have hn' : 5 ≤ n := Nat.le_of_not_gt (by simpa only [Finset.mem_range] using hn)
      rw [hz n hn', Nat.cast_zero, mul_zero]
    _ = 2 := by norm_num [Finset.sum_range_succ, centralBetti]

/-- Every one of the three actual filling homology groups is finite. -/
theorem fillingHomology_finite (i : Puncture) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (localPiece (some i)) n) := by
  cases i with
  | none => exact cuspPieceHomology_finite n
  | some j => exact ellipticPieceHomology_finite j n

theorem fillingHomology_subsingleton (i : Puncture) {n : ℕ} (hn : 4 < n) :
    Subsingleton (SingularHomology (localPiece (some i)) n) := by
  cases i with
  | none => exact cuspPieceHomology_subsingleton hn
  | some j => exact ellipticPieceHomology_subsingleton j hn

/-- Finiteness is transported through the genuine full-overlap mapping-torus models. -/
theorem overlapHomology_finite (i : Puncture) (n : ℕ) :
    Module.Finite ℤ (SingularHomology (RegularOverlap i) n) := by
  have := ThreefoldHomologyFinitenessMappingTorus.homology_finite
    (ThreefoldOverlapMappingTorus.monodromy i) n
  exact Module.Finite.of_surjective
    (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm.toLinearMap
    (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).symm.surjective

theorem overlapHomology_subsingleton (i : Puncture) {n : ℕ} (hn : 5 < n) :
    Subsingleton (SingularHomology (RegularOverlap i) n) := by
  have := ThreefoldHomologyFinitenessMappingTorus.homology_subsingleton_of_lt
    (ThreefoldOverlapMappingTorus.monodromy i) hn
  refine ⟨fun a b => (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n).injective ?_⟩
  exact Subsingleton.elim _ _

theorem overlapRationalHomology_finrank (i : Puncture) (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (RegularOverlap i) n) =
      ThreefoldHomologyFinitenessMappingTorus.rationalBetti
        (ThreefoldOverlapMappingTorus.monodromy i) n :=
  (LinearEquiv.baseChange ℤ ℚ _ _
    (ThreefoldOverlapMappingTorus.overlapHomologyEquiv i n)).finrank_eq

/-- Every actual overlap has zero Euler characteristic, retaining its own monodromy. -/
theorem overlapRationalHomology_euler_of_le (i : Puncture) {N : ℕ} (hN : 6 ≤ N) :
    (∑ n ∈ Finset.range N, (-1 : ℤ) ^ n *
      (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology (RegularOverlap i) n) : ℤ)) = 0 := by
  simp only [overlapRationalHomology_finrank]
  exact ThreefoldHomologyFinitenessMappingTorus.euler_sum_eq_zero
    (ThreefoldOverlapMappingTorus.monodromy i) N hN

theorem starFillingHomology_finite (n : ℕ) : Module.Finite ℤ (StarFillingHomology n) := by
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (localPiece (some i)) n) :=
    fun i => fillingHomology_finite i n
  exact finite_pi_int (fun i : Puncture => SingularHomology (localPiece (some i)) n)

theorem starOverlapHomology_finite (n : ℕ) : Module.Finite ℤ (StarOverlapHomology n) := by
  have : ∀ i : Puncture, Module.Finite ℤ (SingularHomology (RegularOverlap i) n) :=
    fun i => overlapHomology_finite i n
  exact finite_pi_int (fun i : Puncture => SingularHomology (RegularOverlap i) n)

theorem starPairHomology_finite (n : ℕ) : Module.Finite ℤ (StarPairHomology n) := by
  have := regularHomology_finite n
  have := starFillingHomology_finite n
  exact finite_prod_int (SingularHomology SpecialRegularFamily n) (StarFillingHomology n)

theorem starFillingHomology_subsingleton {n : ℕ} (hn : 4 < n) :
    Subsingleton (StarFillingHomology n) := by
  have : ∀ i : Puncture, Subsingleton (SingularHomology (localPiece (some i)) n) :=
    fun i => fillingHomology_subsingleton i hn
  infer_instance

theorem starOverlapHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (StarOverlapHomology n) := by
  have : ∀ i : Puncture, Subsingleton (SingularHomology (RegularOverlap i) n) :=
    fun i => overlapHomology_subsingleton i hn
  infer_instance

theorem starPairHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (StarPairHomology n) := by
  have := regularHomology_subsingleton hn
  have := starFillingHomology_subsingleton (by omega : 4 < n)
  infer_instance

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
