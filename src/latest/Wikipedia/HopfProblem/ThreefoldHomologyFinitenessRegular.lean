import Wikipedia.HopfProblem.TrianglePeriodFamilyHomology
import Wikipedia.HopfProblem.SpecialPeriodsThreefoldChosenBase
import Mathlib.LinearAlgebra.Dimension.Constructions
import Mathlib.RingTheory.TensorProduct.Finite

/-!
# Homology finiteness of the actual regular threefold piece

The regular piece of the chosen threefold is definitionally the constructed
special period family in the proved regular-family homology calculation.
Its periods and both generator equations are the actual unconditional ones.
We retain that calculation's integral coordinate equivalence and derive
finiteness, high-degree vanishing and Euler characteristic zero. The rational
statements concern the literal rationalization of these actual integral
singular-homology modules, not an assigned model of their ranks.
-/

noncomputable section

open CategoryTheory Limits
open scoped TensorProduct

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness

open SingularMayerVietoris
open TrianglePeriodFamily.Homology

/-- The previously proved marking of the actual regular piece, with all
period data and covariance equations already supplied by the construction. -/
def regularHomologyEquiv (n : ℕ) :
    SingularHomology SpecialRegularFamily n ≃ₗ[ℤ] (Fin (familyBetti n) → ℤ) :=
  TrianglePeriodFamily.Canonical.specialRegularHomologyEquiv n

theorem regularHomology_free (n : ℕ) :
    Module.Free ℤ (SingularHomology SpecialRegularFamily n) :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_free n

theorem regularHomology_finite (n : ℕ) :
    Module.Finite ℤ (SingularHomology SpecialRegularFamily n) :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_finite n

theorem regularHomology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology SpecialRegularFamily n) :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_torsionFree n

/-- The actual integral ranks in every degree. -/
theorem regularHomology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology SpecialRegularFamily n) = familyBetti n :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_finrank n

theorem regularHomology_rank_table :
    (fun n : Fin 6 => Module.finrank ℤ (SingularHomology SpecialRegularFamily n.val)) =
      ![1, 3, 6, 8, 6, 2] :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_rank_table

/-- There is no actual regular-piece homology above degree five. -/
theorem regularHomology_isZero {n : ℕ} (hn : 5 < n) :
    IsZero (SingularHomology SpecialRegularFamily n) :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_isZero_of_lt hn

theorem regularHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (SingularHomology SpecialRegularFamily n) :=
  ModuleCat.isZero_iff_subsingleton.mp (regularHomology_isZero hn)

theorem regularHomology_finrank_eq_zero {n : ℕ} (hn : 5 < n) :
    Module.finrank ℤ (SingularHomology SpecialRegularFamily n) = 0 := by
  have := regularHomology_subsingleton hn
  exact Module.finrank_zero_of_subsingleton

theorem regularHomology_euler :
    ∑ n ∈ Finset.range 6,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology SpecialRegularFamily n) : ℤ) = 0 :=
  TrianglePeriodFamily.Canonical.specialRegularHomology_euler

/-- The same actual Euler characteristic at any larger finite cutoff. -/
theorem regularHomology_euler_of_le {N : ℕ} (hN : 6 ≤ N) :
    ∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology SpecialRegularFamily n) : ℤ) = 0 := by
  calc
    _ = ∑ n ∈ Finset.range 6,
        (-1 : ℤ) ^ n *
          (Module.finrank ℤ (SingularHomology SpecialRegularFamily n) : ℤ) := by
      symm
      apply Finset.sum_subset (Finset.range_mono hN)
      intro n _ hn
      simp only [Finset.mem_range, not_lt] at hn
      have h : 5 < n := by omega
      rw [regularHomology_finrank_eq_zero h]
      simp
    _ = 0 := regularHomology_euler

/-- Rationalization of the actual integral regular homology is finite-dimensional. -/
theorem regularRationalHomology_finite (n : ℕ) :
    Module.Finite ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) := by
  have := regularHomology_finite n
  infer_instance

/-- Rationalization has the same rank because integral freeness was proved. -/
theorem regularRationalHomology_finrank (n : ℕ) :
    Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) = familyBetti n := by
  have := regularHomology_free n
  rw [Module.finrank_baseChange, regularHomology_finrank]

theorem regularRationalHomology_rank_table :
    (fun n : Fin 6 =>
      Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n.val)) =
      ![1, 3, 6, 8, 6, 2] := by
  funext n
  rw [regularRationalHomology_finrank]
  fin_cases n <;> rfl

theorem regularRationalHomology_subsingleton {n : ℕ} (hn : 5 < n) :
    Subsingleton (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) := by
  have := regularHomology_subsingleton hn
  infer_instance

theorem regularRationalHomology_isZero {n : ℕ} (hn : 5 < n) :
    IsZero (ModuleCat.of ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n)) := by
  have := regularRationalHomology_subsingleton hn
  exact ModuleCat.isZero_of_subsingleton _

/-- The rational Euler characteristic of the actual regular piece is zero. -/
theorem regularRationalHomology_euler :
    ∑ n ∈ Finset.range 6,
      (-1 : ℤ) ^ n *
        (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) : ℤ) = 0 := by
  simpa only [regularHomology_finrank, regularRationalHomology_finrank]
    using regularHomology_euler

theorem regularRationalHomology_euler_of_le {N : ℕ} (hN : 6 ≤ N) :
    ∑ n ∈ Finset.range N,
      (-1 : ℤ) ^ n *
        (Module.finrank ℚ (ℚ ⊗[ℤ] SingularHomology SpecialRegularFamily n) : ℤ) = 0 := by
  simpa only [regularHomology_finrank, regularRationalHomology_finrank]
    using regularHomology_euler_of_le hN

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Homology.Finiteness
