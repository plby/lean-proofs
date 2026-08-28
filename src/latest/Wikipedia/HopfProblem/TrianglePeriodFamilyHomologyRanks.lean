import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyGroups
import Wikipedia.HopfProblem.TrianglePeriodFamilyHomologyBounds

/-!
# The all-degree integral homology table of the actual regular family

The constructed equivalences, including actual degree-zero augmentation
and high-degree vanishing, give a single all-degree integral marking. In
particular freeness, finite generation, torsion-freeness and the ranks are
proved for the actual singular-homology objects, not assigned to a model.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.Homology

open SpecialPeriods SingularMayerVietoris

/-- The ranks proved by the actual regular-family Mayer--Vietoris calculation. -/
def familyBetti : ℕ → ℕ
  | 0 => 1
  | 1 => 3
  | 2 => 6
  | 3 => 8
  | 4 => 6
  | 5 => 2
  | _ + 6 => 0

variable (D : Data ℂ TriangleRegularPoint)

/-- An integral coordinate equivalence for every actual singular-homology group. -/
def familyHomologyEquiv : (n : ℕ) →
    SingularHomology D.Space n ≃ₗ[ℤ] (Fin (familyBetti n) → ℤ)
  | 0 => (familyH0Equiv D).trans (LinearEquiv.funUnique (Fin 1) ℤ ℤ).symm
  | 1 => familyH1Equiv D
  | 2 => familyH2Equiv D
  | 3 => familyH3Equiv D
  | 4 => familyH4Equiv D
  | 5 => familyH5Equiv D
  | n + 6 => by
      change SingularHomology D.Space (n + 6) ≃ₗ[ℤ] (Fin 0 → ℤ)
      letI := family_homology_subsingleton_of_lt D (n := n + 6) (by omega)
      exact LinearEquiv.ofSubsingleton _ _

@[simp] theorem familyHomologyEquiv_zero (a : SingularHomology D.Space 0) (i : Fin 1) :
    familyHomologyEquiv D 0 a i = familyH0Equiv D a := rfl

@[simp] theorem familyHomologyEquiv_one : familyHomologyEquiv D 1 = familyH1Equiv D := rfl
@[simp] theorem familyHomologyEquiv_two : familyHomologyEquiv D 2 = familyH2Equiv D := rfl
@[simp] theorem familyHomologyEquiv_three : familyHomologyEquiv D 3 = familyH3Equiv D := rfl
@[simp] theorem familyHomologyEquiv_four : familyHomologyEquiv D 4 = familyH4Equiv D := rfl
@[simp] theorem familyHomologyEquiv_five : familyHomologyEquiv D 5 = familyH5Equiv D := rfl

/-- Every actual regular-family integral singular-homology group is free. -/
theorem family_homology_free (n : ℕ) : Module.Free ℤ (SingularHomology D.Space n) :=
  Module.Free.of_equiv (familyHomologyEquiv D n).symm

/-- Every actual regular-family integral singular-homology group is finitely generated. -/
theorem family_homology_finite (n : ℕ) : Module.Finite ℤ (SingularHomology D.Space n) :=
  Module.Finite.of_surjective (familyHomologyEquiv D n).symm.toLinearMap
    (familyHomologyEquiv D n).symm.surjective

/-- The actual integral homology has the stated rank in every degree. -/
theorem family_homology_finrank (n : ℕ) :
    Module.finrank ℤ (SingularHomology D.Space n) = familyBetti n := by
  rw [(familyHomologyEquiv D n).finrank_eq]
  simp

/-- No actual regular-family integral homology group has integer torsion. -/
theorem family_homology_torsionFree (n : ℕ) :
    Module.IsTorsionFree ℤ (SingularHomology D.Space n) := by
  let := family_homology_free D n
  infer_instance

/-- The ranks of the actual homology in degrees zero through five. -/
theorem family_homology_rank_table :
    (fun n : Fin 6 => Module.finrank ℤ (SingularHomology D.Space n.val)) =
      ![1, 3, 6, 8, 6, 2] := by
  funext n
  rw [family_homology_finrank]
  fin_cases n <;> rfl

/-- The alternating sum of the actual finite homology ranks is zero. -/
theorem family_homology_euler :
    ∑ n ∈ Finset.range 6,
      (-1 : ℤ) ^ n * (Module.finrank ℤ (SingularHomology D.Space n) : ℤ) = 0 := by
  simp only [family_homology_finrank]
  norm_num [Finset.sum_range_succ, familyBetti]

end Wikipedia.HopfProblem.TrianglePeriodFamily.Homology
