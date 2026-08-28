import Wikipedia.HopfProblem.CuspNormalizationSheafGermComplexAxes

/-!
# Coordinate tables for actual analytic branch and axis germs

These identities compute the genuine pullbacks along coordinate-plane and
coordinate-axis inclusions.  Every computation is verified on an actual
analytic representative of the germ.
-/

noncomputable section

open Set Filter Topology

namespace Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex

open Germs ToricCharts ToricComponent

local notation "E₂" => CoordinateSpace 2
local notation "E₃" => CoordinateSpace 3

private theorem toBranch_extendBranch_of_coordinate
    (j k : Fin 3) (i l : Fin 2)
    (h : ∀ z : E₂, removeCoordinate k (insertZero j z) = Pi.single i (z l))
    (φ : BranchGerm) :
    toBranch j (extendBranch k φ) = axisExtension l (axisRestriction i φ) := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [extendBranch_ofAnalytic, toBranch_ofAnalytic,
    axisRestriction_ofAnalytic, axisExtension_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => congrArg f (h z)

theorem toBranch_extendBranch_01 (φ : BranchGerm) :
    toBranch 0 (extendBranch 1 φ) = axisExtension 1 (axisRestriction 1 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

theorem toBranch_extendBranch_02 (φ : BranchGerm) :
    toBranch 0 (extendBranch 2 φ) = axisExtension 0 (axisRestriction 1 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

theorem toBranch_extendBranch_10 (φ : BranchGerm) :
    toBranch 1 (extendBranch 0 φ) = axisExtension 1 (axisRestriction 1 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

theorem toBranch_extendBranch_12 (φ : BranchGerm) :
    toBranch 1 (extendBranch 2 φ) = axisExtension 0 (axisRestriction 0 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

theorem toBranch_extendBranch_20 (φ : BranchGerm) :
    toBranch 2 (extendBranch 0 φ) = axisExtension 1 (axisRestriction 0 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

theorem toBranch_extendBranch_21 (φ : BranchGerm) :
    toBranch 2 (extendBranch 1 φ) = axisExtension 0 (axisRestriction 0 φ) := by
  apply toBranch_extendBranch_of_coordinate
  intro z
  ext i
  fin_cases i <;>
    simp [removeCoordinate, insertZero, Fin.removeNth, Fin.insertNth,
      Fin.succAboveCases, Fin.succAbove]

private theorem toBranch_ambientAxisExtension_of_coordinate
    (j k : Fin 3) (i : Fin 2) (h : ∀ z : E₂, insertZero j z k = z i)
    (φ : AxisGerm) :
    toBranch j (ambientAxisExtension k φ) = axisExtension i φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [ambientAxisExtension_ofAnalytic, toBranch_ofAnalytic, axisExtension_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => congrArg f (h z)

theorem toBranch_ambientAxisExtension_self (j : Fin 3) (φ : AxisGerm) :
    toBranch j (ambientAxisExtension j φ) = constant (0 : E₂) (eval (0 : ℂ) φ) := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  change toBranch j (ambientAxisExtension j (ofAnalytic f hf)) =
    ofAnalytic (fun _ : E₂ => f 0) analyticAt_const
  rw [ambientAxisExtension_ofAnalytic, toBranch_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun z => congrArg f (insertZero_at j z)

theorem toBranch_ambientAxisExtension_00 (φ : AxisGerm) :
    toBranch 0 (ambientAxisExtension 0 φ) = constant (0 : E₂) (eval (0 : ℂ) φ) :=
  toBranch_ambientAxisExtension_self 0 φ

theorem toBranch_ambientAxisExtension_01 (φ : AxisGerm) :
    toBranch 0 (ambientAxisExtension 1 φ) = axisExtension 0 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 0 0 z 0

theorem toBranch_ambientAxisExtension_02 (φ : AxisGerm) :
    toBranch 0 (ambientAxisExtension 2 φ) = axisExtension 1 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 0 0 z 1

theorem toBranch_ambientAxisExtension_10 (φ : AxisGerm) :
    toBranch 1 (ambientAxisExtension 0 φ) = axisExtension 0 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 1 0 z 0

theorem toBranch_ambientAxisExtension_11 (φ : AxisGerm) :
    toBranch 1 (ambientAxisExtension 1 φ) = constant (0 : E₂) (eval (0 : ℂ) φ) :=
  toBranch_ambientAxisExtension_self 1 φ

theorem toBranch_ambientAxisExtension_12 (φ : AxisGerm) :
    toBranch 1 (ambientAxisExtension 2 φ) = axisExtension 1 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 1 0 z 1

theorem toBranch_ambientAxisExtension_20 (φ : AxisGerm) :
    toBranch 2 (ambientAxisExtension 0 φ) = axisExtension 0 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 2 0 z 0

theorem toBranch_ambientAxisExtension_21 (φ : AxisGerm) :
    toBranch 2 (ambientAxisExtension 1 φ) = axisExtension 1 φ := by
  apply toBranch_ambientAxisExtension_of_coordinate
  intro z
  exact Fin.insertNth_apply_succAbove (α := fun _ : Fin 3 => ℂ) 2 0 z 1

theorem toBranch_ambientAxisExtension_22 (φ : AxisGerm) :
    toBranch 2 (ambientAxisExtension 2 φ) = constant (0 : E₂) (eval (0 : ℂ) φ) :=
  toBranch_ambientAxisExtension_self 2 φ

private theorem axisRestriction_toBranch_of_coordinate
    (i : Fin 2) (j k : Fin 3)
    (h : ∀ t : ℂ, insertZero j (Pi.single i t) = Pi.single k t)
    (φ : AmbientGerm) :
    axisRestriction i (toBranch j φ) = ambientAxisRestriction k φ := by
  obtain ⟨f, hf, rfl⟩ := exists_representative φ
  rw [toBranch_ofAnalytic, axisRestriction_ofAnalytic, ambientAxisRestriction_ofAnalytic]
  apply (ofAnalytic_eq_iff _ _ _ _).mpr
  exact Eventually.of_forall fun t => congrArg f (h t)

theorem axisRestriction_toBranch_00 (φ : AmbientGerm) :
    axisRestriction 0 (toBranch 0 φ) = ambientAxisRestriction 1 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

theorem axisRestriction_toBranch_01 (φ : AmbientGerm) :
    axisRestriction 0 (toBranch 1 φ) = ambientAxisRestriction 0 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

theorem axisRestriction_toBranch_02 (φ : AmbientGerm) :
    axisRestriction 0 (toBranch 2 φ) = ambientAxisRestriction 0 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

theorem axisRestriction_toBranch_10 (φ : AmbientGerm) :
    axisRestriction 1 (toBranch 0 φ) = ambientAxisRestriction 2 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

theorem axisRestriction_toBranch_11 (φ : AmbientGerm) :
    axisRestriction 1 (toBranch 1 φ) = ambientAxisRestriction 2 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

theorem axisRestriction_toBranch_12 (φ : AmbientGerm) :
    axisRestriction 1 (toBranch 2 φ) = ambientAxisRestriction 1 φ := by
  apply axisRestriction_toBranch_of_coordinate
  intro t
  ext k
  fin_cases k <;> simp [insertZero, Fin.insertNth, Fin.succAboveCases]

end Wikipedia.HopfProblem.CuspNormalization.SheafGermComplex
