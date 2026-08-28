import Wikipedia.HopfProblem.CuspControlledRetractionFibre
import Wikipedia.HopfProblem.ToricTorusChart

/-!
# Literal fibre spaces for the positive-level specialization model

These are fixed-time subspaces of the original toric space and its actual
positive part. Subsequent files construct the phase-plane presentation
at a positive real level `ρ`. This is a specialization of the fixed-fibre
construction, not an identification of arbitrary complex levels: at a
nonreal level the base phase contributes an additional factor to the deck
action and to the prescribed central collapse.
-/

noncomputable section

open Set Topology
open scoped ContinuousMap

namespace Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel

open ToricSpace CuspRetraction CuspControlledRetraction

/-- The fixed-time subspace of the actual glued toric space. -/
abbrev ToricFibre (t : ℂ) := {x : Space // time x = t}

/-- The positive fixed-height subspace, with its original subspace topology. -/
abbrev PositiveFibre (ρ : ℝ) := {q : PositivePart // time (q : Space) = (ρ : ℂ)}

@[simp] theorem time_toricFibre (t : ℂ) (x : ToricFibre t) : time (x : Space) = t := x.2

@[simp] theorem time_positiveFibre (ρ : ℝ) (q : PositiveFibre ρ) :
    time (q.1 : Space) = (ρ : ℂ) := q.2

theorem norm_time_positiveFibre (ρ : ℝ) (hρ : 0 ≤ ρ) (q : PositiveFibre ρ) :
    ‖time (q.1 : Space)‖ = ρ := by
  rw [q.2, Complex.norm_of_nonneg hρ]

def toricFibreInclusion (t : ℂ) : C(ToricFibre t, Space) :=
  ⟨Subtype.val, continuous_subtype_val⟩

def positiveFibreInclusion (ρ : ℝ) : C(PositiveFibre ρ, Space) :=
  ⟨fun q => (q.1 : Space), continuous_subtype_val.comp continuous_subtype_val⟩

/-- Adding or removing the redundant closed-tube condition does not change
the literal fixed-time fibre or its topology. -/
def toricFibreLevelHomeomorph (η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η) :
    ToricFibre t ≃ₜ ToricLevel η t where
  toFun x := ⟨⟨(x : Space), by rw [x.2]; exact htη⟩, x.2⟩
  invFun x := ⟨(x.1 : Space), x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact continuous_subtype_val.subtype_mk _
  continuous_invFun := (continuous_subtype_val.comp continuous_subtype_val).subtype_mk _

@[simp] theorem toricFibreLevelHomeomorph_coe (η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η)
    (x : ToricFibre t) :
    ((toricFibreLevelHomeomorph η t htη x).1 : Space) = (x : Space) := rfl

@[simp] theorem toricFibreLevelHomeomorph_symm_coe (η : ℝ) (t : ℂ) (htη : ‖t‖ ≤ η)
    (x : ToricLevel η t) :
    ((toricFibreLevelHomeomorph η t htη).symm x : Space) = (x.1 : Space) := rfl

end Wikipedia.HopfProblem.CuspCentralHomology.SpecializationModel
