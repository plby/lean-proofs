import ErdosProblems.Erdos1197.TorusAverageMeasure

namespace Erdos1197

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

/-- Pointwise norm control for averaging over a normalized closed subgroup. -/
lemma avgOverSubgroup_norm_apply_le
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) (y : UnitAddTorus d) :
    ‖avgOverSubgroup (d := d) H f y‖ ≤ ‖f‖ := by
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hμ : μH Set.univ = 1 := by
    simpa [μH] using subgroup_univ_measure (d := d) H
  haveI : IsFiniteMeasure μH := ⟨by simp [hμ]⟩
  rw [avgOverSubgroup_apply]
  have hbound : ∀ᵐ h : H ∂μH, ‖f (y + h)‖ ≤ ‖f‖ := by
    exact Filter.Eventually.of_forall (fun h => f.norm_coe_le_norm (y + h))
  calc
    ‖∫ h : H, f (y + h) ∂μH‖ ≤ ‖f‖ * μH.real Set.univ := by
      exact MeasureTheory.norm_integral_le_of_norm_le_const (μ := μH) hbound
    _ = ‖f‖ := by
      rw [Measure.real_def, hμ, ENNReal.toReal_one, mul_one]

end Erdos1197
