import ErdosProblems.Erdos1197.TorusAverageBase

namespace Erdos1197

open scoped BigOperators

noncomputable section

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

lemma integrable_translateFamily {d : Type*} [Finite d]
    (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) :
    letI : Fintype d := Fintype.ofFinite d
    Integrable
      (fun h : H => f.comp (torusTranslate (d := d) (h : UnitAddTorus d)))
      (addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  let _ : Fintype d := Fintype.ofFinite d
  let μH : Measure H := addHaarMeasure (subgroupUnivPositiveCompact (α := H))
  have hcont :
      Continuous (fun h : H =>
        f.comp (torusTranslate (d := d) (h : UnitAddTorus d))) := by
    refine ContinuousMap.continuous_of_continuous_uncurry _ ?_
    change Continuous (fun z : H × UnitAddTorus d => f (z.2 + (z.1 : UnitAddTorus d)))
    exact f.continuous.comp
      ((continuous_snd).add ((continuous_subtype_val).comp continuous_fst))
  simpa [μH] using
    (hcont.continuousOn.integrableOn_compact (μ := μH) (K := (Set.univ : Set H)) isCompact_univ)

lemma avgOverSubgroup_apply (H : ClosedAddSubgroup (UnitAddTorus d))
    (f : C(UnitAddTorus d, ℂ)) (y : UnitAddTorus d) :
    avgOverSubgroup (d := d) H f y =
      ∫ h : H, f (y + h) ∂(addHaarMeasure (subgroupUnivPositiveCompact (α := H))) := by
  rw [avgOverSubgroup, ContinuousMap.integral_apply (integrable_translateFamily (d := d) H f)]
  rfl


end

end Erdos1197
