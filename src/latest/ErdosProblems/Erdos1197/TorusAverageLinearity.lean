import ErdosProblems.Erdos1197.TorusAverageDefinitions

namespace Erdos1197

open scoped BigOperators

noncomputable section

open MeasureTheory
open UnitAddTorus
open MeasureTheory.Measure

variable {d : Type*} [Fintype d]

lemma avgOverSubgroup_sub (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f - g) =
      avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f - g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) -
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_sub (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_add (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (f + g) =
      avgOverSubgroup (d := d) H f + avgOverSubgroup (d := d) H g := by
  rw [avgOverSubgroup, avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (f + g).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H =>
          f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) +
            g.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp]
  rw [integral_add (integrable_translateFamily (d := d) H f)
    (integrable_translateFamily (d := d) H g)]

lemma avgOverSubgroup_smul (H : ClosedAddSubgroup (UnitAddTorus d))
    (c : ℂ) (f : C(UnitAddTorus d, ℂ)) :
    avgOverSubgroup (d := d) H (c • f) =
      c • avgOverSubgroup (d := d) H f := by
  rw [avgOverSubgroup, avgOverSubgroup]
  have hcomp :
      (fun h : H => (c • f).comp (torusTranslate (d := d) (h : UnitAddTorus d))) =
        fun h : H => c • f.comp (torusTranslate (d := d) (h : UnitAddTorus d)) := by
    funext h
    ext y
    rfl
  rw [hcomp, integral_smul]

lemma avgOverSubgroup_norm_sub_le (H : ClosedAddSubgroup (UnitAddTorus d))
    (f g : C(UnitAddTorus d, ℂ)) :
    ‖avgOverSubgroup (d := d) H f - avgOverSubgroup (d := d) H g‖ ≤ ‖f - g‖ := by
  rw [← avgOverSubgroup_sub (d := d) H f g]
  exact avgOverSubgroup_norm_le (d := d) H (f - g)

lemma avgOverSubgroup_lipschitz (H : ClosedAddSubgroup (UnitAddTorus d)) :
    LipschitzWith 1 (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) := by
  refine LipschitzWith.of_dist_le_mul ?_
  intro f g
  simpa [dist_eq_norm] using avgOverSubgroup_norm_sub_le (d := d) H f g

lemma avgOverSubgroup_continuous (H : ClosedAddSubgroup (UnitAddTorus d)) :
    Continuous (avgOverSubgroup (d := d) H : C(UnitAddTorus d, ℂ) → C(UnitAddTorus d, ℂ)) :=
  (avgOverSubgroup_lipschitz (d := d) H).continuous



end

end Erdos1197
