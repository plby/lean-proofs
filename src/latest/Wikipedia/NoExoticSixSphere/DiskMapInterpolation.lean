import Wikipedia.NoExoticSixSphere.DiskBoundaryNullhomotopy

/-!
# Relative interpolation between maps into the actual closed disk

Straight interpolation stays in the original norm disk and fixes every
point where the two endpoint maps agree. This will compare disk-coordinate
contractions while retaining both path endpoints and the chosen basepoint.
-/

noncomputable section

open Set Metric
open scoped unitInterval
open Wikipedia.HopfProblem.DegreeCollapse

namespace NoExoticSixSphere.DiskMapInterpolation

variable {E X : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace X]

def homotopyRel (F G : C(X, DiskCylinder.Disk (E := E))) (S : Set X) (h : EqOn F G S) :
    F.HomotopyRel G S where
  toFun p := ⟨(1 - (p.1 : ℝ)) • (F p.2).val + (p.1 : ℝ) • (G p.2).val,
    (convex_closedBall (0 : E) 1) (F p.2).property (G p.2).property
      (sub_nonneg.mpr p.1.property.2) p.1.property.1 (sub_add_cancel 1 (p.1 : ℝ))⟩
  continuous_toFun :=
    (((continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
      (continuous_subtype_val.comp (F.continuous.comp continuous_snd))).add
        ((continuous_subtype_val.comp continuous_fst).smul
          (continuous_subtype_val.comp (G.continuous.comp continuous_snd)))).subtype_mk _
  map_zero_left x := by
    apply Subtype.ext
    change (1 - (0 : ℝ)) • (F x).val + (0 : ℝ) • (G x).val = (F x).val
    simp
  map_one_left x := by
    apply Subtype.ext
    change (1 - (1 : ℝ)) • (F x).val + (1 : ℝ) • (G x).val = (G x).val
    simp
  prop' t x hx := by
    apply Subtype.ext
    change (1 - (t : ℝ)) • (F x).val + (t : ℝ) • (G x).val = (F x).val
    rw [← h hx, ← add_smul, sub_add_cancel, one_smul]

end NoExoticSixSphere.DiskMapInterpolation
