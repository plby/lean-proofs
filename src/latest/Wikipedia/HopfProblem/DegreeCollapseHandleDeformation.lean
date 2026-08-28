import Wikipedia.HopfProblem.DegreeCollapseHandleRetraction
import Mathlib.Topology.Homotopy.Equiv
import Mathlib.Analysis.Normed.Module.Convex

/-!
# A handle strongly deforms onto its attaching face and core

Straight interpolation to the explicit retraction stays inside both disks
and fixes the entire attaching face and core throughout the homotopy. Thus
this is relative geometric data suitable for gluing to a lower sublevel.
-/

noncomputable section

open Set Metric
open scoped unitInterval ContinuousMap

namespace Wikipedia.HopfProblem.DegreeCollapse.Handle

variable {N P : Type*} [NormedAddCommGroup N] [NormedSpace ℝ N]
  [NormedAddCommGroup P] [NormedSpace ℝ P]

def interpolate (t : I) (z : Space (N := N) (P := P)) : Space (N := N) (P := P) :=
  (⟨(1 - (t : ℝ)) • (z.1 : N) + (t : ℝ) • ((retraction z).1 : N),
    (convex_closedBall (0 : N) 1 : Convex ℝ _) z.1.property (retraction z).1.property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩,
   ⟨(1 - (t : ℝ)) • (z.2 : P) + (t : ℝ) • ((retraction z).2 : P),
    (convex_closedBall (0 : P) 1 : Convex ℝ _) z.2.property (retraction z).2.property
      (sub_nonneg.mpr t.property.2) t.property.1 (by ring)⟩)

theorem continuous_interpolate :
    Continuous (fun tz : I × Space (N := N) (P := P) => interpolate tz.1 tz.2) := by
  have ht : Continuous (fun tz : I × Space (N := N) (P := P) => (tz.1 : ℝ)) :=
    continuous_subtype_val.comp continuous_fst
  have hu : Continuous (fun tz : I × Space (N := N) (P := P) => (tz.2.1 : N)) :=
    continuous_subtype_val.comp (continuous_fst.comp continuous_snd)
  have hv : Continuous (fun tz : I × Space (N := N) (P := P) => (tz.2.2 : P)) :=
    continuous_subtype_val.comp (continuous_snd.comp continuous_snd)
  have hr : Continuous (fun tz : I × Space (N := N) (P := P) => retraction tz.2) :=
    retraction.continuous.comp continuous_snd
  exact (((continuous_const.sub ht).smul hu).add
    (ht.smul (continuous_subtype_val.comp (continuous_fst.comp hr)))).subtype_mk _ |>.prodMk
      ((((continuous_const.sub ht).smul hv).add
        (ht.smul (continuous_subtype_val.comp (continuous_snd.comp hr)))).subtype_mk _)

@[simp] theorem interpolate_zero (z : Space (N := N) (P := P)) : interpolate 0 z = z := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

@[simp] theorem interpolate_one (z : Space (N := N) (P := P)) :
    interpolate 1 z = retraction z := by
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate]

theorem interpolate_fixed (t : I) (z : Space (N := N) (P := P)) (hz : z ∈ faceCore) :
    interpolate t z = z := by
  have hr := retraction_eq_self z hz
  apply Prod.ext <;> apply Subtype.ext <;> simp [interpolate, hr, ← add_smul]

/-- This native relative homotopy fixes the attaching face at every time. -/
def deformation :
    (ContinuousMap.id (Space (N := N) (P := P))).HomotopyRel retraction faceCore where
  toFun tz := interpolate tz.1 tz.2
  continuous_toFun := continuous_interpolate
  map_zero_left := interpolate_zero
  map_one_left := interpolate_one
  prop' := interpolate_fixed

/-- The relative deformation supplies a genuine homotopy equivalence of the actual spaces. -/
def faceCoreHomotopyEquiv :
    ↥(faceCore (N := N) (P := P)) ≃ₕ Space (N := N) (P := P) where
  toFun := ⟨Subtype.val, continuous_subtype_val⟩
  invFun := ⟨fun z => ⟨retraction z, retraction_mem_faceCore z⟩,
    retraction.continuous.subtype_mk _⟩
  left_inv := by
    have he : (⟨fun z => ⟨retraction z, retraction_mem_faceCore z⟩,
        retraction.continuous.subtype_mk _⟩ :
        C(Space (N := N) (P := P), faceCore (N := N) (P := P))).comp
        ⟨Subtype.val, continuous_subtype_val⟩ =
          ContinuousMap.id ↥(faceCore (N := N) (P := P)) := by
      apply ContinuousMap.ext
      intro z
      apply Subtype.ext
      exact retraction_eq_self z.val z.property
    rw [he]
  right_inv := ⟨deformation.toHomotopy.symm⟩

end Wikipedia.HopfProblem.DegreeCollapse.Handle
