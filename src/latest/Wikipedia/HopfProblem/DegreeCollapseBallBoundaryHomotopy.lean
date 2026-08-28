import Wikipedia.HopfProblem.DegreeCollapseNativeTubeMeridian

/-!
# The boundary of an actual ball contracts through its given extension

The positive belt coordinate extends over the small parameter ball.
Contract that ball by scalar multiplication, retaining the actual center
and the original boundary parametrization.
-/

noncomputable section

open Set Metric ContinuousMap
open scoped Topology
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {A : Type} [NormedAddCommGroup A] [NormedSpace ℝ A]

def parameterBallBoundary (r : ℝ) (hr : 0 < r) :
    C(sphere (0 : A) 1, closedBall (0 : A) r) where
  toFun u := ⟨r • u.val, by
    rw [mem_closedBall_zero_iff, LocalDegree.norm_radius_smul r hr u]⟩
  continuous_toFun := by
    have h : Continuous (fun u : sphere (0 : A) 1 => r • u.val) :=
      continuous_const.smul continuous_subtype_val
    exact h.subtype_mk _

def parameterBallCenter (r : ℝ) (hr : 0 < r) : closedBall (0 : A) r :=
  ⟨0, by simpa using hr.le⟩

def parameterBallContraction (r : ℝ) (hr : 0 < r) :
    (parameterBallBoundary (A := A) r hr).Homotopy
      (ContinuousMap.const _ (parameterBallCenter r hr)) where
  toFun z := ⟨(1 - (z.1 : ℝ)) • (r • z.2.val), by
    rw [mem_closedBall_zero_iff, norm_smul, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr z.1.property.2), LocalDegree.norm_radius_smul r hr z.2]
    exact mul_le_of_le_one_left hr.le (by linarith [z.1.property.1])⟩
  continuous_toFun := by
    have h : Continuous (fun z : unitInterval × sphere (0 : A) 1 =>
        (1 - (z.1 : ℝ)) • (r • z.2.val)) :=
      (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).smul
        (continuous_const.smul (continuous_subtype_val.comp continuous_snd))
    exact h.subtype_mk _
  map_zero_left u := by apply Subtype.ext; simp [parameterBallBoundary]
  map_one_left u := by apply Subtype.ext; simp [parameterBallCenter]

theorem parameterBall_boundary_nullhomotopic {Y : Type} [TopologicalSpace Y]
    (r : ℝ) (hr : 0 < r) (g : C(closedBall (0 : A) r, Y)) :
    (g.comp (parameterBallBoundary r hr)).Homotopic
      (ContinuousMap.const _ (g (parameterBallCenter r hr))) := by
  have h := (Homotopic.refl g).comp ⟨parameterBallContraction r hr⟩
  exact h

theorem normalized_pos_smul {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (r : ℝ) (hr : 0 < r) (x : F) :
    ‖r • x‖⁻¹ • (r • x) = ‖x‖⁻¹ • x := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr, mul_inv_rev, smul_smul,
    mul_assoc, inv_mul_cancel₀ hr.ne', mul_one]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
