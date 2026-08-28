import Wikipedia.SmoothSixDPoincare.LocalDegreeLinearization
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Constructing the small boundary around an actual regular zero

The radius is chosen from the derivative estimate and any prescribed
neighborhood of the center. The boundary map and its zero-avoiding homotopy
retain the original function evaluated at that actual radius.
-/

noncomputable section

open Set Metric Topology Filter ContinuousMap
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.LocalDegree

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

structure BoundaryData (f : E → F) (L : E ≃L[ℝ] F) (s : Set E) where
  radius : ℝ
  radius_pos : 0 < radius
  ball_subset : closedBall 0 radius ⊆ s
  continuous : Continuous (fun u : sphere (0 : E) 1 => f (radius • (u : E)))
  remainder_bound : ∀ u : sphere (0 : E) 1,
    ‖f (radius • (u : E)) - L (radius • (u : E))‖ ≤
      (1 / 2 : ℝ) * ‖L (radius • (u : E))‖

theorem norm_radius_smul (r : ℝ) (hr : 0 < r) (u : sphere (0 : E) 1) :
    ‖r • (u : E)‖ = r := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos hr,
    mem_sphere_zero_iff_norm.mp u.property, mul_one]

theorem nonempty_boundaryData {f : E → F} (L : E ≃L[ℝ] F) {s : Set E}
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContinuousOn f s) :
    Nonempty (BoundaryData f L s) := by
  obtain ⟨δ, hδ, hδs⟩ := Metric.mem_nhds_iff.mp hs
  obtain ⟨ε, hε, hεb⟩ := exists_pos_remainder_bound L hf hzero
  let r : ℝ := min δ ε / 2
  have hr : 0 < r := half_pos (lt_min hδ hε)
  have hrδ : r < δ := (half_lt_self (lt_min hδ hε)).trans_le (min_le_left δ ε)
  have hrε : r < ε := (half_lt_self (lt_min hδ hε)).trans_le (min_le_right δ ε)
  have hball : closedBall (0 : E) r ⊆ s :=
    (closedBall_subset_ball hrδ).trans hδs
  have hparam (u : sphere (0 : E) 1) : r • (u : E) ∈ closedBall (0 : E) r := by
    rw [mem_closedBall_zero_iff, norm_radius_smul r hr u]
  have hparamc : Continuous (fun u : sphere (0 : E) 1 => r • (u : E)) :=
    continuous_const.smul continuous_subtype_val
  refine ⟨⟨r, hr, hball, hc.comp_continuous hparamc (fun u => hball (hparam u)), ?_⟩⟩
  intro u
  apply hεb
  rw [mem_ball_zero_iff, norm_radius_smul r hr u]
  exact hrε

theorem nonempty_boundaryData_of_contDiffAt {f : E → F} (L : E ≃L[ℝ] F) {s : Set E}
    (hf : HasFDerivAt f L.toContinuousLinearMap 0) (hzero : f 0 = 0)
    (hs : s ∈ 𝓝 (0 : E)) (hc : ContDiffAt ℝ ∞ f 0) :
    Nonempty (BoundaryData f L s) := by
  obtain ⟨t, ht, htc⟩ := contDiffAt_zero.mp (hc.of_le (by simp))
  obtain ⟨b⟩ := nonempty_boundaryData L hf hzero (inter_mem hs ht)
    (htc.mono inter_subset_right)
  exact ⟨{ b with ball_subset := b.ball_subset.trans inter_subset_left }⟩

namespace BoundaryData

variable {f : E → F} {L : E ≃L[ℝ] F} {s : Set E} (b : BoundaryData f L s)

def map : C(sphere (0 : E) 1, PuncturedRadial.Space F) :=
  boundaryMap f L b.radius b.radius_pos b.continuous b.remainder_bound

theorem map_coe (u : sphere (0 : E) 1) : (b.map u).val = f (b.radius • (u : E)) := rfl

def homotopy : (linearSphereMap L b.radius b.radius_pos).Homotopy b.map :=
  boundaryHomotopy f L b.radius b.radius_pos b.continuous b.remainder_bound

end BoundaryData

end Wikipedia.SmoothSixDPoincare.LocalDegree
