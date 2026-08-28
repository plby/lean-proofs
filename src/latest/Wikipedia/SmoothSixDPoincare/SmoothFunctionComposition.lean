import Wikipedia.SmoothSixDPoincare.CompactFunctionTaylor
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Smooth composition on the Banach space of continuous functions on a compact space

The derivative is the original pointwise derivative field acting on the
whole increment. The uniform Taylor estimate proves Fréchet differentiability;
induction on differentiability order proves smoothness of the composition map.
This supplies the nonlinear term in the smooth local-flow integral equation.
-/

noncomputable section

open Set Metric Filter Topology ContinuousMap
open scoped ContDiff

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

section Derivative

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem hasFDerivAt_composition (f : C(E, F)) (L : C(E, E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (L x) x) (a : C(X, E)) :
    HasFDerivAt (fun b : C(X, E) => f.comp b) (applyField (L.comp a)) a := by
  rw [hasFDerivAt_iff_isLittleO, Asymptotics.isLittleO_iff]
  intro ε hε
  obtain ⟨δ, hδ, hrem⟩ := exists_uniform_taylor_remainder f L hf a hε
  filter_upwards [Metric.ball_mem_nhds a hδ] with b hb
  have hba : ‖b - a‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hb
  apply (ContinuousMap.norm_le _ (mul_nonneg hε.le (norm_nonneg _))).mpr
  intro x
  have hpoint : ‖b x - a x‖ ≤ ‖b - a‖ := (b - a).norm_coe_le_norm x
  exact (hrem x (b x) (hpoint.trans_lt hba)).trans
    (mul_le_mul_of_nonneg_left hpoint hε.le)

end Derivative

section Smoothness

variable {X E F : Type} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem contDiff_composition (n : ℕ) (f : C(E, F)) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun a : C(X, E) => f.comp a) := by
  induction n generalizing F with
  | zero => exact contDiff_zero.mpr (ContinuousMap.continuous_postcomp f)
  | succ n ih =>
      obtain ⟨L, hL, hder⟩ := contDiff_succ_iff_hasFDerivAt.mp hf
      let L₀ : C(E, E →L[ℝ] F) := ⟨L, hL.continuous⟩
      refine contDiff_succ_iff_hasFDerivAt.mpr
        ⟨fun a => applyField (L₀.comp a), ?_, fun a => hasFDerivAt_composition f L₀ hder a⟩
      have hcomp : ContDiff ℝ n (fun a : C(X, E) => L₀.comp a) := ih L₀ hL
      exact (liftField (X := X) (E := E) (F := F)).contDiff.comp hcomp

theorem contDiff_infty_composition (f : C(E, F)) (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ (fun a : C(X, E) => f.comp a) :=
  contDiff_infty.mpr (fun n => contDiff_composition n f (contDiff_infty.mp hf n))

end Smoothness

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
