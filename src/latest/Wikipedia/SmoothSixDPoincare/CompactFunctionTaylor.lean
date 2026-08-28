import Wikipedia.SmoothSixDPoincare.CompactFunctionDerivative
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.Compactness.Compact
import Mathlib.Tactic.Abel

/-!
# A uniform first-order remainder along a compact continuous family

Continuity of the derivative gives one normal radius for the entire compact
source. The mean-value estimate on each convex ball then controls the actual
Taylor remainder uniformly. No finite-dimensionality or derivative bound is
assumed for the continuous-function space.
-/

noncomputable section

open Set Metric Filter Topology ContinuousMap

namespace Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_derivative_radius (L : C(E, E →L[ℝ] F)) (a : C(X, E))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x (h : E), ‖h‖ < δ → ‖L (a x + h) - L (a x)‖ < ε := by
  have hc : Continuous (fun z : E × X => L (a z.2 + z.1) - L (a z.2)) :=
    (L.continuous.comp ((a.continuous.comp continuous_snd).add continuous_fst)).sub
      (L.continuous.comp (a.continuous.comp continuous_snd))
  have hU : IsOpen {z : E × X | ‖L (a z.2 + z.1) - L (a z.2)‖ < ε} :=
    isOpen_lt hc.norm continuous_const
  have hnear : ∀ᶠ h in 𝓝 (0 : E), ∀ x, ‖L (a x + h) - L (a x)‖ < ε := by
    have h := isCompact_univ.eventually_forall_of_forall_eventually
      (x₀ := (0 : E)) (P := fun h x => ‖L (a x + h) - L (a x)‖ < ε)
      (fun x (_ : x ∈ (univ : Set X)) => hU.mem_nhds (by simpa using hε))
    filter_upwards [h] with h hh
    exact fun x => hh x (mem_univ x)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp hnear
  exact ⟨δ, hδ, fun x h hh => hball (mem_ball_zero_iff.mpr hh) x⟩

theorem exists_uniform_taylor_remainder (f : C(E, F)) (L : C(E, E →L[ℝ] F))
    (hf : ∀ x, HasFDerivAt f (L x) x) (a : C(X, E)) {ε : ℝ} (hε : 0 < ε) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ x y, ‖y - a x‖ < δ →
      ‖f y - f (a x) - L (a x) (y - a x)‖ ≤ ε * ‖y - a x‖ := by
  obtain ⟨δ, hδ, hL⟩ := exists_uniform_derivative_radius L a hε
  refine ⟨δ, hδ, ?_⟩
  intro x y hy
  have hder (z : E) : HasFDerivAt (fun z : E => f z - L (a x) z) (L z - L (a x)) z :=
    (hf z).sub (L (a x)).hasFDerivAt
  have hbound (z : E) (hz : z ∈ ball (a x) δ) : ‖L z - L (a x)‖ ≤ ε := by
    have hh : ‖z - a x‖ < δ := by simpa only [mem_ball, dist_eq_norm] using hz
    have hadd : a x + (z - a x) = z := by abel
    simpa only [hadd] using (hL x (z - a x) hh).le
  have hmean := (convex_ball (a x) δ).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun z _ => (hder z).hasFDerivWithinAt) hbound (mem_ball_self hδ)
      (show y ∈ ball (a x) δ by simpa only [mem_ball, dist_eq_norm] using hy)
  have heq : (f y - L (a x) y) - (f (a x) - L (a x) (a x)) =
      f y - f (a x) - L (a x) (y - a x) := by
    rw [map_sub]
    abel
  rwa [heq] at hmean

end Wikipedia.SmoothSixDPoincare.FunctionSpaceCalculus
