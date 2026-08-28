import Wikipedia.NoExoticSixSphere.RectangularSmoothNormalization
import Wikipedia.NoExoticSixSphere.CompactParameter
import Mathlib.Geometry.Manifold.SmoothApprox

/-!
# Relative smoothing of partial frames on a compact Euclidean region

Uniform injectivity on the compact region gives a positive approximation
tolerance. Project a relative smooth ambient approximation into the original
subspaces and normalize by smooth rectangular Gram--Schmidt. Already smooth
protected frame values stay exactly fixed.
-/

noncomputable section

open Set Function
open scoped ContDiff Topology

namespace NoExoticSixSphere.Stiefel

open GLOrthonormalization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
variable {N n : ℕ}

theorem exists_smoothPartialFrame_rel {K S U : Set E} (hK : IsCompact K)
    (A : E → Vector n →L[ℝ] Vector N) (hA : Continuous A)
    (P : E → Vector N →L[ℝ] Vector N)
    (hPs : ∀ x ∈ K, ContDiffAt ℝ ∞ P x)
    (hAPi : ∀ x ∈ K, Injective ((P x).comp (A x)))
    (hPA : ∀ x ∈ K ∩ S, (P x).comp (A x) = A x)
    (hAi : ∀ x ∈ K ∩ S, ∀ w, ‖A x w‖ = ‖w‖)
    (hS : IsClosed S) (hU : U ∈ 𝓝ˢ S) (hAU : ContDiffOn ℝ ∞ A U) :
    ∃ T : E → Vector n →L[ℝ] Vector N,
      (∀ x ∈ K, ContDiffAt ℝ ∞ T x) ∧
      (∀ x ∈ K, ∀ w, ‖T x w‖ = ‖w‖) ∧
      (∀ x ∈ K, (T x).range ≤ (P x).range) ∧ EqOn T A (K ∩ S) := by
  let : CompactSpace K := isCompact_iff_compactSpace.mp hK
  have hPc : Continuous (fun x : K ↦ P x) := by
    apply continuous_iff_continuousAt.mpr
    intro x
    exact (hPs x x.property).continuousAt.comp continuous_subtype_val.continuousAt
  let V : Set (Vector n →L[ℝ] Vector N) :=
    {L | ∀ x : K, Injective ((P x).comp (A x + L))}
  have hV : IsOpen V := by
    have hc : Continuous (fun z : (Vector n →L[ℝ] Vector N) × K ↦
        (P z.2).comp (A z.2 + z.1)) :=
      (hPc.comp continuous_snd).clm_comp
        (((hA.comp continuous_subtype_val).comp continuous_snd).add continuous_fst)
    exact isOpen_forall_compact (ContinuousLinearMap.isOpen_injective.preimage hc)
  have hzero : (0 : Vector n →L[ℝ] Vector N) ∈ V := by
    intro x
    simpa only [add_zero] using hAPi x x.property
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hV 0 hzero
  obtain ⟨g, hgs, hg, heq, _⟩ := hA.exists_contDiff_approx_and_eqOn (⊤ : ℕ∞)
    continuous_const (fun _ ↦ hε) hS hU hAU
  let B : E → Vector n →L[ℝ] Vector N := fun x ↦ (P x).comp (g x)
  have hBi (x : E) (hx : x ∈ K) : Injective (B x) := by
    have hb : g x - A x ∈ Metric.ball 0 ε := by
      simpa only [Metric.mem_ball, dist_zero_right, dist_eq_norm, sub_zero] using hg x
    have h := hball hb ⟨x, hx⟩
    simpa only [← add_sub_assoc, add_sub_cancel_left] using h
  refine ⟨Orthonormalization.operator B, ?_, ?_, ?_, ?_⟩
  · intro x hx
    exact Orthonormalization.contDiffAt_operator B x
      ((hPs x hx).clm_comp hgs.contDiffAt) (hBi x hx)
  · intro x hx w
    exact Orthonormalization.operator_norm B x (hBi x hx) w
  · intro x hx
    rw [Orthonormalization.operator_range B x (hBi x hx)]
    rintro y ⟨w, rfl⟩
    exact ⟨g x w, rfl⟩
  · intro x hx
    have hB : B x = A x := by
      change (P x).comp (g x) = A x
      rw [heq hx.2, hPA x hx]
    exact (Orthonormalization.operator_eq_self B x (by rw [hB]; exact hAi x hx)).trans hB

end NoExoticSixSphere.Stiefel
