import Wikipedia.NoExoticSixSphere.CompactParameter
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.Normed.Module.Normalize
import Mathlib.Analysis.Normed.Operator.Bilinear
import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Uniform negative bounds near a negative bilinear form

Negativity on a finite-dimensional linear family gives a uniform quadratic
bound on a neighborhood of the bilinear form. Compactness is applied to the
unit sphere of the parameter space, with its actual norm.
-/

open Set Filter NormedSpace
open scoped Topology

namespace NoExoticSixSphere.NegativeFormNeighborhood

variable {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem exists_uniform_bound (Q : E →L[ℝ] E →L[ℝ] ℝ) (L : D →L[ℝ] E)
    (hneg : ∀ w : D, w ≠ 0 → Q (L w) (L w) < 0) :
    ∃ c > 0, ∀ᶠ B in 𝓝 Q, ∀ w : D, B (L w) (L w) ≤ -c * ‖w‖ ^ 2 := by
  let S := Metric.sphere (0 : D) 1
  have hcompact : IsCompact S := isCompact_sphere _ _
  have hnorm (w : D) (hw : w ∈ S) : ‖w‖ = 1 := by
    simpa only [S, Metric.mem_sphere, dist_zero_right] using hw
  have hcont : Continuous (fun w : D ↦ -Q (L w) (L w)) :=
    ((continuous_const.clm_apply L.continuous).clm_apply L.continuous).neg
  have hpositive : ∀ w ∈ S, 0 < -Q (L w) (L w) := by
    intro w hw
    apply neg_pos.mpr
    apply hneg w
    intro hz
    have hh := hnorm w hw
    simp only [hz, norm_zero, zero_ne_one] at hh
  obtain ⟨c, hc, hlower⟩ := hcompact.exists_forall_le' hcont.continuousOn hpositive
  let : CompactSpace S := isCompact_iff_compactSpace.mp hcompact
  have hval : Continuous (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × S ↦ L p.2.1) :=
    L.continuous.comp (continuous_subtype_val.comp continuous_snd)
  have hpair : Continuous (fun p : (E →L[ℝ] E →L[ℝ] ℝ) × S ↦ p.1 (L p.2.1) (L p.2.1)) :=
    (continuous_fst.clm_apply hval).clm_apply hval
  have ho : IsOpen {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ w : S, B (L w.1) (L w.1) < -(c / 2)} :=
    isOpen_forall_compact (isOpen_lt hpair continuous_const)
  have hQ : Q ∈ {B : E →L[ℝ] E →L[ℝ] ℝ | ∀ w : S, B (L w.1) (L w.1) < -(c / 2)} := by
    intro w
    have hh := hlower w.1 w.2
    linarith
  refine ⟨c / 2, by linarith, ?_⟩
  filter_upwards [ho.mem_nhds hQ] with B hB
  intro w
  by_cases hz : w = 0
  · simp [hz]
  · have hn : normalize w ∈ S := by
      simpa only [S, Metric.mem_sphere, dist_zero_right] using norm_normalize hz
    have hb := (hB ⟨normalize w, hn⟩).le
    have hscale (r : ℝ) (z : D) :
        B (L (r • z)) (L (r • z)) = r ^ 2 * B (L z) (L z) := by
      simp only [map_smul, smul_apply, smul_eq_mul]
      ring
    calc
      B (L w) (L w) = B (L (‖w‖ • normalize w)) (L (‖w‖ • normalize w)) := by
        rw [norm_smul_normalize]
      _ = ‖w‖ ^ 2 * B (L (normalize w)) (L (normalize w)) := hscale _ _
      _ ≤ ‖w‖ ^ 2 * -(c / 2) := mul_le_mul_of_nonneg_left hb (sq_nonneg _)
      _ = -(c / 2) * ‖w‖ ^ 2 := by ring

end NoExoticSixSphere.NegativeFormNeighborhood
