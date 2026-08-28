import Wikipedia.NoExoticSixSphere.UniformProductTube
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# A uniform first-order estimate along a compact family of normal directions

The original defining equations vanish on the compact core and their
differential sends the specified normal frame to the identity. A single
positive-radius closed normal disk then has any prescribed positive
relative error bound. The estimate follows from continuity of the actual
ambient differential and the mean-value inequality on each normal disk.
-/

open Set Filter Topology Metric
open scoped ContDiff

namespace NoExoticSixSphere

variable {X E F : Type*} [TopologicalSpace X] [CompactSpace X]
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem exists_uniform_normal_remainder_bound
    {e : X → E} (he : Continuous e)
    {B : X → F →L[ℝ] E} (hB : Continuous B)
    {f : E → F} {U : Set E} (hU : IsOpen U)
    (hcore : ∀ x, e x ∈ U) (hf : ContDiffOn ℝ ∞ f U)
    (hzero : ∀ x, f (e x) = 0)
    (hder : ∀ x, (fderiv ℝ f (e x)).comp (B x) = ContinuousLinearMap.id ℝ F)
    {ε : ℝ} (hε : 0 < ε) :
    ∃ r : ℝ, 0 < r ∧ ∀ x v, ‖v‖ ≤ r →
      e x + B x v ∈ U ∧ ‖f (e x + B x v) - v‖ ≤ ε * ‖v‖ := by
  let q : X × F → E := fun p ↦ e p.1 + B p.1 p.2
  have hq : Continuous q := (he.comp continuous_fst).add
    ((hB.comp continuous_fst).clm_apply continuous_snd)
  let D : X × F → F →L[ℝ] F := fun p ↦
    (fderiv ℝ f (q p)).comp (B p.1) - ContinuousLinearMap.id ℝ F
  let W := interior {p : X × F | q p ∈ U ∧ ‖D p‖ < ε}
  have hWzero (x : X) : (x, (0 : F)) ∈ W := by
    have hqzero : q (x, 0) = e x := by simp [q]
    have hDzero : D (x, 0) = 0 := by simp [D, hqzero, hder]
    have hd : ContinuousAt (fderiv ℝ f) (q (x, 0)) := by
      rw [hqzero]
      exact (hf.continuousOn_fderiv_of_isOpen hU (by simp)).continuousAt
        (hU.mem_nhds (hcore x))
    have hD : ContinuousAt D (x, 0) :=
      ((hd.comp hq.continuousAt).clm_comp
        (hB.comp continuous_fst).continuousAt).sub continuousAt_const
    have hnear : ∀ᶠ p in 𝓝 (x, (0 : F)), q p ∈ U :=
      hq.continuousAt.preimage_mem_nhds (hU.mem_nhds (hqzero ▸ hcore x))
    have hsmall : ∀ᶠ p in 𝓝 (x, (0 : F)), ‖D p‖ < ε := by
      have hh := hD.norm.eventually (gt_mem_nhds (show ‖D (x, 0)‖ < ε by
        rw [hDzero, norm_zero]
        exact hε))
      exact hh
    exact mem_interior_iff_mem_nhds.mpr (hnear.and hsmall)
  obtain ⟨r, hr, hW⟩ := exists_uniform_closedProductTube isOpen_interior hWzero
  have hbound (x : X) (v : F) (hv : ‖v‖ ≤ r) :
      q (x, v) ∈ U ∧ ‖D (x, v)‖ < ε :=
    (interior_subset (s := {p : X × F | q p ∈ U ∧ ‖D p‖ < ε})) (hW x v hv)
  refine ⟨r, hr, fun x v hv ↦ ⟨(hbound x v hv).1, ?_⟩⟩
  let g : F → F := fun w ↦ f (e x + B x w) - w
  have hg (w : F) (hw : w ∈ closedBall (0 : F) r) :
      HasFDerivAt g (D (x, w)) w := by
    have hwU := (hbound x w (mem_closedBall_zero_iff.mp hw)).1
    have hfd := ((hf.contDiffAt (hU.mem_nhds hwU)).differentiableAt (by simp)).hasFDerivAt
    exact (hfd.comp w ((B x).hasFDerivAt.const_add (e x))).sub (hasFDerivAt_id w)
  have hmean := (convex_closedBall (0 : F) r).norm_image_sub_le_of_norm_hasFDerivWithin_le
    (fun w hw ↦ (hg w hw).hasFDerivWithinAt)
    (fun w hw ↦ (hbound x w (mem_closedBall_zero_iff.mp hw)).2.le)
    (mem_closedBall_self hr.le) (mem_closedBall_zero_iff.mpr hv)
  simpa only [g, map_zero, add_zero, hzero, sub_zero] using hmean

omit [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Relative errors in a fixed ball are preserved under convex interpolation. -/
theorem norm_convex_blend_sub_le {u w v : F} {ε t : ℝ}
    (hu : ‖u - v‖ ≤ ε * ‖v‖) (hw : ‖w - v‖ ≤ ε * ‖v‖)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    ‖(1 - t) • u + t • w - v‖ ≤ ε * ‖v‖ := by
  have heq : (1 - t) • u + t • w - v = (1 - t) • (u - v) + t • (w - v) := by
    module
  rw [heq]
  calc
    ‖(1 - t) • (u - v) + t • (w - v)‖ ≤
        ‖(1 - t) • (u - v)‖ + ‖t • (w - v)‖ := norm_add_le _ _
    _ = (1 - t) * ‖u - v‖ + t * ‖w - v‖ := by
      rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_nonneg (sub_nonneg.mpr ht.2), abs_of_nonneg ht.1]
    _ ≤ (1 - t) * (ε * ‖v‖) + t * (ε * ‖v‖) :=
      add_le_add (mul_le_mul_of_nonneg_left hu (sub_nonneg.mpr ht.2))
        (mul_le_mul_of_nonneg_left hw ht.1)
    _ = ε * ‖v‖ := by ring

omit [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] in
theorem convex_blend_eq_zero_iff_of_relative_error {u w v : F} {ε t : ℝ}
    (hε : ε < 1) (hu : ‖u - v‖ ≤ ε * ‖v‖) (hw : ‖w - v‖ ≤ ε * ‖v‖)
    (ht : t ∈ Icc (0 : ℝ) 1) :
    (1 - t) • u + t • w = 0 ↔ v = 0 := by
  have hbound := norm_convex_blend_sub_le hu hw ht
  constructor
  · intro hzero
    rw [hzero, zero_sub, norm_neg] at hbound
    exact norm_eq_zero.mp (by nlinarith [norm_nonneg v])
  · intro hv
    rw [hv, sub_zero, norm_zero, mul_zero] at hbound
    exact norm_eq_zero.mp (le_antisymm hbound (norm_nonneg _))

omit [TopologicalSpace X] [CompactSpace X] [NormedAddCommGroup E] [NormedSpace ℝ E] in
/-- Positive rescaling of the two endpoints changes a convex segment only
by a positive scalar and a reparametrization. -/
theorem exists_convex_blend_positive_rescaling {r₀ r₁ t : ℝ}
    (h₀ : 0 < r₀) (h₁ : 0 < r₁) (ht : t ∈ Icc (0 : ℝ) 1) :
    ∃ s ∈ Icc (0 : ℝ) 1, ∃ c : ℝ, 0 < c ∧ ∀ u w : F,
      (1 - s) • (r₀ • u) + s • (r₁ • w) = c • ((1 - t) • u + t • w) := by
  let D := (1 - t) * r₁ + t * r₀
  have hD : 0 < D := by
    rcases eq_or_lt_of_le ht.1 with ht0 | ht0
    · simp [D, ← ht0, h₁]
    · exact add_pos_of_nonneg_of_pos (mul_nonneg (sub_nonneg.mpr ht.2) h₁.le)
        (mul_pos ht0 h₀)
  let s := t * r₀ / D
  let c := r₀ * r₁ / D
  have hs : s ∈ Icc (0 : ℝ) 1 := by
    refine ⟨div_nonneg (mul_nonneg ht.1 h₀.le) hD.le, ?_⟩
    apply (div_le_one hD).mpr
    exact le_add_of_nonneg_left (mul_nonneg (sub_nonneg.mpr ht.2) h₁.le)
  have hc : 0 < c := div_pos (mul_pos h₀ h₁) hD
  refine ⟨s, hs, c, hc, fun u w ↦ ?_⟩
  have hleft : (1 - s) * r₀ = c * (1 - t) := by
    dsimp [s, c]
    field_simp
    dsimp [D]
    ring
  have hright : s * r₁ = c * t := by dsimp [s, c]; ring
  rw [smul_smul, smul_smul, smul_add, smul_smul, smul_smul, hleft, hright]

end NoExoticSixSphere
