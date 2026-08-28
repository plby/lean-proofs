import Wikipedia.HopfProblem.RiemannBoundaryProper
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Analysis.SpecialFunctions.Complex.Log

/-!
# The modulus limit at an ideal boundary point

A genuine disc homeomorphism has modulus tending to one along a source
escaping every ambient compact set. This treats the ideal vertex of a
half-strip, where a logarithmic source chart tends to infinity rather than
to a finite point of the plane.
-/

noncomputable section

open Complex Filter Metric Set
open scoped Topology

namespace Wikipedia.HopfProblem.RiemannBoundary

/-- Properness forces the unit-modulus limit when the source tends to
infinity. Eventual source membership is enough; values outside the source
domain do not enter the assertion. -/
theorem tendsto_norm_discHomeomorph_of_cocompact
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ))
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto z l (cocompact ℂ)) (hmem : ∀ᶠ i in l, z i ∈ D) :
    Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_order.mpr
  constructor
  · intro r hr
    let K : Set ℂ := (Subtype.val : D → ℂ) ''
      (e ⁻¹' ((Subtype.val : ball (0 : ℂ) 1 → ℂ) ⁻¹' closedBall 0 r))
    have hK : IsCompact K := RiemannMapping.isCompact_discHomeomorph_preimage_closedBall e hr
    have hesc : ∀ᶠ i in l, z i ∉ K := hz.eventually hK.compl_mem_cocompact
    filter_upwards [hesc, hmem] with i hi him
    apply lt_of_not_ge
    intro hle
    apply hi
    refine ⟨⟨z i, him⟩, ?_, rfl⟩
    have hh := he ⟨z i, him⟩
    simpa only [mem_preimage, mem_closedBall, dist_zero_right, ← hh] using hle
  · intro r hr
    filter_upwards [hmem] with i hi
    have hh := he ⟨z i, hi⟩
    have hb : ‖f (z i)‖ < 1 := by
      simpa only [mem_ball, dist_zero_right, ← hh] using (e ⟨z i, hi⟩).property
    exact hb.trans hr

theorem tendsto_norm_discHomeomorph_of_norm_atTop
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ))
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun i => ‖z i‖) l atTop) (hmem : ∀ᶠ i in l, z i ∈ D) :
    Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_cocompact e he _ hmem
  simpa only [Metric.cobounded_eq_cocompact] using tendsto_norm_atTop_iff_cobounded.mp hz

theorem tendsto_norm_discHomeomorph_of_im_atTop
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ))
    {α : Type*} {l : Filter α} {z : α → ℂ}
    (hz : Tendsto (fun i => (z i).im) l atTop) (hmem : ∀ᶠ i in l, z i ∈ D) :
    Tendsto (fun i => ‖f (z i)‖) l (𝓝 1) :=
  tendsto_norm_discHomeomorph_of_norm_atTop e he
    (tendsto_atTop_mono (fun i => im_le_norm (z i)) hz) hmem

/-- Inverse to the exponential coordinate on a half-strip: positive
arguments traverse the strip from its left boundary to its right one. -/
def logHalfStrip (a c : ℝ) (q : ℂ) : ℂ :=
  a - I * c * log q

@[simp] theorem logHalfStrip_re (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).re = a + c * q.arg := by
  simp [logHalfStrip, mul_re, mul_im, log_im]

@[simp] theorem logHalfStrip_im (a c : ℝ) (q : ℂ) :
    (logHalfStrip a c q).im = -c * Real.log ‖q‖ := by
  simp [logHalfStrip, mul_re, mul_im, log_re]

/-- The logarithmic half-strip chart escapes to the ideal vertex as its
parameter tends to zero. -/
theorem tendsto_logHalfStrip_im_atTop (a : ℝ) {c : ℝ} (hc : 0 < c) :
    Tendsto (fun q : ℂ => (logHalfStrip a c q).im) (𝓝[≠] 0) atTop := by
  simp only [logHalfStrip_im]
  exact (tendsto_const_mul_atTop_of_neg (neg_neg_of_pos hc)).mpr
    (Real.tendsto_log_nhdsGT_zero.comp tendsto_norm_nhdsNE_zero)

/-- The modulus limit of the actual uniformizing map at the ideal
half-strip vertex, with no finite boundary value assumed there. -/
theorem tendsto_norm_discHomeomorph_logHalfStrip
    {D : Set ℂ} (e : D ≃ₜ ball (0 : ℂ) 1) {f : ℂ → ℂ}
    (he : ∀ z : D, f z = (e z : ℂ)) (a : ℝ) {c : ℝ} (hc : 0 < c)
    (hmem : ∀ᶠ q in 𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ), logHalfStrip a c q ∈ D) :
    Tendsto (fun q => ‖f (logHalfStrip a c q)‖)
      (𝓝[{z : ℂ | 0 < z.im}] (0 : ℂ)) (𝓝 1) := by
  apply tendsto_norm_discHomeomorph_of_im_atTop e he _ hmem
  apply (tendsto_logHalfStrip_im_atTop a hc).mono_left
  apply nhdsWithin_mono
  intro z hz
  change 0 < z.im at hz
  change z ≠ 0
  intro heq
  rw [heq, zero_im] at hz
  exact (lt_irrefl 0) hz

end Wikipedia.HopfProblem.RiemannBoundary
