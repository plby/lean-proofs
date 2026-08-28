import Wikipedia.SmoothSixDPoincare.HeightStretch
import Wikipedia.SmoothSixDPoincare.RegularBandHeight

/-!
# Homeomorphisms of closed sublevels through regular bands

Stretch the height above a lower regular level, fixing all points below
it. Exact height translation by the constructed flow proves the inverse
laws. This gives an actual homeomorphism, not just a homotopy equivalence.
-/

noncomputable section

open Set Manifold
open scoped ContDiff Topology

namespace Wikipedia.SmoothSixDPoincare.FlowConstruction

section Topological

variable {X : Type*} [TopologicalSpace X] (F : Flow ℝ X) (f : X → ℝ)

def stretchFlow (c k : ℝ) (x : X) : X := F (stretchHeight c k (f x) - f x) x

theorem continuous_stretchFlow (hf : Continuous f) (c k : ℝ) :
    Continuous (stretchFlow F f c k) :=
  F.continuous (((continuous_stretchHeight c k).comp hf).sub hf) continuous_id

variable {f} {c d a b : ℝ}
  (hF : ∀ x t, f x ∈ Icc c d → f x + t ∈ Icc c d → f (F t x) = f x + t)

include hF

/-- The height reparametrization is realized exactly by the native time-varying flow map. -/
theorem stretchFlow_height (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) =
      stretchHeight c ((b - c) / (a - c)) (f x) := by
  by_cases hxc : f x ≤ c
  · simp only [stretchFlow, stretchHeight_of_le hxc, sub_self, F.map_zero_apply]
  · have hcx : c ≤ f x := le_of_not_ge hxc
    have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
    have hslo : c ≤ stretchHeight c ((b - c) / (a - c)) (f x) := by
      rw [stretchHeight_of_ge hcx]
      exact le_add_of_nonneg_right (mul_nonneg hk.le (sub_nonneg.mpr hcx))
    have hshi := stretchHeight_le_target hca hcb hx
    have hsum : f x + (stretchHeight c ((b - c) / (a - c)) (f x) - f x) =
        stretchHeight c ((b - c) / (a - c)) (f x) := by ring
    have hh := hF x (stretchHeight c ((b - c) / (a - c)) (f x) - f x)
      ⟨hcx, hx.trans ha⟩ (by rw [hsum]; exact ⟨hslo, hshi.trans hb⟩)
    exact hh.trans hsum

/-- The stretched trajectory lands in the desired new sublevel. -/
theorem stretchFlow_le_target (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    {x : X} (hx : f x ≤ a) :
    f (stretchFlow F f c ((b - c) / (a - c)) x) ≤ b := by
  rw [stretchFlow_height F hF hca hcb ha hb hx]
  exact stretchHeight_le_target hca hcb hx

/-- Reciprocal height stretching gives the inverse trajectory map. -/
theorem stretchFlow_inverse (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    {x : X} (hx : f x ≤ a) :
    stretchFlow F f c ((a - c) / (b - c))
      (stretchFlow F f c ((b - c) / (a - c)) x) = x := by
  have hh := stretchFlow_height F hF hca hcb ha hb hx
  have hk : 0 < (b - c) / (a - c) := div_pos (sub_pos.mpr hcb) (sub_pos.mpr hca)
  have hi : (a - c) / (b - c) = ((b - c) / (a - c))⁻¹ := (inv_div _ _).symm
  change F (stretchHeight c ((a - c) / (b - c))
      (f (stretchFlow F f c ((b - c) / (a - c)) x)) -
        f (stretchFlow F f c ((b - c) / (a - c)) x))
    (F (stretchHeight c ((b - c) / (a - c)) (f x) - f x) x) = x
  rw [hh, hi, stretchHeight_inverse hk, ← F.map_add]
  rw [show f x - stretchHeight c ((b - c) / (a - c)) (f x) +
      (stretchHeight c ((b - c) / (a - c)) (f x) - f x) = 0 by ring, F.map_zero_apply]

/-- A height-translating flow yields a homeomorphism of the two closed sublevels. -/
def regularSublevelHomeomorphOfFlow (hf : Continuous f)
    (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d) :
    {x : X // f x ≤ a} ≃ₜ {x : X // f x ≤ b} where
  toFun x := ⟨stretchFlow F f c ((b - c) / (a - c)) x.1,
    stretchFlow_le_target F hF hca hcb ha hb x.2⟩
  invFun x := ⟨stretchFlow F f c ((a - c) / (b - c)) x.1,
    stretchFlow_le_target F hF hcb hca hb ha x.2⟩
  left_inv x := Subtype.ext (stretchFlow_inverse F hF hca hcb ha hb x.2)
  right_inv x := Subtype.ext (stretchFlow_inverse F hF hcb hca hb ha x.2)
  continuous_toFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _
  continuous_invFun :=
    ((continuous_stretchFlow F f hf c _).comp continuous_subtype_val).subtype_mk _

/-- The regular-sublevel homeomorphism carries exactly the old top level to the new top level. -/
theorem regularSublevelHomeomorphOfFlow_level_iff (hf : Continuous f)
    (hca : c < a) (hcb : c < b) (ha : a ≤ d) (hb : b ≤ d)
    (x : {x : X // f x ≤ a}) :
    f ((regularSublevelHomeomorphOfFlow F hF hf hca hcb ha hb) x).1 = b ↔ f x.1 = a := by
  change f (stretchFlow F f c ((b - c) / (a - c)) x.1) = b ↔ _
  rw [stretchFlow_height F hF hca hcb ha hb x.2]
  exact stretchHeight_endpoint_iff hca hcb

end Topological

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- Closed sublevels are homeomorphic if a slightly larger band has no critical points. -/
theorem nonempty_regularSublevelHomeomorph {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Icc c (max a b) → x ∉ ManifoldMorse.criticalPoints E f) :
    Nonempty ({x : M // f x ≤ a} ≃ₜ {x : M // f x ≤ b}) := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  exact ⟨regularSublevelHomeomorphOfFlow F hF hf.continuous hca hcb
    (le_max_left a b) (le_max_right a b)⟩

/-- Construct the regular-sublevel homeomorphism with its exact boundary-level correspondence. -/
theorem exists_regularSublevelHomeomorph_with_level {f : M → ℝ}
    (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f) {c a b : ℝ} (hca : c < a) (hcb : c < b)
    (hband : ∀ x, f x ∈ Icc c (max a b) → x ∉ ManifoldMorse.criticalPoints E f) :
    ∃ e : {x : M // f x ≤ a} ≃ₜ {x : M // f x ≤ b},
      ∀ x, f (e x).1 = b ↔ f x.1 = a := by
  obtain ⟨F, hF⟩ := exists_heightTranslatingFlow hf hband
  refine ⟨regularSublevelHomeomorphOfFlow F hF hf.continuous hca hcb
    (le_max_left a b) (le_max_right a b), ?_⟩
  exact regularSublevelHomeomorphOfFlow_level_iff F hF hf.continuous hca hcb
    (le_max_left a b) (le_max_right a b)

end Wikipedia.SmoothSixDPoincare.FlowConstruction
