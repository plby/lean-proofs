import Mathlib.Geometry.Manifold.LocalDiffeomorph
import Mathlib.Geometry.Manifold.MFDeriv.FDeriv
import Mathlib.Topology.Separation.Hausdorff

/-!
# Replacing a scalar function in an actual partial smooth chart

The two coordinate functions agree outside a compact subset of the chart.
The replacement extends smoothly to the original manifold. Its entire germ
is unchanged off the compact support image, including the chart boundary.
The native critical-point criterion inside the chart is proved by the chain
rule and the surjective differential of the inverse chart.
-/

noncomputable section

open Set Filter
open scoped ContDiff Manifold Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.LocalFunctionReplacement

variable {E B H M : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B] [TopologicalSpace H]
  {I : ModelWithCorners ℝ B H}
  [TopologicalSpace M] [ChartedSpace H M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, E) I E M ∞)

def replace (f : M → ℝ) (b : E → ℝ) (y : M) : ℝ := by
  classical
  exact if y ∈ Φ.target then b (Φ.symm y) else f y

theorem replace_of_mem (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b y = b (Φ.symm y) := by simp [replace, hy]

theorem replace_of_notMem (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∉ Φ.target) :
    replace Φ f b y = f y := by simp [replace, hy]

theorem replace_chart (f : M → ℝ) (b : E → ℝ) {x : E} (hx : x ∈ Φ.source) :
    replace Φ f b (Φ x) = b x := by
  rw [replace_of_mem Φ f b (Φ.map_source' hx)]
  exact congrArg b (Φ.left_inv' hx)

theorem replace_germ_chart (f : M → ℝ) (b : E → ℝ) {y : M} (hy : y ∈ Φ.target) :
    replace Φ f b =ᶠ[𝓝 y] b ∘ Φ.symm := by
  filter_upwards [Φ.open_target.mem_nhds hy] with z hz
  exact replace_of_mem Φ f b hz

theorem replace_self {f : M → ℝ} {b : E → ℝ}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b x) : replace Φ f b = f := by
  funext y
  by_cases hy : y ∈ Φ.target
  · rw [replace_of_mem Φ f b hy]
    exact (hmodel (Φ.symm y) (Φ.map_target' hy)).symm.trans
      (congrArg f (Φ.right_inv' hy))
  · exact replace_of_notMem Φ f b hy

theorem replace_eq_off_support {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) :
    replace Φ f b₁ y = f y := by
  by_cases hyt : y ∈ Φ.target
  · have hx : Φ.symm y ∉ K := fun h => hy ⟨Φ.symm y, h, Φ.right_inv' hyt⟩
    rw [replace_of_mem Φ f b₁ hyt, hfix _ hx]
    exact (hmodel (Φ.symm y) (Φ.map_target' hyt)).symm.trans
      (congrArg f (Φ.right_inv' hyt))
  · exact replace_of_notMem Φ f b₁ hyt

variable [T2Space M]

theorem replace_germ_off_support {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) {y : M} (hy : y ∉ Φ '' K) :
    replace Φ f b₁ =ᶠ[𝓝 y] f := by
  have hc : IsClosed (Φ '' K) :=
    (hK.image_of_continuousOn (Φ.contMDiffOn_toFun.continuousOn.mono hKΦ)).isClosed
  filter_upwards [hc.isOpen_compl.mem_nhds hy] with z hz
  exact replace_eq_off_support Φ hmodel hfix hz

/-- Compact support makes the actual replacement smooth even across the chart boundary. -/
theorem contMDiff_replace {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hf : ContMDiff I 𝓘(ℝ, ℝ) ∞ f) (hb : ContDiff ℝ ∞ b₁)
    (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x) :
    ContMDiff I 𝓘(ℝ, ℝ) ∞ (replace Φ f b₁) := by
  intro y
  by_cases hy : y ∈ Φ.target
  · have hs := hb.contMDiff.contMDiffAt.comp y
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds hy))
    exact hs.congr_of_eventuallyEq (replace_germ_chart Φ f b₁ hy)
  · have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    exact hf.contMDiffAt.congr_of_eventuallyEq
      (replace_germ_off_support Φ hK hKΦ hmodel hfix hnot)

omit [T2Space M] in
/-- Critical points inside the chart are exactly the actual coordinate critical points. -/
theorem replace_critical_iff (f : M → ℝ) {b : E → ℝ} (hb : ContDiff ℝ ∞ b)
    {y : M} (hy : y ∈ Φ.target) :
    mfderiv I 𝓘(ℝ, ℝ) (replace Φ f b) y = 0 ↔ fderiv ℝ b (Φ.symm y) = 0 := by
  have hΦ : IsLocalDiffeomorphAt I 𝓘(ℝ, E) ∞ Φ.symm y :=
    ⟨Φ.symm, hy, fun _ _ => rfl⟩
  have hsurj := (hΦ.mfderivToContinuousLinearEquiv (by simp)).surjective
  rw [(replace_germ_chart Φ f b hy).mfderiv_eq,
    mfderiv_comp y (hb.contMDiff.mdifferentiableAt (by simp))
      (Φ.symm.mdifferentiableAt (by simp) hy), mfderiv_eq_fderiv]
  constructor
  · intro h
    apply ContinuousLinearMap.ext
    intro v
    obtain ⟨w, hw⟩ := hsurj v
    have he := congrArg (fun L : TangentSpace I y →L[ℝ] ℝ => L w) h
    change fderiv ℝ b (Φ.symm y) (mfderiv I 𝓘(ℝ, E) Φ.symm y w) = 0 at he
    change mfderiv I 𝓘(ℝ, E) Φ.symm y w = v at hw
    simpa only [hw, zero_apply] using he
  · intro h
    rw [h]
    rfl

/-- If the new coordinate function has no critical points, precisely the
critical points in this chart are removed; all exterior germs are retained. -/
theorem critical_points_after_replacement {f : M → ℝ} {b₀ b₁ : E → ℝ} {K : Set E}
    (hb : ContDiff ℝ ∞ b₁) (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hmodel : ∀ x ∈ Φ.source, f (Φ x) = b₀ x)
    (hfix : ∀ x ∉ K, b₁ x = b₀ x)
    (hregular : ∀ x ∈ Φ.source, fderiv ℝ b₁ x ≠ 0) (y : M) :
    mfderiv I 𝓘(ℝ, ℝ) (replace Φ f b₁) y = 0 ↔
      mfderiv I 𝓘(ℝ, ℝ) f y = 0 ∧ y ∉ Φ.target := by
  by_cases hy : y ∈ Φ.target
  · rw [replace_critical_iff Φ f hb hy]
    have hne : fderiv ℝ b₁ (Φ.symm y) ≠ 0 := hregular _ (Φ.map_target' hy)
    simp only [hne, hy, not_true_eq_false, and_false]
  · have hnot : y ∉ Φ '' K := by
      rintro ⟨x, hx, rfl⟩
      exact hy (Φ.map_source' (hKΦ hx))
    rw [(replace_germ_off_support Φ hK hKΦ hmodel hfix hnot).mfderiv_eq]
    simp only [hy, not_false_eq_true, and_true]
    rfl

end Wikipedia.HopfProblem.DegreeCollapse.LocalFunctionReplacement
