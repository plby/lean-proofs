import Wikipedia.HopfProblem.DegreeCollapseCompactIsotopySuspension
import Wikipedia.HopfProblem.DegreeCollapseNativeVerticalReplacement
import Wikipedia.SmoothSixDPoincare.PartialChartIntegralCurve

/-!
# Inserting a compact suspension field in a native height chart

The actual chart height computes the native directional derivative.
Compact replacement retains the zero set and all exterior field germs,
while a model field of vertical speed one retains height speed minus one.
-/

noncomputable section

open Set Function Filter Manifold
open scoped Topology ContDiff
open Wikipedia.SmoothSixDPoincare

namespace Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension

variable {E B M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup B] [NormedSpace ℝ B]
  [TopologicalSpace M] [ChartedSpace B M]

theorem mvfderiv_native_height_field
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (W : (E × ℝ) → E × ℝ) {x : M} (hx : x ∈ Φ.target) :
    mvfderiv 𝓘(ℝ, B) f x (FlowConstruction.partialChartField Φ.symm W x) =
      -(W (Φ.symm x)).2 := by
  let q := Φ.symm x
  have hq : q ∈ Φ.source := Φ.map_target' hx
  have heq : (f ∘ Φ) =ᶠ[𝓝 q] (fun p : E × ℝ => b - p.2) := by
    filter_upwards [Φ.open_source.mem_nhds hq] with p hp
    exact hheight p hp
  have hd : fderiv ℝ (f ∘ Φ) q = fderiv ℝ (fun p : E × ℝ => b - p.2) q :=
    heq.fderiv_eq
  rw [FlowConstruction.mvfderiv_partialChartField hf Φ.symm W hx]
  change fderiv ℝ (f ∘ Φ) q (W q) = -(W q).2
  rw [hd]
  have hh := (hasFDerivAt_const (𝕜 := ℝ) b q).sub
    (ContinuousLinearMap.snd ℝ E ℝ).hasFDerivAt
  have hh' : fderiv ℝ (fun p : E × ℝ => b - p.2) q =
      (0 : (E × ℝ) →L[ℝ] ℝ) - ContinuousLinearMap.snd ℝ E ℝ := hh.fderiv
  rw [hh']
  simp

variable [FiniteDimensional ℝ B] [IsManifold 𝓘(ℝ, B) ∞ M] [T2Space M]

theorem exists_native_suspension_field
    (Φ : PartialDiffeomorph 𝓘(ℝ, E × ℝ) 𝓘(ℝ, B) (E × ℝ) M ∞)
    {f : M → ℝ} (hf : ContMDiff 𝓘(ℝ, B) 𝓘(ℝ, ℝ) ∞ f) {b : ℝ}
    (hheight : ∀ p ∈ Φ.source, f (Φ p) = b - p.2)
    (V : (x : M) → TangentSpace 𝓘(ℝ, B) x)
    (hV : ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
      (fun x => (⟨x, V x⟩ : TangentBundle 𝓘(ℝ, B) M)))
    (hmodel : ∀ x ∈ Φ.target, V x =
      FlowConstruction.partialChartField Φ.symm (fun _ : E × ℝ => (0, 1)) x)
    {W : (E × ℝ) → E × ℝ} (hW : ContDiff ℝ ∞ W) (hWheight : ∀ p, (W p).2 = 1)
    {K : Set (E × ℝ)} (hK : IsCompact K) (hKΦ : K ⊆ Φ.source)
    (hfix : ∀ p ∉ K, W p = (0, 1)) :
    ∃ V' : (x : M) → TangentSpace 𝓘(ℝ, B) x,
      ContMDiff 𝓘(ℝ, B) (𝓘(ℝ, B).tangent) ∞
        (fun x => (⟨x, V' x⟩ : TangentBundle 𝓘(ℝ, B) M)) ∧
      (∀ x ∈ Φ.target, V' x = FlowConstruction.partialChartField Φ.symm W x) ∧
      (∀ x ∈ Φ.target, mvfderiv 𝓘(ℝ, B) f x (V' x) = -1) ∧
      (∀ x, V' x = 0 ↔ V x = 0) ∧
      ∀ x ∉ Φ '' K, ∀ᶠ y in 𝓝 x, V' y = V y := by
  obtain ⟨V', hV', hnew, hzero, hgerm⟩ :=
    exists_native_vertical_field_replacement Φ V hV hmodel hW hWheight hK hKΦ hfix
  refine ⟨V', hV', hnew, ?_, hzero, hgerm⟩
  intro x hx
  rw [hnew x hx, mvfderiv_native_height_field Φ hf hheight W hx, hWheight]

end Wikipedia.HopfProblem.DegreeCollapse.FlowSuspension
