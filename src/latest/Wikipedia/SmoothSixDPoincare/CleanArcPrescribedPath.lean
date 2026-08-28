import Wikipedia.SmoothSixDPoincare.SmoothCurvePathClass
import Wikipedia.SmoothSixDPoincare.CleanArcHomotopy

/-!
# Clean connecting arcs in the prescribed input path class

Construct the smooth endpoint-germ curve in the original path class, then
embed it and avoid the two original obstacles without changing that class.
The two obstacle dimensions may differ. All endpoint comparisons are explicit.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open CurveImmersion

variable {G V₁ V₂ H H₁ H₂ N Y₁ Y₂ : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [NormedAddCommGroup V₁] [NormedSpace ℝ V₁] [FiniteDimensional ℝ V₁]
  [NormedAddCommGroup V₂] [NormedSpace ℝ V₂] [FiniteDimensional ℝ V₂]
  [TopologicalSpace H] [TopologicalSpace H₁] [TopologicalSpace H₂]
  {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  {I₁ : ModelWithCorners ℝ V₁ H₁} {I₂ : ModelWithCorners ℝ V₂ H₂}
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]
  [TopologicalSpace Y₁] [ChartedSpace H₁ Y₁] [IsManifold I₁ ∞ Y₁]
  [CompactSpace Y₁] [SecondCountableTopology Y₁]
  [TopologicalSpace Y₂] [ChartedSpace H₂ Y₂] [IsManifold I₂ ∞ Y₂]
  [SecondCountableTopology Y₂]

theorem exists_clean_arc_two_images_in_path_class {a b : ℝ → N} {U W : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b W)
    (hU : IsOpen U) (hW : IsOpen W) (h0U : (0 : ℝ) ∈ U) (h1W : (1 : ℝ) ∈ W)
    (hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1) (hdim : 3 ≤ Module.finrank ℝ G)
    (o₁ : C(Y₁, N)) (ho₁ : ContMDiff I₁ J ∞ o₁)
    (o₂ : C(Y₂, N)) (ho₂ : ContMDiff I₂ J ∞ o₂) (hc₂ : IsClosed (range o₂))
    (hd₁ : 1 + Module.finrank ℝ V₁ < Module.finrank ℝ G)
    (hd₂ : 1 + Module.finrank ℝ V₂ < Module.finrank ℝ G)
    (ha₁ : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ range o₁ → t = 0)
    (hb₁ : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ range o₁ → t = 1)
    (ha₂ : ∀ᶠ t in 𝓝 (0 : ℝ), a t ∈ range o₂ → t = 0)
    (hb₂ : ∀ᶠ t in 𝓝 (1 : ℝ), b t ∈ range o₂ → t = 1) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
      IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ range o₁ ∧ f t ∉ range o₂) ∧
      ∃ (h0 : f 0 = a 0) (h1 : f 1 = b 1),
        ((intervalPath f).cast h0.symm h1.symm).Homotopic γ := by
  obtain ⟨f, hf, hfa, hfb, hf0, hf1, hclass⟩ :=
    exists_smooth_curve_with_local_endpoint_germs_pathClass ha hb hU hW h0U h1W γ
  have hfxy : f 0 ≠ f 1 := by rw [hf0, hf1]; exact hxy
  have hfi0 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 0) := by rw [hfa.mfderiv_eq]; exact hia
  have hfi1 : Injective (mfderiv 𝓘(ℝ, ℝ) J f 1) := by rw [hfb.mfderiv_eq]; exact hib
  have hf₁0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o₁ → t = 0 := by
    filter_upwards [hfa, ha₁] with t ht hc
    rw [ht]
    exact hc
  have hf₁1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o₁ → t = 1 := by
    filter_upwards [hfb, hb₁] with t ht hc
    rw [ht]
    exact hc
  have hf₂0 : ∀ᶠ t in 𝓝 (0 : ℝ), f t ∈ range o₂ → t = 0 := by
    filter_upwards [hfa, ha₂] with t ht hc
    rw [ht]
    exact hc
  have hf₂1 : ∀ᶠ t in 𝓝 (1 : ℝ), f t ∈ range o₂ → t = 1 := by
    filter_upwards [hfb, hb₂] with t ht hc
    rw [ht]
    exact hc
  obtain ⟨g, hg, hgf0, hgf1, hge, hgi, hfg, havoid⟩ :=
    ManifoldImmersion.exists_clean_arc_two_images_homotopicRel f hf hfxy hfi0 hfi1
      o₁ ho₁ o₂ ho₂ hc₂ hdim hd₁ hd₂ hf₁0 hf₁1 hf₂0 hf₂1
  have hh := (intervalPath_homotopic hfg).pathCast hf0.symm hf1.symm
  exact ⟨g, hg, hgf0.trans hfa, hgf1.trans hfb, hge, hgi, havoid,
    hgf0.eq_of_nhds.trans hf0, hgf1.eq_of_nhds.trans hf1, hh.symm.trans hclass⟩

end Wikipedia.SmoothSixDPoincare
