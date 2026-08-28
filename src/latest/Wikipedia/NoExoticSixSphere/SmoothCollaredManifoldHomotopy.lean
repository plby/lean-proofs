import Wikipedia.NoExoticSixSphere.SmoothTubularRetraction
import Wikipedia.NoExoticSixSphere.CylinderTime
import Wikipedia.NoExoticSixSphere.RelativeSphereNormalization
import Mathlib.Topology.MetricSpace.Thickening

/-!
# A continuous manifold homotopy has a smooth representative with exact end collars

Use the original Euclidean embedding and its actual tubular retraction.
Relative ambient approximation stays inside the tubular domain by a uniform
neighborhood of the compact embedded manifold. The protected end collars
retain the original smooth endpoint maps exactly.
-/

noncomputable section

open Set Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin 6)) M]
  [CompactSpace M]
  (e : EuclideanEmbedding 6 M) (r : TubularRetraction e)

include e r

theorem exists_smoothCollaredHomotopy (f₀ f₁ : C(Sphere 3, M))
    (h₀ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₀) (h₁ : ContMDiff (𝓡 3) (𝓡 6) ∞ f₁)
    (H : f₀.Homotopy f₁) :
    ∃ G : C(ℝ × Sphere 3, M), ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ G ∧
      (∀ t : ℝ, t ≤ 1 / 4 → ∀ s, G (t, s) = f₀ s) ∧
      (∀ t : ℝ, 3 / 4 ≤ t → ∀ s, G (t, s) = f₁ s) := by
  let F := CylinderTime.realCollaredMap H.toContinuousMap
  let S : Set (ℝ × Sphere 3) := {p | p.1 ≤ 1 / 4 ∨ 3 / 4 ≤ p.1}
  let U : Set (ℝ × Sphere 3) := {p | p.1 < 1 / 3 ∨ 2 / 3 < p.1}
  have hleft (p : ℝ × Sphere 3) (hp : p.1 ≤ 1 / 3) : F p = f₀ p.2 := by
    change H (CylinderTime.collar p.1, p.2) = f₀ p.2
    rw [CylinderTime.collar_left hp]
    exact H.apply_zero p.2
  have hright (p : ℝ × Sphere 3) (hp : 2 / 3 ≤ p.1) : F p = f₁ p.2 := by
    change H (CylinderTime.collar p.1, p.2) = f₁ p.2
    rw [CylinderTime.collar_right hp]
    exact H.apply_one p.2
  have hS : IsClosed S := (isClosed_le continuous_fst continuous_const).union
    (isClosed_le continuous_const continuous_fst)
  have hU : IsOpen U := (isOpen_lt continuous_fst continuous_const).union
    (isOpen_lt continuous_const continuous_fst)
  have hSU : S ⊆ U := by
    intro p hp
    rcases hp with hp | hp
    · exact Or.inl (by linarith)
    · exact Or.inr (by linarith)
  have hFU : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ F U := by
    intro p hp
    rcases hp with hp | hp
    · have heq : (F : ℝ × Sphere 3 → M) =ᶠ[𝓝 p] fun q ↦ f₀ q.2 := by
        filter_upwards [(isOpen_lt continuous_fst continuous_const).mem_nhds hp] with q hq
        exact hleft q hq.le
      exact ((h₀.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
    · have heq : (F : ℝ × Sphere 3 → M) =ᶠ[𝓝 p] fun q ↦ f₁ q.2 := by
        filter_upwards [(isOpen_lt continuous_const continuous_fst).mem_nhds hp] with q hq
        exact hright q hq.le
      exact ((h₁.comp contMDiff_snd).contMDiffAt.congr_of_eventuallyEq heq).contMDiffWithinAt
  have hcompact : IsCompact (range e.toFun) := isCompact_range e.smooth.continuous
  obtain ⟨δ, hδ, hδU⟩ := hcompact.exists_thickening_subset_open r.domain.isOpen r.contains
  have hc : Continuous (e.toFun ∘ F) := e.smooth.continuous.comp F.continuous
  have hs : ContMDiffOn ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 e.ambientDimension) ∞ (e.toFun ∘ F) U :=
    e.smooth.comp_contMDiffOn hFU
  obtain ⟨A, hAclose, hAeq, _⟩ := hc.exists_contMDiff_approx_and_eqOn
    ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (⊤ : ℕ∞) continuous_const (fun _ ↦ hδ)
    hS (hU.mem_nhdsSet.mpr hSU) hs
  have hAdomain (p : ℝ × Sphere 3) : A p ∈ r.domain := by
    apply hδU
    exact mem_thickening_iff.mpr ⟨e.toFun (F p), ⟨F p, rfl⟩, hAclose p⟩
  have hG : ContMDiff ((𝓘(ℝ, ℝ)).prod (𝓡 3)) (𝓡 6) ∞ (r.toFun ∘ A) := by
    intro p
    exact (r.smooth.contMDiffAt (r.domain.isOpen.mem_nhds (hAdomain p))).comp p
      A.contMDiff.contMDiffAt
  let G : C(ℝ × Sphere 3, M) := ⟨r.toFun ∘ A, hG.continuous⟩
  refine ⟨G, hG, ?_, ?_⟩
  · intro t ht s
    change r.toFun (A (t, s)) = f₀ s
    rw [hAeq (show (t, s) ∈ S from Or.inl ht), Function.comp_apply, r.fixes]
    exact hleft (t, s) (by change t ≤ 1 / 3; linarith)
  · intro t ht s
    change r.toFun (A (t, s)) = f₁ s
    rw [hAeq (show (t, s) ∈ S from Or.inr ht), Function.comp_apply, r.fixes]
    exact hright (t, s) (by change 2 / 3 ≤ t; linarith)

end NoExoticSixSphere.EuclideanEmbedding
