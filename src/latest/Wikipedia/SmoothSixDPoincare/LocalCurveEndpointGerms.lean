import Wikipedia.SmoothSixDPoincare.EmbeddedArcEndpointGerms
import Wikipedia.SmoothSixDPoincare.StarConvexSmoothExtension

/-!
# Embedded arcs with locally defined endpoint germs

The endpoint arcs only need to be smooth on their actual open domains.
Translate each endpoint to zero, extend locally without changing its germ,
and apply the relative embedded-arc construction. The native derivatives and
all endpoint values remain those of the original local parametrizations.
-/

noncomputable section

open Set Function Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare

section Extension

variable {G H N : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H}
  [TopologicalSpace N] [ChartedSpace H N]

/-- Extend a locally smooth real curve globally without changing its germ at the given point. -/
theorem exists_smooth_curve_with_germ_at {a : ℝ → N} {U : Set ℝ} {t₀ : ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hU : IsOpen U) (ht₀ : t₀ ∈ U) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧ (f =ᶠ[𝓝 t₀] a) := by
  obtain ⟨f, hf, heq⟩ := exists_smooth_extension_near_point ha hU ht₀
  exact ⟨⟨f, hf.continuous⟩, hf, heq⟩

end Extension

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- An embedded connecting arc can retain actual locally smooth endpoint parametrizations. -/
theorem exists_embedded_arc_with_local_endpoint_germs {a b : ℝ → N} {U V : Set ℝ}
    (ha : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ a U) (hb : ContMDiffOn 𝓘(ℝ, ℝ) J ∞ b V)
    (hU : IsOpen U) (hV : IsOpen V) (h0U : (0 : ℝ) ∈ U) (h1V : (1 : ℝ) ∈ V)
    (hia : Injective (mfderiv 𝓘(ℝ, ℝ) J a 0))
    (hib : Injective (mfderiv 𝓘(ℝ, ℝ) J b 1))
    (γ : Path (a 0) (b 1)) (hxy : a 0 ≠ b 1) (hdim : 3 ≤ Module.finrank ℝ G)
    {S : Set N} (hS : S.Finite) :
    ∃ f : C(ℝ, N), ContMDiff 𝓘(ℝ, ℝ) J ∞ f ∧
      (f =ᶠ[𝓝 (0 : ℝ)] a) ∧ (f =ᶠ[𝓝 (1 : ℝ)] b) ∧
      Topology.IsClosedEmbedding (fun t : unitInterval => f t) ∧
      (∀ t ∈ Icc (0 : ℝ) 1, Injective (mfderiv 𝓘(ℝ, ℝ) J f t)) ∧
      (∀ t ∈ Ioo (0 : ℝ) 1, f t ∉ S) := by
  obtain ⟨a', ha', heqa⟩ := exists_smooth_curve_with_germ_at ha hU h0U
  obtain ⟨b', hb', heqb⟩ := exists_smooth_curve_with_germ_at hb hV h1V
  have hia' : Injective (mfderiv 𝓘(ℝ, ℝ) J a' 0) := by
    rw [heqa.mfderiv_eq]
    exact hia
  have hib' : Injective (mfderiv 𝓘(ℝ, ℝ) J b' 1) := by
    rw [heqb.mfderiv_eq]
    exact hib
  have hxy' : a' 0 ≠ b' 1 := by
    rw [heqa.eq_of_nhds, heqb.eq_of_nhds]
    exact hxy
  obtain ⟨f, hf, hfa, hfb, hemb, hi, havoid⟩ :=
    exists_embedded_arc_with_endpoint_germs a' b' ha' hb' hia' hib'
      (γ.cast heqa.eq_of_nhds heqb.eq_of_nhds) hxy' hdim hS
  exact ⟨f, hf, hfa.trans heqa, hfb.trans heqb, hemb, hi, havoid⟩

end Wikipedia.SmoothSixDPoincare
