import Wikipedia.NoExoticSixSphere.SphereSumNeckInChart
import Wikipedia.SmoothSixDPoincare.CleanTransverseSheetChart

/-!
# A clean neck constructed at an actual transverse sheet crossing

The native derivative transversality produces a simultaneous sheet chart.
Inside any prescribed neighborhood, the resulting smooth immersive cylinder
joins the actual sheets with exact radial end collars. The open middle is
disjoint from both entire input patch images. Compact subcylinders are
embedded in the original manifold, with its original atlas.

This is a local construction. It does not assert a glued sphere sum or a
comparison of its double-point count and frame obstruction.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_neck_at_transverse_sheets {f g : Vector 3 → M}
    {U V : Set (Vector 3)} (hU : IsOpen U) (hV : IsOpen V)
    (h0U : (0 : Vector 3) ∈ U) (h0V : (0 : Vector 3) ∈ V)
    (hf : ContMDiffOn (𝓡 3) (𝓡 6) ∞ f U)
    (hg : ContMDiffOn (𝓡 3) (𝓡 6) ∞ g V) (hzero : g 0 = f 0)
    (hembf : IsEmbedding (fun x : U ↦ f x))
    (hembg : IsEmbedding (fun x : V ↦ g x))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) f 0).coprod
      (mfderiv (𝓡 3) (𝓡 6) g 0)))
    {O : Set M} (hO : IsOpen O) (h0O : f 0 ∈ O) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K : Parameter → M,
      ContMDiff Model (𝓡 6) ∞ K ∧ Injective K ∧
      (∀ q, Injective (mfderiv Model (𝓡 6) K q)) ∧
      range K ⊆ O ∧
      (∀ t s, 1 ≤ t → K (t, s) = f ((ε * profile t) • s.val)) ∧
      (∀ t s, t ≤ -1 → K (t, s) = g ((ε * profile (-t)) • s.val)) ∧
      (∀ q, (K q ∈ f '' U ↔ 1 ≤ q.1) ∧ (K q ∈ g '' V ↔ q.1 ≤ -1)) ∧
      (∀ q, q.1 ∈ Ioo (-1 : ℝ) 1 → K q ∉ f '' U ∪ g '' V) ∧
      (∀ u v : ℝ,
        IsClosedEmbedding (fun q : Icc u v × Sphere 2 ↦ K (q.1.val, q.2))) := by
  have hdim : Module.finrank ℝ (Vector 3) + Module.finrank ℝ (Vector 3) =
      Module.finrank ℝ (Vector 6) := by simp
  obtain ⟨ε, hε, Φ, hprod, _, htarget, hleft, hright, hclean⟩ :=
    Wikipedia.SmoothSixDPoincare.exists_clean_simultaneous_sheetChart
      hU hV h0U h0V hf hg hzero hembf hembg hdim ht hO h0O
  refine ⟨ε, hε, chartNeck Φ ε, contMDiff_chartNeck Φ hε hprod,
    chartNeck_injective Φ hε hprod, injective_mfderiv_chartNeck Φ hε hprod,
    ?_, ?_, ?_, ?_, ?_, chartNeck_closedCylinder_embedded Φ hε hprod⟩
  · rintro _ ⟨q, rfl⟩
    exact htarget (chartNeck_mem_target Φ hε hprod q)
  · exact chartNeck_right_collar Φ hε hprod hleft
  · exact chartNeck_left_collar Φ hε hprod hright
  · exact chartNeck_mem_sheet_iff Φ hε hprod hclean
  · intro q hq hbad
    have hs := chartNeck_mem_sheet_iff Φ hε hprod hclean q
    rcases hbad with hf | hg
    · exact (not_le_of_gt hq.2) (hs.1.mp hf)
    · exact (not_le_of_gt hq.1) (hs.2.mp hg)

end NoExoticSixSphere.SphereSumNeck
