import Wikipedia.SmoothSixDPoincare.BigonNeighborhoodExtension
import Wikipedia.SmoothSixDPoincare.CompactRegionSmoothing

/-!
# A globally smooth extension preserving the entire local bigon boundary germ

The continuous extension is constant outside a compact set, and it is smooth
near the original frontier because it agrees there with the given map.
Compact-region relative smoothing then preserves a smaller closed boundary
neighborhood. Its interior gives full local equality along the entire frontier.
-/

noncomputable section

open Set Function Filter Topology ContinuousMap
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- A locally smooth bigon boundary map extends globally smoothly,
retaining its full boundary germ. -/
theorem exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies
    (hnull : ∀ f : C(Hemisphere.Sphere 1, M),
      ∃ c, f.Homotopic (ContinuousMap.const _ c))
    {h : ℝ} (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W)
    (hfrontW : frontier (bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ frontier (bigon h) ⊆ U ∧ U ⊆ W ∧ EqOn F f U := by
  obtain ⟨G, c, K, hK, hconst, V, hV, hfrontV, hVW, hGeq⟩ :=
    exists_bigon_neighborhood_extension_of_circle_nullhomotopies hnull hh hW hf.continuousOn hfrontW
  have hfrontCompact : IsCompact (frontier (bigon h)) :=
    (isCompact_bigon hh).of_isClosed_subset isClosed_frontier
      (fun p hp => ((mem_frontier_bigon_iff h p).mp hp).1)
  obtain ⟨C, _, hC, hfrontC, hCV⟩ := exists_compact_closed_between hfrontCompact hV hfrontV
  have hGV : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G V :=
    (hf.mono hVW).congr (fun _ hx => hGeq hx)
  have hGK : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ G Kᶜ :=
    (contMDiff_const (c := c)).contMDiffOn.congr (fun x hx => hconst x hx)
  obtain ⟨F, hF, hrel⟩ :=
    ManifoldSmoothing.exists_smooth_map_homotopicRel_of_smooth_off_compact G hK hC hV hCV hGV hGK
  refine ⟨F, hF, interior C, isOpen_interior, hfrontC,
    interior_subset.trans (hCV.trans hVW), ?_⟩
  intro x hx
  exact (hrel.fst_eq_snd (interior_subset hx)).symm.trans (hGeq (hCV (interior_subset hx)))

/-- The original homotopy equivalence supplies the required circle contractions. -/
theorem exists_smooth_bigon_neighborhood_extension (e : M ≃ₕ SixSphere)
    {h : ℝ} (hh : 0 < h) {f : (ℝ × ℝ) → M} {W : Set (ℝ × ℝ)}
    (hW : IsOpen W) (hf : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f W)
    (hfrontW : frontier (bigon h) ⊆ W) :
    ∃ F : C(ℝ × ℝ, M), ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ F ∧
      ∃ U : Set (ℝ × ℝ), IsOpen U ∧ frontier (bigon h) ⊆ U ∧ U ⊆ W ∧ EqOn F f U :=
  exists_smooth_bigon_neighborhood_extension_of_circle_nullhomotopies
    (fun f => sphereMap_nullhomotopic_of_homotopySixSphere e (by norm_num : 1 < 6) f)
    hh hW hf hfrontW

end Wikipedia.SmoothSixDPoincare
