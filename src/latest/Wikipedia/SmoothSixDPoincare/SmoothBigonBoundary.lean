import Wikipedia.SmoothSixDPoincare.BigonBoundaryCover
import Wikipedia.SmoothSixDPoincare.BigonStripCornerGerms
import Wikipedia.SmoothSixDPoincare.SmoothOpenGluing

/-!
# A constructed smooth map on an open neighborhood of the entire bigon boundary

The two native strips are glued using the actual planar edge coordinates.
The full boundary is covered, both prescribed arcs are retained with their
original time, and the glued map equals the appropriate strip on each open
patch. Embedding, clean interior contact, and the Whitney framing are not
asserted by this intermediate gluing theorem.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- Construct the smooth boundary-neighborhood map, preserving both actual edge parametrizations. -/
theorem exists_smooth_bigon_boundary_neighborhood {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    ∃ U : Set (ℝ × ℝ), ∃ V : Set (ℝ × ℝ), IsOpen U ∧ IsOpen V ∧
      frontier (bigon h) ⊆ U ∪ V ∧
      MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) U ∧
      MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) (Icc 0 1) V ∧
      MapsTo (lowerStripCoordinates h) U k.domain ∧
      MapsTo (upperStripCoordinates h) V l.domain ∧
      ∃ f : (ℝ × ℝ) → M, ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ f (U ∪ V) ∧
        EqOn f (k.map ∘ lowerStripCoordinates h) U ∧
        EqOn f (l.map ∘ upperStripCoordinates h) V ∧
        (∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, 0) = a t) ∧
        (∀ t ∈ Icc (0 : ℝ) 1, f (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) = b t) := by
  let Dlo := lowerStripCoordinates h ⁻¹' k.domain
  let Dhi := upperStripCoordinates h ⁻¹' l.domain
  have hDlo : IsOpen Dlo :=
    k.open_domain.preimage (contDiff_lowerStripCoordinates hh.ne').continuous
  have hDhi : IsOpen Dhi :=
    l.open_domain.preimage (contDiff_upperStripCoordinates hh.ne').continuous
  have hkl : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (k.map ∘ lowerStripCoordinates h) Dlo :=
    k.smooth.comp (contDiff_lowerStripCoordinates hh.ne').contMDiff.contMDiffOn (fun _ hp => hp)
  have hlu : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (l.map ∘ upperStripCoordinates h) Dhi :=
    l.smooth.comp (contDiff_upperStripCoordinates hh.ne').contMDiff.contMDiffOn (fun _ hp => hp)
  obtain ⟨O₀, hO₀sub, hO₀, hleft⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_left_germ hh.ne' c₀ c₁ k l)
  obtain ⟨O₁, hO₁sub, hO₁, hright⟩ :=
    mem_nhds_iff.mp (bigon_strip_maps_right_germ hh.ne' c₀ c₁ k l)
  have hlowD : MapsTo (fun t : ℝ => (2 * t - 1, 0)) (Icc 0 1) Dlo := by
    intro t ht
    change lowerStripCoordinates h (2 * t - 1, 0) ∈ k.domain
    rw [lowerStripCoordinates_lower]
    exact k.contains_strip ⟨ht, neg_nonpos.mpr k.width_pos.le, k.width_pos.le⟩
  have huppD : MapsTo (fun t : ℝ => (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)))
      (Icc 0 1) Dhi := by
    intro t ht
    change upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2)) ∈ l.domain
    rw [upperStripCoordinates_upper]
    exact l.contains_strip ⟨ht, neg_nonpos.mpr l.width_pos.le, l.width_pos.le⟩
  obtain ⟨U, V, hU, hV, hUD, hVD, hover, hlowU, huppV, hfront⟩ :=
    exists_bigon_boundary_cover hh hDlo hDhi (hO₀.union hO₁)
      (Or.inl hleft) (Or.inr hright) hlowD huppD
  have hfg : EqOn (k.map ∘ lowerStripCoordinates h) (l.map ∘ upperStripCoordinates h)
      (U ∩ V) := by
    intro p hp
    rcases hover hp with hp0 | hp1
    · exact hO₀sub hp0
    · exact hO₁sub hp1
  obtain ⟨f, hf, hflo, hfhi⟩ :=
    exists_smooth_open_gluing hU hV (hkl.mono hUD) (hlu.mono hVD) hfg
  refine ⟨U, V, hU, hV, hfront, hlowU, huppV, fun _ hp => hUD hp, fun _ hp => hVD hp,
    f, hf, hflo, hfhi, ?_, ?_⟩
  · intro t ht
    rw [hflo (hlowU ht)]
    change k.map (lowerStripCoordinates h (2 * t - 1, 0)) = a t
    rw [lowerStripCoordinates_lower]
    exact k.center t ht
  · intro t ht
    rw [hfhi (huppV ht)]
    change l.map (upperStripCoordinates h (2 * t - 1, h * (1 - (2 * t - 1) ^ 2))) = b t
    rw [upperStripCoordinates_upper]
    exact l.center t ht

end Wikipedia.SmoothSixDPoincare
