import Wikipedia.SmoothSixDPoincare.BigonStripCoordinates
import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# The native edge parametrizations agree on whole corner neighborhoods

Pulling the two native strips back by the actual planar edge coordinates
gives equal maps near each bigon endpoint. This is equality of full planar
germs, not just equality along the boundary arcs or equality of derivatives.
-/

noncomputable section

open Set Function Filter Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The actual lower and upper strip maps coincide near the left bigon endpoint. -/
theorem bigon_strip_maps_left_germ {h : ℝ} (hh : h ≠ 0)
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ lowerStripCoordinates h =ᶠ[𝓝 (-1, 0)] l.map ∘ upperStripCoordinates h := by
  have hx : lowerStripCoordinates h (-1, 0) = (0, 0) := by
    convert lowerStripCoordinates_lower h 0 using 1
    norm_num
  have hy : upperStripCoordinates h (-1, 0) = (0, 0) := by
    convert upperStripCoordinates_upper h 0 using 1
    norm_num
  have hk := k.left_germ.comp_tendsto
    (show Tendsto (lowerStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0)) by
      rw [← hx]
      exact (contDiff_lowerStripCoordinates hh).continuous.continuousAt)
  have hl := l.left_germ.comp_tendsto
    (show Tendsto (upperStripCoordinates h) (𝓝 (-1, 0)) (𝓝 (0, 0)) by
      rw [← hy]
      exact (contDiff_upperStripCoordinates hh).continuous.continuousAt)
  have hnear : ∀ᶠ p in 𝓝 ((-1 : ℝ), (0 : ℝ)), arcTime p ≤ 1 / 3 := by
    have ht : arcTime (-1, 0) < 1 / 3 := by norm_num [arcTime]
    exact ((contDiff_arcTime.continuous.continuousAt).eventually_lt_const ht).mono
      (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change k.map (lowerStripCoordinates h p) = l.map (upperStripCoordinates h p)
  rw [hkp, hlp, lowerStripCoordinates_left h hp, upperStripCoordinates_left hh hp]
  change c₀.map (leftCornerCoordinates h p) = c₀.map ((leftCornerCoordinates h p).swap.swap)
  rw [Prod.swap_swap]

/-- The same full-map compatibility holds at the right endpoint with reversed strip time. -/
theorem bigon_strip_maps_right_germ {h : ℝ} (hh : h ≠ 0)
    {S T : Set M} {a b a₀ b₀ a₁ b₁ : ℝ → M}
    (c₀ : CleanCornerPatch (E := E) S T a₀ b₀)
    (c₁ : CleanCornerPatch (E := E) S T a₁ b₁)
    (k : CleanStripPatch (E := E) S T a c₀.map c₁.map)
    (l : CleanStripPatch (E := E) T S b c₀.swap.map c₁.swap.map) :
    k.map ∘ lowerStripCoordinates h =ᶠ[𝓝 (1, 0)] l.map ∘ upperStripCoordinates h := by
  have hx : lowerStripCoordinates h (1, 0) = (1, 0) := by
    convert lowerStripCoordinates_lower h 1 using 1
    norm_num
  have hy : upperStripCoordinates h (1, 0) = (1, 0) := by
    convert upperStripCoordinates_upper h 1 using 1
    norm_num
  have hk := k.right_germ.comp_tendsto
    (show Tendsto (lowerStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0)) by
      have ht := (contDiff_lowerStripCoordinates hh).continuous.continuousAt (x := (1, 0))
      rw [ContinuousAt, hx] at ht
      exact ht)
  have hl := l.right_germ.comp_tendsto
    (show Tendsto (upperStripCoordinates h) (𝓝 (1, 0)) (𝓝 (1, 0)) by
      have ht := (contDiff_upperStripCoordinates hh).continuous.continuousAt (x := (1, 0))
      rw [ContinuousAt, hy] at ht
      exact ht)
  have hnear : ∀ᶠ p in 𝓝 ((1 : ℝ), (0 : ℝ)), 2 / 3 ≤ arcTime p := by
    have ht : 2 / 3 < arcTime (1, 0) := by norm_num [arcTime]
    exact ((contDiff_arcTime.continuous.continuousAt).eventually_const_lt ht).mono
      (fun _ hp => hp.le)
  filter_upwards [hk, hl, hnear] with p hkp hlp hp
  dsimp only [Function.comp_apply] at hkp hlp
  change k.map (lowerStripCoordinates h p) = l.map (upperStripCoordinates h p)
  rw [hkp, hlp]
  change c₁.map (StripCoordinates.reverse (lowerStripCoordinates h p)) =
    c₁.map ((StripCoordinates.reverse (upperStripCoordinates h p)).swap)
  rw [lowerStripCoordinates_right h hp, upperStripCoordinates_right hh hp, Prod.swap_swap]

end Wikipedia.SmoothSixDPoincare
