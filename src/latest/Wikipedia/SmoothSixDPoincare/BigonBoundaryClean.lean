import Wikipedia.SmoothSixDPoincare.BigonStripInterior
import Wikipedia.SmoothSixDPoincare.CornerStripData

/-!
# Clean sheet contact for the assembled bigon boundary neighborhood

The strict planar coordinate bounds rule out all three possible strip
contact loci: its center and its two endpoint axes. This gives avoidance of
both full sheets at every interior bigon point in either glued patch.
-/

open Set Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

theorem CleanStripPatch.avoids_sheets {S T : Set M} {a : ℝ → M}
    {k₀ k₁ : (ℝ × ℝ) → M} (k : CleanStripPatch (E := E) S T a k₀ k₁)
    {p : ℝ × ℝ} (hp : p ∈ k.domain) (ht : p.1 ∈ Ioo (0 : ℝ) 1) (hn : p.2 ≠ 0) :
    k.map p ∉ S ∪ T := by
  rintro (hS | hT)
  · exact hn ((k.first_sheet p hp).mp hS)
  · rcases (k.second_sheet p hp).mp hT with h0 | h1
    · exact ht.1.ne' h0
    · exact ht.2.ne h1

theorem bigon_boundary_map_avoids_sheets {h : ℝ} (hh : 0 < h)
    {S T : Set M} {a b : ℝ → M} {k₀ k₁ l₀ l₁ : (ℝ × ℝ) → M}
    (k : CleanStripPatch (E := E) S T a k₀ k₁)
    (l : CleanStripPatch (E := E) T S b l₀ l₁)
    {f : (ℝ × ℝ) → M} {U V : Set (ℝ × ℝ)}
    (hmapU : MapsTo (lowerStripCoordinates h) U k.domain)
    (hmapV : MapsTo (upperStripCoordinates h) V l.domain)
    (hflo : EqOn f (k.map ∘ lowerStripCoordinates h) U)
    (hfhi : EqOn f (l.map ∘ upperStripCoordinates h) V)
    {p : ℝ × ℝ} (hp : p ∈ U ∪ V) (hpi : p ∈ interior (bigon h)) : f p ∉ S ∪ T := by
  rcases hp with hpU | hpV
  · rw [hflo hpU]
    have hc := lowerStripCoordinates_interior hh hpi
    exact k.avoids_sheets (hmapU hpU) hc.1 hc.2.ne'
  · rw [hfhi hpV]
    have hc := upperStripCoordinates_interior hh hpi
    change l.map (upperStripCoordinates h p) ∉ S ∪ T
    rw [union_comm]
    exact l.avoids_sheets (hmapV hpV) hc.1 hc.2.ne'

end Wikipedia.SmoothSixDPoincare
