import Mathlib.Analysis.Convex.SpecificFunctions.Deriv
import Mathlib.Tactic.Linarith

namespace Puzzling139335.GlideCrossing

/-- A nonnegative linear combination of sine and cosine is concave on the
first quadrant. -/
theorem concaveOn_sin_cos_quarter {A B : ℝ} (hA : 0 ≤ A) (hB : 0 ≤ B) :
    ConcaveOn ℝ (Set.Icc 0 (Real.pi / 2))
      (fun x => A * Real.sin x + B * Real.cos x) := by
  have hs : ConcaveOn ℝ (Set.Icc 0 (Real.pi / 2)) Real.sin :=
    strictConcaveOn_sin_Icc.concaveOn.subset
      (by intro x hx; exact ⟨hx.1, by linarith [hx.2, Real.pi_pos]⟩)
      (convex_Icc _ _)
  have hc : ConcaveOn ℝ (Set.Icc 0 (Real.pi / 2)) Real.cos :=
    strictConcaveOn_cos_Icc.concaveOn.subset
      (by intro x hx; exact ⟨by linarith [hx.1, Real.pi_pos], hx.2⟩)
      (convex_Icc _ _)
  convert (hs.smul hA).add (hc.smul hB) using 1 <;> rfl

/-- Strict lower bounds at both ends of an interval in the first quadrant
give the same strict lower bound throughout the interval. -/
theorem sin_cos_arc_lower_bound {A B k l u β : ℝ}
    (hA : 0 ≤ A) (hB : 0 ≤ B) (hl : 0 ≤ l) (hu : u ≤ Real.pi / 2)
    (hlβ : l ≤ β) (hβu : β ≤ u)
    (hleft : k < A * Real.sin l + B * Real.cos l)
    (hright : k < A * Real.sin u + B * Real.cos u) :
    k < A * Real.sin β + B * Real.cos β := by
  have hlu : l ≤ u := hlβ.trans hβu
  have hlmem : l ∈ Set.Icc 0 (Real.pi / 2) := ⟨hl, hlu.trans hu⟩
  have humem : u ∈ Set.Icc 0 (Real.pi / 2) := ⟨hl.trans hlu, hu⟩
  have hseg : β ∈ segment ℝ l u := by
    rw [segment_eq_Icc hlu]
    exact ⟨hlβ, hβu⟩
  exact (lt_min hleft hright).trans_le
    ((concaveOn_sin_cos_quarter hA hB).ge_on_segment hlmem humem hseg)

end Puzzling139335.GlideCrossing
