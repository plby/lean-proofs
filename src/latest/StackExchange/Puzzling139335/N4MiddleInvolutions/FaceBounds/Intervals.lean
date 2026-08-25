import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.BigOperators

/-!
# A finite family of disjoint intervals inside one interval

Lebesgue measure makes the length estimate independent of the order of
the intervals. Degenerate intervals contribute zero and need no special
case.
-/

open Set MeasureTheory
open scoped BigOperators

namespace Puzzling139335.N4MiddleInvolutions.FaceBounds

/-- The total length of finitely many pairwise disjoint open intervals
contained in one ambient interval is at most the ambient length. -/
theorem sum_interval_lengths_le {ι : Type*}
    (s : Finset ι) (lo hi : ι → ℝ) {L U : ℝ}
    (hLU : L ≤ U) (hlo : ∀ i ∈ s, L ≤ lo i) (hhi : ∀ i ∈ s, hi i ≤ U)
    (hord : ∀ i ∈ s, lo i ≤ hi i)
    (hdis : (↑s : Set ι).Pairwise fun i j =>
      Disjoint (Ioo (lo i) (hi i)) (Ioo (lo j) (hi j))) :
    ∑ i ∈ s, (hi i - lo i) ≤ U - L := by
  apply (ENNReal.ofReal_le_ofReal_iff (sub_nonneg.mpr hLU)).mp
  rw [ENNReal.ofReal_sum_of_nonneg (fun i hi => sub_nonneg.mpr (hord i hi))]
  calc
    ∑ i ∈ s, ENNReal.ofReal (hi i - lo i) =
        volume (⋃ i ∈ s, Ioo (lo i) (hi i)) := by
      rw [measure_biUnion_finset hdis (fun _ _ => measurableSet_Ioo)]
      simp only [Real.volume_Ioo]
    _ ≤ volume (Ioo L U) := by
      apply measure_mono
      intro x hx
      obtain ⟨i, hi, hxi⟩ := mem_iUnion₂.mp hx
      exact ⟨(hlo i hi).trans_lt hxi.1, hxi.2.trans_le (hhi i hi)⟩
    _ = ENNReal.ofReal (U - L) := Real.volume_Ioo

end Puzzling139335.N4MiddleInvolutions.FaceBounds
