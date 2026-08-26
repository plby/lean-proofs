/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The score-ordered entropy of the BBMST initial coordinate segments.
Informal source: BBMST equations (17)--(19).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingFrameLower
import ErdosProblems.Erdos1189.FrameEntropyFormula

namespace Erdos1189

open Finset

noncomputable def countingEntropy (x : ℝ) : ℝ := by
  classical
  exact ∑ c ∈ countingCoordinates x, ((c.1 - 1 : ℕ) : ℝ) *
    ∑ i ∈ countingCoordinates x with i.1 ≠ c.1 ∧
      coordinateScore i.1 i.2 < coordinateScore c.1 c.2, logIncrement i.2

lemma countingEntropy_eq_coordinates (x : ℝ) :
    countingEntropy x =
      ∑ c : PrimeCoordinate (countingInteger x), ((coordinateSize c - 1 : ℕ) : ℝ) *
        ∑ i : PrimeCoordinate (countingInteger x) with i.1 ≠ c.1 ∧
          coordinateScore i.1 i.2 < coordinateScore c.1 c.2, logIncrement i.2.val := by
  classical
  unfold countingEntropy
  simp only [sum_filter]
  rw [← image_counting_coordinates x]
  simp only [sum_image (fun _ _ _ _ h => coordinatePair_injective (countingInteger x) h)]
  apply sum_congr rfl
  intro c _
  congr 1
  apply sum_congr rfl
  intro i _
  simp only [coordinatePair, ne_eq, Subtype.ext_iff]
  rfl

lemma countingEntropy_le_frameEntropy {x : ℝ}
    {rank : PrimeCoordinate (countingInteger x) → ℕ} (hrank : IsArithmeticRank rank)
    (href : ∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i) :
    countingEntropy x ≤ frameEntropy rank := by
  classical
  rw [countingEntropy_eq_coordinates, frameEntropy_eq hrank]
  apply sum_le_sum
  intro c _
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  apply sum_le_sum_of_subset_of_nonneg
  · intro i hi
    obtain ⟨_, hne, hscore⟩ := mem_filter.mp hi
    exact mem_filter.mpr ⟨mem_univ _, hne, href i c hscore⟩
  · intro i _ _
    exact (logIncrement_pos i.2.val).le

/-- The finite score-entropy lower bound has no unproved covering-system inputs. -/
theorem countingEntropy_lower_count {x : ℝ} (hx : coordinateScore 7 0 < x) :
    countingEntropy x - (simpsonWeight (countingInteger x) : ℝ) *
      (Real.log 2 + 2 * Real.log (countingSize x)) ≤
        Real.log (irreducibleCount (countingSize x)) := by
  obtain ⟨rank, _, hrank, href, hbound⟩ := counting_frame_lower hx
  exact (sub_le_sub_right (countingEntropy_le_frameEntropy hrank href) _).trans hbound

end Erdos1189
