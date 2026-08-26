/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite lower bound along the BBMST coordinate initial segments.
Informal source: BBMST Section 5 and Section 8.3 of the selected writeup.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingCoordinates
import ErdosProblems.Erdos1189.OptimalFrameCount

namespace Erdos1189

noncomputable def countingSize (x : ℝ) : ℕ := simpsonWeight (countingInteger x) + 1

lemma countingSize_eq (x : ℝ) :
    countingSize x = 1 + ∑ c ∈ countingCoordinates x, (c.1 - 1) := by
  rw [countingSize, countingInteger_weight, Nat.add_comm]

theorem counting_frame_lower {x : ℝ} (hx : coordinateScore 7 0 < x) :
    ∃ rank : PrimeCoordinate (countingInteger x) → ℕ,
      Function.Injective rank ∧ IsArithmeticRank rank ∧
      (∀ c i, coordinateScore c.1 c.2 < coordinateScore i.1 i.2 → rank c < rank i) ∧
      frameEntropy rank - (simpsonWeight (countingInteger x) : ℝ) *
        (Real.log 2 + 2 * Real.log (countingSize x)) ≤
          Real.log (irreducibleCount (countingSize x)) := by
  obtain ⟨P, hP, hP7, hpf⟩ := countingInteger_primeFactors_initial hx
  obtain ⟨rank, hinj, hrank, href⟩ := exists_optimal_frame_rank (countingInteger x)
  exact ⟨rank, hinj, hrank, href, optimal_frame_count
    (countingInteger_one_lt hx) hP hP7 hpf hinj hrank href⟩

end Erdos1189
