import ErdosProblems.Erdos67b.MRHalaszDistanceTail
import ErdosProblems.Erdos67b.MRTMajorArc

/-!
# Propagating MR nonpretentiousness to lower cutoffs

This file specializes the unconditional reciprocal-prime tail estimate to the
Archimedean twists occurring in the complex Matomaki--Radziwill theorem.
-/

namespace Erdos67b.MRHalaszDistancePropagation

noncomputable section

open Erdos67b MRHalaszDistanceTail

/-- Uniformly in the Archimedean frequency, nonpretentiousness at `X`
propagates to every lower prime cutoff `x`, with an explicit loss. -/
theorem exists_uniform_archimedean_distance_ge_at_lower_cutoff :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ {f : ℕ → ℂ} {A X x : ℕ},
        2 ≤ x → x < X →
        (∀ p, p.Prime → ‖f p‖ ≤ 1) →
        MRArchimedeanNonpretentious f A X →
        ∀ t : ℝ, |t| ≤ X →
          (A : ℝ) -
              2 * (Real.log ((X : ℝ) / (x + 1 : ℝ)) + C) /
                Real.log (x + 1 : ℝ) ≤
            pretentiousDistSq f (archimedeanTwist t) x := by
  obtain ⟨C, hC, htail⟩ :=
    exists_uniform_pretentiousDistSq_ge_at_lower_cutoff
  refine ⟨C, hC, ?_⟩
  intro f A X x hx hX hf hnonpret t ht
  apply htail hx hX hf
  · intro p hp
    rw [norm_archimedeanTwist hp.pos]
  · exact hnonpret t ht

end

end Erdos67b.MRHalaszDistancePropagation
