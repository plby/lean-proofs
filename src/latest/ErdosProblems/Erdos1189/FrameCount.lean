/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A finite lower bound on the number of irreducible covering sets from frames.
Informal source: Section 8.3 of Pickhardt and Omniscience Research Agent.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.FrameChoices
import ErdosProblems.Erdos1189.MaximumModulus

namespace Erdos1189

theorem frameCount_le_irreducibleCount {N : ℕ} (hN : 1 < N)
    (rank : PrimeCoordinate N → ℕ) :
    (∏ c : PrimeCoordinate N,
      (admissibleFrameModuli rank c).card.choose (coordinateSize c - 1)) ≤
        irreducibleCount (simpsonWeight N + 1) := by
  have h := Set.ncard_le_ncard_of_injOn
    (s := Set.univ) (t := irreducibleSetsOfSize (simpsonWeight N + 1))
    FrameChoice.moduli (fun F _ => F.irreducible hN)
    (FrameChoice.moduli_injective rank).injOn
    (finite_irreducibleSetsOfSize (simpsonWeight N + 1))
  simpa only [Set.ncard_univ, Nat.card_eq_fintype_card, card_frameChoice,
    irreducibleCount] using h

end Erdos1189
