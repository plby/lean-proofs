/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos232.CombinatorialInt

namespace Erdos232

private theorem pairContribution_eq_list (s : Nat) :
    atomPairContributionInt s =
      atomPairWeights.foldl
        (fun z p => z + if natMaskSubset p.1 s then p.2 else 0) 0 := by
  simp only [atomPairContributionInt, atomPairWeights, List.foldl]
  ring

private theorem congruenceContribution00_eq_list (s : Nat) :
    atomCongruenceContributionInt00 s =
      atomCongruenceWeights00.foldl (fun z c =>
        z + c.2.2 * ((if natMaskSubset c.1 s then 1 else 0) -
          (if natMaskSubset c.2.1 s then 1 else 0))) 0 := by
  simp only [atomCongruenceContributionInt00, atomCongruenceWeights00, List.foldl]
  ring

end Erdos232
