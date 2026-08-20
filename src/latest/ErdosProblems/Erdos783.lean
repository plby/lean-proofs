/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, OpenAI Codex
-/
import ErdosProblems.Erdos783.GSFinal
import ErdosProblems.Erdos783.PrimeLower

/-!
# Erdős Problem 783

This is the public assembly module.  It combines the unconditional
Granville--Soundararajan/Hildebrand prime-only lower bound, Tao's reduction
from pairwise-coprime moduli to primes, and the terminal-prime construction.
-/

namespace Erdos783

noncomputable section

/-- Tao's endpoint-uniform lower bound for every admissible pairwise-coprime
family. -/
theorem taoLowerBound_dickmanRho : TaoLowerBound dickmanRho :=
  taoLowerBound_of_boundedComposite
    (boundedCompositeLowerBound_of_primeOnly_of_product
      primeOnlyLowerBound_dickmanRho dickmanProductInequality)

/-- Complete asymptotic resolution of Erdős Problem 783: for every fixed
positive reciprocal-mass budget `C`, the minimum unsieved density tends to
`dickmanRho (exp C)`. -/
theorem erdos_783 : AsymptoticResolution dickmanRho :=
  asymptoticResolution_of_lower_of_achievable
    taoLowerBound_dickmanRho terminalPrimeAchievability_dickmanRho

end

end Erdos783

#print axioms Erdos783.erdos_783
