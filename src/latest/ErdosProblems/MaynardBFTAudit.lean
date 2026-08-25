import ErdosProblems.Erdos427
import ErdosProblems.Erdos997

/-!
# Axiom audit for the unconditional consecutive-prime theorem and its consumers

This audit is not imported by the mathematical proof modules.
-/

#print axioms MaynardBFT.consecutive_primes
#print axioms maynardTaoBFT
#print axioms shiu_consecutive_primes
#print axioms Erdos427.erdos_427
#print axioms Erdos997.erdos_997

-- Each declaration above depends only on [propext, Classical.choice, Quot.sound].
