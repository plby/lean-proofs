import ErdosProblems.Erdos427
import ErdosProblems.Erdos997

/-!
# Axiom audit for the Maynard–Tao family and the BFT consumers

This audit is not imported by the mathematical proof modules.
-/

#print axioms MaynardTao.natural_maynard_tao
#print axioms MaynardTao.maynard_tao
#print axioms MaynardBFT.single_prime
#print axioms MaynardBFT.consecutive_primes
#print axioms maynardTaoBFT
#print axioms shiu_consecutive_primes
#print axioms Erdos427.erdos_427
#print axioms Erdos997.erdos_997

-- Each declaration above depends only on [propext, Classical.choice, Quot.sound].
