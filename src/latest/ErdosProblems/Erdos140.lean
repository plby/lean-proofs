import ErdosProblems.Erdos140.Quantitative
import ErdosProblems.Erdos140.KelleyMekaCount
import ErdosProblems.Erdos140.FinalAssembly
import ErdosProblems.Erdos140.ConcreteSupply

/-!
# Erdős Problem 140

The public theorem below is the literal r3 formulation of the problem:
for every positive real exponent C, the largest three-term-progression-free
subset of {1, ..., N} is O(N / (log N)^C).

The long finite-group argument is split into the files in
ErdosProblems/Erdos140/.  This endpoint first turns the concrete
rank-regular two-Bohr supply into the ordered Kelley--Meka progression count,
then uses the elementary quantitative endpoint from Quantitative.lean.
-/

open Filter
open scoped Topology

namespace Erdos140

/-- Once the concrete rank-regular supply has been established, the exact
Erdős-140 asymptotic bound follows for every real logarithmic exponent.
The positivity hypothesis from the problem statement is therefore not needed
at this final analytic step. -/
theorem isBigO_r3_log_rpow_of_rawConcreteSupply
    {K : ℝ} (hK : 0 < K) (hraw : FinalAssembly.RawConcreteSupply K)
    (C : ℝ) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  obtain ⟨K', N₀, hcount⟩ :=
    exists_orderedCount_of_exists_holderCertificates
      ⟨8 + 2050 * (2 : ℝ) ^ 12 * K,
        FinalAssembly.holderCertificates_of_rawConcreteSupply hK hraw⟩
  exact isBigO_r3_log_rpow_of_orderedCount hcount C

/-- Existential form of the final composition.  The remaining structural
theorem in ConcreteSupply.lean supplies this hypothesis unconditionally. -/
theorem erdos_140_of_exists_rawConcreteSupply
    (hraw : ∃ K : ℝ, 0 < K ∧ FinalAssembly.RawConcreteSupply K)
    (C : ℝ) (_hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  obtain ⟨K, hK, hKraw⟩ := hraw
  exact isBigO_r3_log_rpow_of_rawConcreteSupply hK hKraw C

/-- Erdős Problem 140: for every positive logarithmic exponent C, the
largest three-term-progression-free subset of {1, ..., N} is
O(N / (log N)^C). -/
theorem erdos_140 (C : ℝ) (hC : 0 < C) :
    (fun N : ℕ => (r3 N : ℝ)) =O[atTop]
      (fun N : ℕ => (N : ℝ) / (Real.log (N : ℝ)) ^ C) := by
  exact erdos_140_of_exists_rawConcreteSupply
    ConcreteSupply.exists_rawConcreteSupply C hC

#print axioms isBigO_r3_log_rpow_of_rawConcreteSupply
#print axioms erdos_140_of_exists_rawConcreteSupply
#print axioms erdos_140

end Erdos140
