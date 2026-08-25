import ErdosProblems.Erdos157.PrefixParameters
import ErdosProblems.Erdos157.PrimeProgressionLowerBound

/-! Uniform prime supply for every modulus with the prescribed short-prefix degree. -/

namespace Erdos157.Elementary

open Filter Polynomial PolynomialCharacters
open scoped Topology

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

/-- Eventually, every unit class of every eligible prefix modulus contains
at least half of the expected number of prime polynomials. -/
theorem eventually_shortPrefix_prime_lower :
    ∀ᶠ k in atTop, ∀ (g : K[X]), g.Monic → g.natDegree = prefixLength k ^ 2 →
      Odd (Nat.card (AdjoinRoot g)ˣ) → ∀ a : (AdjoinRoot g)ˣ,
      (Fintype.card K : ℝ) ^ levelDegree k /
          (2 * (levelDegree k : ℝ) * Nat.card (AdjoinRoot g)ˣ) ≤
        primeProgressionCount g (levelDegree k) ↑a := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card
  have herr := (tendsto_prefix_relativeError (Fintype.card K) hq).eventually
    (gt_mem_nhds (by norm_num : (0 : ℝ) < 1 / 2))
  filter_upwards [herr, eventually_prefixDegree_lt_levelDegree] with k hk hdegree
  intro g hg hdeg hodd a
  apply primeProgressionCount_lower g hg hodd (levelDegree k) (by simpa only [hdeg] using hdegree)
  simpa only [hdeg, Nat.cast_pow] using hk.le

end Erdos157.Elementary
