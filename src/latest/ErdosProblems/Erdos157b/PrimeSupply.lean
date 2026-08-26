import ErdosProblems.Erdos157b.PrefixEstimates
import ErdosProblems.Erdos157.GoodFibers

namespace Erdos157.Binary

open Erdos157.Elementary Elementary.PolynomialCharacters Elementary.AuxiliaryModuli
open Elementary.FiniteFiberCounts Polynomial Filter
open scoped Topology

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K] [CharP K 2]

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


theorem eventually_six_le_prefix_primeSupply :
    ∀ᶠ k in atTop, ∀ g : K[X], g.Monic → g.natDegree = prefixLength k ^ 2 →
      (6 : ℝ) ≤ (Fintype.card K : ℝ) ^ levelDegree k /
        (2 * (levelDegree k : ℝ) * Nat.card (AdjoinRoot g)ˣ) := by
  have hq : (1 : ℝ) < Fintype.card K := by exact_mod_cast Fintype.one_lt_card
  have hlim := (tendsto_exponential_primeSupply (Fintype.card K) hq).comp tendsto_levelDegree
  have hexp := hlim.eventually_ge_atTop 6
  filter_upwards [hexp, eventually_twice_prefixDegree_le_levelDegree,
    eventually_prefixDegree_lt_levelDegree] with k hk hhalf hdeg
  intro g hg hdegree
  let : Finite (AdjoinRoot g) :=
    Finite.of_injective (AdjoinRoot.powerBasisAux' hg).equivFun
      (AdjoinRoot.powerBasisAux' hg).equivFun.injective
  have hφ : (0 : ℝ) < Nat.card (AdjoinRoot g)ˣ := by exact_mod_cast Nat.card_pos
  apply hk.trans (exponential_le_primeSupply _ _ hq hφ g.natDegree (levelDegree k)
    (lt_of_le_of_lt (Nat.zero_le _) hdeg) (by simpa only [hdegree] using hhalf) _)
  exact_mod_cast natCard_adjoinRoot_units_le g hg


theorem eventually_prefix_prime_lower :
    ∀ᶠ k in Filter.atTop, ∀ a : (AdjoinRoot (product K (prefixLength k)))ˣ,
      (Fintype.card K : ℝ) ^ levelDegree k /
          (2 * (levelDegree k : ℝ) * Nat.card (AdjoinRoot (product K (prefixLength k)))ˣ) ≤
        PolynomialCharacters.primeProgressionCount (product K (prefixLength k)) (levelDegree k) ↑a := by
  classical
  filter_upwards [eventually_shortPrefix_prime_lower (K := K)] with k hk
  exact hk _ (product_monic K _) (product_natDegree K _) (quotient_units_card_odd K _)


theorem eventually_prefix_tripleSupply :
    ∀ᶠ k in atTop, ∀ u : (AdjoinRoot (AuxiliaryModuli.product K (prefixLength k)))ˣ,
      (Fintype.card K : ℝ) ^ (3 * levelDegree k) /
        (512 * (levelDegree k : ℝ) ^ 3 * Nat.card (AdjoinRoot (AuxiliaryModuli.product K (prefixLength k)))ˣ) ≤
      Nat.card {T : PrimeTriple K (levelDegree k) // levelTripleResidue k (prefixLength k) T = u} := by
  filter_upwards [eventually_prefix_prime_lower (K := K),
    eventually_six_le_prefix_primeSupply (K := K), eventually_prefixDegree_lt_levelDegree]
      with k hprimes hsize hdeg
  intro u
  apply primeTriple_fiber_lower_of_primeSupply _ (AuxiliaryModuli.product_monic K _)
    (lt_of_le_of_lt (Nat.zero_le _) hdeg)
    (fun f => AuxiliaryModuli.product_isCoprime_even_prime K (levelDegree_even k) f _)
  · exact hsize _ (AuxiliaryModuli.product_monic K _) (AuxiliaryModuli.product_natDegree K _)
  · exact hprimes


theorem eventually_good_extensions :
    ∀ᶠ k in atTop, prefixLength k ≤ k ∧ ∀ (hhk : prefixLength k ≤ k)
      (u : (AdjoinRoot (product K (prefixLength k)))ˣ),
      (fiberCard (quotientProjection K hhk) u : ℝ) / (1024 * (levelDegree k : ℝ) ^ 3) ≤
        Nat.card {v : {v : (AdjoinRoot (product K k))ˣ // quotientProjection K hhk v = u} //
          GoodResidue k v.1} := by
  filter_upwards [eventually_prefixLength_le, eventually_prefix_tripleSupply (K := K),
    eventually_prefixDegree_lt_levelDegree] with k hk hmass hdeg
  refine ⟨hk, fun hhk u => ?_⟩
  exact good_extensions_lower k (prefixLength k) hhk (lt_of_le_of_lt (Nat.zero_le _) hdeg) u (hmass u)


end Erdos157.Binary
