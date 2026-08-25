import ErdosProblems.Erdos157.ShortPrefixPrimes

/-! The lower bound for the number of primes per short-prefix class tends to infinity. -/

namespace Erdos157.Elementary

open Filter Polynomial PolynomialCharacters
open scoped Topology

theorem tendsto_exponential_primeSupply (q : ℝ) (hq : 1 < q) :
    Tendsto (fun n : ℝ => Real.exp ((Real.log q / 2) * n) / (2 * n)) atTop atTop := by
  have hb : 0 < Real.log q / 2 := div_pos (Real.log_pos hq) (by norm_num)
  have h := (tendsto_exp_mul_div_rpow_atTop 1 (Real.log q / 2) hb).const_mul_atTop
    (by norm_num : (0 : ℝ) < 1 / 2)
  convert h using 1
  ext n
  simp only [Real.rpow_one]
  ring

theorem exponential_le_primeSupply (q φ : ℝ) (hq : 1 < q) (hφ : 0 < φ)
    (H n : ℕ) (hn : 0 < n) (hH : 2 * H ≤ n) (hcard : φ ≤ q ^ H) :
    Real.exp ((Real.log q / 2) * (n : ℝ)) / (2 * (n : ℝ)) ≤
      q ^ n / (2 * (n : ℝ) * φ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hqpos : 0 < q := lt_trans zero_lt_one hq
  have hpow (d : ℕ) : q ^ d = Real.exp ((d : ℝ) * Real.log q) := by
    rw [Real.exp_nat_mul, Real.exp_log hqpos]
  have hratio : Real.exp ((Real.log q / 2) * (n : ℝ)) ≤ q ^ n / q ^ H := by
    rw [hpow n, hpow H, ← Real.exp_sub]
    apply Real.exp_le_exp.mpr
    have hH' : 2 * (H : ℝ) ≤ n := by exact_mod_cast hH
    have hlog := (Real.log_pos hq).le
    nlinarith
  calc
    _ ≤ (q ^ n / q ^ H) / (2 * (n : ℝ)) := div_le_div_of_nonneg_right hratio (by positivity)
    _ = q ^ n / (2 * (n : ℝ) * q ^ H) := by ring
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) (by positivity)
      (mul_le_mul_of_nonneg_left hcard (by positivity))

variable {K : Type*} [Field K] [DecidableEq K] [Fintype K]

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

end Erdos157.Elementary
