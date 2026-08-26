/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SieveSelection

/-! # Squarefree almost-prime values of the sixteen affine forms -/

open scoped BigOperators
open Filter

namespace Erdos946.SieveSupply

open AffineSieve SieveWindow SquarefreeSieve RichertWeights SieveSelection
open MertensRichert WeightedAverage SieveAsymptotics

noncomputable section

/-- The sieve output, with all analytic hypotheses discharged by the
preceding finite bounds and limit theorems. -/
theorem exists_large_squarefree_cardFactors_le
    (a b : Fin 16 → ℕ) {z : ℕ} (hz : 272 ≤ z)
    (hb : ∀ i, 0 < b i)
    (hpair : ∀ n, Pairwise fun i j ↦ (a i * n + b i).Coprime (a j * n + b j))
    (hsmall : ∀ n p : ℕ, p.Prime → p ≤ z → ¬p ∣ affineProduct a b n)
    (hlocal : ∀ p : ℕ, p.Prime → z < p → localNu a b p = 16)
    (hcop : ∀ p : ℕ, p.Prime → z < p → ∀ i, (a i).Coprime p)
    (T : ℕ) :
    ∃ n : ℕ, T < n ∧ Squarefree (affineProduct a b n) ∧
      ArithmeticFunction.cardFactors (affineProduct a b n) ≤ 130 := by
  obtain ⟨N, hN, hzN, hCN, hTN, herr, hmass⟩ :=
    ((eventually_ge_atTop 2).and ((eventually_ge_atTop z).and
      ((eventually_ge_atTop (coefficientBound a b)).and
        ((eventually_ge_atTop (T + 1)).and
          ((eventually_combinedError_lt hz).and
            eventually_primeRichertMass_thousand_lt))))).exists
  let S := siftedCandidates a b (N ^ 2100) z (N + 1)
  let Q : ℝ := (N : ℝ) ^ 2100 * sieveV z N
  have hNpos : 0 < N := by omega
  have hNR : (0 : ℝ) < N := by exact_mod_cast hNpos
  have hQ : 0 < Q := mul_pos (pow_pos hNR _) (sieveV_pos (by omega : 16 ≤ z))
  have hY : 1 < N ^ 1000 := one_lt_pow₀ (by omega : 1 < N) (by norm_num)
  have hI : S ⊆ Finset.Ioc (N ^ 2100) (2 * N ^ 2100) := Finset.filter_subset _ _
  have hpos : ∀ n : ℕ, ∀ i, 0 < a i * n + b i := by
    intro n i
    exact Nat.add_pos_right _ (hb i)
  have hF : ∀ n : ℕ, 0 < affineProduct a b n := fun n ↦
    Finset.prod_pos fun i _ ↦ hpos n i
  have hrough : ∀ n ∈ S, ∀ p : ℕ, p.Prime → p ≤ N → ¬p ∣ affineProduct a b n :=
    fun n hn ↦ sifted_rough (hsmall n) hn
  have hcopS : ∀ p : ℕ, p.Prime → p ∣ Erdos387.sievePrimeProduct z (N + 1) →
      ∀ i, (a i).Coprime p := by
    intro p hp hpP
    exact hcop p hp (Erdos387.mem_sievePrimes.mp
      (Erdos387.prime_mem_sievePrimes_of_dvd_product hp hpP)).2.1
  have hcard := (affine_cardinality_bounds (X := N ^ 2100) hz hzN
    (fun p hp hzp _ ↦ hlocal p hp hzp) hcopS).1
  norm_num only [Nat.cast_pow, ← pow_mul, Nat.reduceMul] at hcard
  have hcard' : (999 / 1000) * Q - (N : ℝ) ^ 1000 ≤ (S.card : ℝ) := by
    have hη : (999 / 1000 : ℝ) * Q ≤ (1 - sieveError) * Q :=
      mul_le_mul_of_nonneg_right (by linarith [sieveError_lt]) hQ.le
    calc
      _ ≤ (1 - sieveError) * Q - (N : ℝ) ^ 1000 := sub_le_sub_right hη _
      _ = (N : ℝ) ^ 2100 * ((1 - sieveError) * sieveV z N) -
          (N : ℝ) ^ 1000 := by dsimp only [Q]; ring
      _ ≤ _ := hcard
  have hbad := nonsquarefreeCandidates_card_le S (by omega : 1 ≤ N) hI
    (fun n _ i ↦ hpos n i)
    (fun n hn i ↦ affine_le_squarePower (by omega : 1 ≤ N) hCN
      (Finset.mem_Ioc.mp (hI hn)).2 i)
    (fun n _ ↦ hpair n) hrough (fun p hp hNp ↦ hcop p hp (hzN.trans_lt hNp))
  have hdiv : (N : ℝ) ^ 2100 / N = (N : ℝ) ^ 2099 := by
    rw [show (2100 : ℕ) = 2099 + 1 by rfl, pow_succ,
      mul_div_cancel_right₀ _ hNR.ne']
  simp only [Nat.cast_pow, hdiv] at hbad
  have hw := affine_weight_sum_bound (X := N ^ 2100) hz hzN hY hlocal hcopS
    (fun n _ ↦ (hF n).ne') hrough
  have hw' : (∑ n ∈ S, distinctRichertWeight (affineProduct a b n) (N ^ 1000)) ≤
      (963 / 10) * Q + 16 * (N : ℝ) ^ 2000 := by
    have heq : 16 * ((N ^ 2100 : ℕ) : ℝ) * ((1 + sieveError) * sieveV z N) *
        primeRichertMass N (N ^ 1000) +
        16 * ((N ^ 1000 : ℕ) : ℝ) * ((N ^ 500 : ℕ) : ℝ) ^ 2 =
      (16 * (1 + sieveError) * primeRichertMass N (N ^ 1000)) * Q +
        16 * (N : ℝ) ^ 2000 := by
      simp only [Nat.cast_pow]
      dsimp only [Q]
      ring
    rw [heq] at hw
    exact hw.trans (add_le_add
      (mul_le_mul_of_nonneg_right (richert_main_coefficient_lt hmass).le hQ.le) le_rfl)
  obtain ⟨n, hn, hsq, hwlt⟩ := exists_squarefree_weight_lt S (affineProduct a b)
    (fun n ↦ distinctRichertWeight (affineProduct a b n) (N ^ 1000))
    hQ (pow_nonneg hNR.le 1000)
    (mul_nonneg (by norm_num) (add_nonneg (pow_nonneg hNR.le 2099)
      (pow_nonneg hNR.le 1051)))
    (mul_nonneg (by norm_num) (pow_nonneg hNR.le 2000))
    herr hcard' hbad hw' (fun n _ ↦ distinctRichertWeight_nonneg _ hY)
  refine ⟨n, ?_, hsq, ?_⟩
  · have hnX := (Finset.mem_Ioc.mp (hI hn)).1
    have hNX : N ≤ N ^ 2100 := le_self_pow (by omega : 1 ≤ N) (by norm_num)
    omega
  · apply cardFactors_le_oneHundredThirty_of_weight_lt (hF n).ne' hY
    · exact log_ratio_le_of_le_pow (hF n) hY
        (affineProduct_le_weightPower (by omega : 1 ≤ N) hCN
          (Finset.mem_Ioc.mp (hI hn)).2)
    · rwa [richertWeight_eq_distinct_of_squarefree hsq]

end

end Erdos946.SieveSupply
