/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos946.SieveAsymptotics

/-! # Selecting a squarefree value with small Richert weight -/

open scoped BigOperators

namespace Erdos946.SieveSelection

open AffineSieve SieveWindow SquarefreeSieve RichertWeights

noncomputable section

theorem richert_main_coefficient_lt {A : ℝ} (hA : A < 601 / 100) :
    16 * (1 + sieveError) * A < 963 / 10 := by
  have hp : 0 < 16 * (1 + sieveError) := by linarith [sieveError_nonneg]
  have h := mul_lt_mul_of_pos_left hA hp
  nlinarith [sieveError_lt]

theorem exists_squarefree_weight_lt
    (S : Finset ℕ) (F : ℕ → ℕ) (w : ℕ → ℝ)
    {Q E₀ E₁ E₂ : ℝ} (_hQ : 0 < Q)
    (hE₀ : 0 ≤ E₀) (hE₁ : 0 ≤ E₁) (hE₂ : 0 ≤ E₂)
    (hsmall : E₀ + E₁ + E₂ < Q / 1000)
    (hcard : (999 / 1000) * Q - E₀ ≤ (S.card : ℝ))
    (hbad : ((nonsquarefreeCandidates S F).card : ℝ) ≤ E₁)
    (hweight : (∑ n ∈ S, w n) ≤ (963 / 10) * Q + E₂)
    (hwnonneg : ∀ n ∈ S, 0 ≤ w n) :
    ∃ n ∈ S, Squarefree (F n) ∧ w n < 97 := by
  let T := squarefreeCandidates S F
  have hpartition : (T.card : ℝ) +
      ((nonsquarefreeCandidates S F).card : ℝ) = S.card := by
    exact_mod_cast card_squarefree_add_nonsquarefree S F
  have hT : (998 / 1000) * Q < (T.card : ℝ) := by linarith
  have hsum : (∑ n ∈ T, w n) ≤ ∑ n ∈ S, w n :=
    Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
      (fun n hn _ ↦ hwnonneg n hn)
  have hlt : (∑ n ∈ T, w n) < ∑ _n ∈ T, (97 : ℝ) := by
    simp only [Finset.sum_const, nsmul_eq_mul]
    nlinarith
  obtain ⟨n, hn, hw⟩ := Finset.exists_lt_of_sum_lt hlt
  exact ⟨n, (Finset.mem_filter.mp hn).1, (Finset.mem_filter.mp hn).2, hw⟩

def coefficientBound (a b : Fin 16 → ℕ) : ℕ :=
  1 + ∑ i : Fin 16, (2 * a i + b i)

theorem affine_le_parameterPower {a b : Fin 16 → ℕ} {N n : ℕ}
    (hN : 1 ≤ N) (hC : coefficientBound a b ≤ N)
    (hn : n ≤ 2 * N ^ 2100) (i : Fin 16) :
    a i * n + b i ≤ N ^ 2101 := by
  have hi : 2 * a i + b i ≤ N :=
    (Finset.single_le_sum (fun j _ ↦ Nat.zero_le (2 * a j + b j))
      (Finset.mem_univ i)).trans (by dsimp [coefficientBound] at hC; omega)
  have hX : 1 ≤ N ^ 2100 := one_le_pow₀ hN
  calc
    a i * n + b i ≤ a i * (2 * N ^ 2100) + b i * N ^ 2100 :=
      add_le_add (Nat.mul_le_mul_left _ hn)
        (by simpa only [mul_one] using Nat.mul_le_mul_left (b i) hX)
    _ = (2 * a i + b i) * N ^ 2100 := by ring
    _ ≤ N * N ^ 2100 := Nat.mul_le_mul_right _ hi
    _ = N ^ 2101 := (pow_succ' N 2100).symm

theorem affine_le_squarePower {a b : Fin 16 → ℕ} {N n : ℕ}
    (hN : 1 ≤ N) (hC : coefficientBound a b ≤ N)
    (hn : n ≤ 2 * N ^ 2100) (i : Fin 16) :
    a i * n + b i ≤ (N ^ 1051) ^ 2 := by
  calc
    _ ≤ N ^ 2101 := affine_le_parameterPower hN hC hn i
    _ ≤ N ^ 2102 := Nat.pow_le_pow_right hN (by decide : (2101 : ℕ) ≤ 2102)
    _ = _ := by rw [← pow_mul]

theorem affineProduct_le_weightPower {a b : Fin 16 → ℕ} {N n : ℕ}
    (hN : 1 ≤ N) (hC : coefficientBound a b ≤ N)
    (hn : n ≤ 2 * N ^ 2100) :
    affineProduct a b n ≤ (N ^ 1000) ^ 34 := by
  calc
    _ ≤ ∏ _i : Fin 16, N ^ 2101 := Finset.prod_le_prod'
      (fun i _ ↦ affine_le_parameterPower hN hC hn i)
    _ = N ^ 33616 := by simp only [Finset.prod_const, Finset.card_univ,
      Fintype.card_fin, ← pow_mul]
    _ ≤ N ^ 34000 := Nat.pow_le_pow_right hN (by decide : (33616 : ℕ) ≤ 34000)
    _ = _ := by rw [← pow_mul]

theorem log_ratio_le_of_le_pow {m Y : ℕ} (hm : 0 < m) (hY : 1 < Y)
    (hsize : m ≤ Y ^ 34) : Real.log (m : ℝ) / Real.log (Y : ℝ) ≤ 34 := by
  have hlog : 0 < Real.log (Y : ℝ) := Real.log_pos (by exact_mod_cast hY)
  rw [div_le_iff₀ hlog]
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  have hle : (m : ℝ) ≤ (Y : ℝ) ^ 34 := by exact_mod_cast hsize
  have h := Real.log_le_log hmR hle
  simpa only [Real.log_pow, Nat.cast_ofNat] using h

theorem sifted_rough {a b : Fin 16 → ℕ} {X z y n : ℕ}
    (hsmall : ∀ p : ℕ, p.Prime → p ≤ z → ¬p ∣ affineProduct a b n)
    (hn : n ∈ siftedCandidates a b X z (y + 1)) :
    ∀ p : ℕ, p.Prime → p ≤ y → ¬p ∣ affineProduct a b n := by
  intro p hp hpy
  by_cases hpz : p ≤ z
  · exact hsmall p hp hpz
  · have hpP : p ∣ Erdos387.sievePrimeProduct z (y + 1) :=
      Finset.dvd_prod_of_mem id
        (Erdos387.mem_sievePrimes.mpr ⟨hp, by omega, by omega⟩)
    have hc := (Finset.mem_filter.mp hn).2
    exact hp.coprime_iff_not_dvd.mp (Nat.Coprime.of_dvd_left hpP hc)

end

end Erdos946.SieveSelection
