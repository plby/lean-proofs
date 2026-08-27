import ErdosProblems.Erdos587.HooleyProgressionCover
import ErdosProblems.Erdos587.HooleySieveLogBlock
import ErdosProblems.Erdos587.HooleySieveSmallPrimes
import ErdosProblems.Erdos587.HooleyFiniteCover

/-!
# Unconditional Delta means in short affine progressions

The three proved sieve ranges cover every nonzero affine value. Their
sum is uniform in the signed primitive coefficients. This first form
retains an integer fourth-root scale and the slope's totient ratio.
-/

open scoped BigOperators

namespace Erdos587

theorem exists_delta_affine_fourth_root_mean (k : ℕ) (hk : 0 < k) :
    ∃ C : ℝ, 0 < C ∧ ∀ (A B : ℤ), B ≠ 0 → IsCoprime A B →
      ∀ R N Y : ℕ, 2 ≤ R → 2 ≤ N → R ^ 4 ≤ Y → N ≤ (R + 1) ^ k →
      ∀ S : Finset ℕ, S ⊆ Finset.Icc 1 Y →
      (∀ n ∈ S, A + B * n ≠ 0) → (∀ n ∈ S, (A + B * n).natAbs ≤ N) →
      (∑ n ∈ S, (hooleyDelta (A + B * n).natAbs : ℝ)) ≤
        C * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 := by
  classical
  obtain ⟨C₀, hC₀, hmain⟩ := exists_delta_main_sieve_loglog_bound k hk
  obtain ⟨C₁, hC₁, hsmall⟩ := exists_delta_small_prime_sieve_bound k
    (deltaSmallPrimeCutoff k) hk (deltaSmallPrimeCutoff_two_le k)
  obtain ⟨C₂, hC₂, hblock⟩ := exists_delta_sieve_log_block_bound k hk
  refine ⟨C₀ + C₁ + 2 * C₂, by positivity, ?_⟩
  intro A B hB hAB R N Y hR hN hRY hRN S hS hnonzero hvalues
  let f : ℕ → ℝ := fun n => hooleyDelta (A + B * n).natAbs
  let S₀ := S.filter (fun n : ℕ => DeltaMainFactor R (A + B * n).natAbs)
  let S₁ := S.filter (fun n : ℕ => DeltaSmallFactor R (deltaSmallPrimeCutoff k) (A + B * n).natAbs)
  let F : ℕ → Finset ℕ := fun j => S.filter (fun n : ℕ => 1 ≤ j ∧
    2 * (2 * (k : ℝ) + 2) ≤ Real.log (deltaLogCutoff R j : ℝ) ∧
      DeltaBlockFactor R j (A + B * n).natAbs)
  let Z : ℝ := ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
    (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5
  have hZ : 0 ≤ Z := by dsimp only [Z]; positivity
  have hS₀ : S₀ ⊆ S := Finset.filter_subset _ _
  have hS₁ : S₁ ⊆ S := Finset.filter_subset _ _
  have hF (j : ℕ) : F j ⊆ S := Finset.filter_subset _ _
  have hcover : ∀ n ∈ S, n ∈ S₀ ∨ n ∈ S₁ ∨
      ∃ j ∈ Finset.range (deltaPrimeBlockCount R), n ∈ F j := by
    intro n hn
    rcases delta_prime_prefix_cover k (by omega : 1 ≤ R) (Int.natAbs_pos.mpr (hnonzero n hn))
      with hm | hs | ⟨j, hj, hj1, hlarge, hb⟩
    · exact Or.inl (Finset.mem_filter.mpr ⟨hn, hm⟩)
    · exact Or.inr (Or.inl (Finset.mem_filter.mpr ⟨hn, hs⟩))
    · exact Or.inr (Or.inr ⟨j, hj, Finset.mem_filter.mpr ⟨hn, hj1, hlarge, hb⟩⟩)
  have hsum₀ : (∑ n ∈ S₀, f n) ≤ C₀ * Z := by
    calc
      _ ≤ C₀ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 :=
        hmain A B hB hAB R N Y (by omega) hN hRY hRN S₀ (hS₀.trans hS)
          (fun n hn => hvalues n (hS₀ hn)) (fun n hn => (Finset.mem_filter.mp hn).2)
      _ = _ := by dsimp only [Z]; ring
  have hsum₁ : (∑ n ∈ S₁, f n) ≤ C₁ * Z := by
    calc
      _ ≤ C₁ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
          (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 :=
        hsmall A B hB hAB R N Y hR hN hRY hRN S₁ (hS₁.trans hS)
          (fun n hn => hvalues n (hS₁ hn)) (fun n hn => (Finset.mem_filter.mp hn).2)
      _ = _ := by dsimp only [Z]; ring
  have hsumF (j : ℕ) : (∑ n ∈ F j, f n) ≤ C₂ * Z * Real.exp (-(j : ℝ)) := by
    by_cases hne : (F j).Nonempty
    · obtain ⟨n, hn⟩ := hne
      have hprops := (Finset.mem_filter.mp hn).2
      calc
        _ ≤ C₂ * ((B.natAbs : ℝ) / B.natAbs.totient) * Y *
            (max 1 (Real.log (Real.log (N : ℝ)))) ^ 5 * Real.exp (-(j : ℝ)) :=
          hblock A B hB hAB R N Y j hR hN hRY hRN hprops.1 hprops.2.1 (F j)
            ((hF j).trans hS) (fun n hn => hvalues n (hF j hn))
            (fun n hn => (Finset.mem_filter.mp hn).2.2.2)
        _ = _ := by dsimp only [Z]; ring
    · rw [Finset.not_nonempty_iff_eq_empty.mp hne, Finset.sum_empty]
      positivity
  have hsumBlocks : (∑ j ∈ Finset.range (deltaPrimeBlockCount R), ∑ n ∈ F j, f n) ≤
      2 * C₂ * Z := by
    calc
      _ ≤ ∑ j ∈ Finset.range (deltaPrimeBlockCount R), C₂ * Z * Real.exp (-(j : ℝ)) :=
        Finset.sum_le_sum (fun j _ => hsumF j)
      _ = (C₂ * Z) * ∑ j ∈ Finset.range (deltaPrimeBlockCount R), Real.exp (-(j : ℝ)) :=
        (Finset.mul_sum _ _ _).symm
      _ ≤ (C₂ * Z) * 2 := mul_le_mul_of_nonneg_left
        (delta_sum_exp_neg_le_two _) (mul_nonneg hC₂.le hZ)
      _ = _ := by ring
  calc
    _ ≤ (∑ n ∈ S₀, f n) + (∑ n ∈ S₁, f n) +
        ∑ j ∈ Finset.range (deltaPrimeBlockCount R), ∑ n ∈ F j, f n :=
      delta_sum_cover_three_le S S₀ S₁ _ F f (fun n => by dsimp only [f]; positivity)
        hS₀ hS₁ (fun j _ => hF j) hcover
    _ ≤ C₀ * Z + C₁ * Z + 2 * C₂ * Z := add_le_add (add_le_add hsum₀ hsum₁) hsumBlocks
    _ = _ := by dsimp only [Z]; ring

end Erdos587
