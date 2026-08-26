import ErdosProblems.Erdos67b.MRTDyadicPartition

/-! # The logarithmic cost of the actual dyadic minor-arc partition -/

open scoped BigOperators
open Finset

namespace Erdos67b

noncomputable section

theorem mrtExists_dyadicRamare_minorArc_saving :
    ∃ C : ℝ, 0 < C ∧ ∀ H W q : ℕ, ∀ a : ℤ, ∀ α : ℝ,
      1 ≤ Real.log H → 2 ≤ W → W ≤ q → q ≤ H / W + 1 →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / q| ≤ (W : ℝ) / ((H : ℝ) * q) →
      ∀ (blocks : Finset (ℕ × ℕ)) (I : ℕ × ℕ) (Z Y : ℕ) (f θ : ℕ → ℂ),
        W ^ 200 ≤ I.1 → I.2 ≤ H / W ^ 3 → H ≤ Y →
        (∀ J ∈ blocks, J ≠ I → Disjoint (primesInBlock I) (primesInBlock J)) →
        (∀ r, 0 < r → ‖f r‖ ≤ 1) → (∀ n ∈ Finset.Ioc Y (2 * Y), ‖θ n‖ ≤ 1) →
        ‖∑ n ∈ Finset.Ioc Y (2 * Y),
          θ n * mrtRawRamarePrimeSum blocks I (primesInBlock I) Z f n H α‖ ^ 4 ≤
          C * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H ^ 5 / W := by
  obtain ⟨C, hC, hfinite⟩ := mrtExists_finiteRamare_minorArc_saving
  refine ⟨81 * C, by positivity, ?_⟩
  intro H W q a α hlog hW hWq hq ha hα blocks I Z Y f θ hIlo hIhi hHY hdisj hf hθ
  let V := mrtActiveDyadicBlocks I (W ^ 200) H
  let D := mrtSelectedDyadicPrimes I (W ^ 200)
  let P : ℕ → ℕ := fun j ↦ 2 ^ j * W ^ 200
  have hH : 1 ≤ H := by
    by_contra h
    have hzero : H = 0 := by omega
    norm_num [hzero] at hlog
  have hbase : 0 < W ^ 200 := pow_pos (by omega) _
  have hpart : Set.PairwiseDisjoint (↑V) D := mrtSelectedDyadicPrimes_pairwise I _ V
  have hcover : V.biUnion D = primesInBlock I :=
    mrtActiveDyadicBlocks_cover hbase (fun p hp ↦ mrtSelectedPrime_gt_power hIlo hp)
      (hIhi.trans (Nat.div_le_self _ _))
  have hD : ∀ j ∈ V, D j ⊆ dyadicPrimeBlock (P j) 0 :=
    fun j _ ↦ mrtSelectedDyadicPrimes_scaled I _ j
  have hP : ∀ j ∈ V,
      W ^ 200 ≤ P j ∧ P j ≤ H / W ^ 3 ∧ 1 ≤ Real.log (P j) := by
    intro j hj
    have hh := mrtActiveDyadicBlocks_lower_upper hj
    exact ⟨hh.1, hh.2.le.trans hIhi, mrtLog_dyadicScale_one_le hW hh.1⟩
  have hcount : (V.card : ℝ) ≤ 3 * Real.log H := by
    apply (show (V.card : ℝ) ≤ mrtDyadicBlockCount H by
      exact_mod_cast mrtCard_activeDyadicBlocks_le I (W ^ 200) H).trans
    exact mrtDyadicBlockCount_le_log hlog
  have hlog0 : 0 ≤ Real.log H := zero_le_one.trans hlog
  calc
    _ ≤ C * (V.card : ℝ) ^ 4 * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H / W :=
      hfinite H W q a α hW hWq hq ha hα blocks I V D P Z Y f θ hHY hH
        hpart hcover hD hP hdisj hf hθ
    _ ≤ C * (3 * Real.log H) ^ 4 * (H : ℝ) ^ 4 * (Y : ℝ) ^ 4 * Real.log H / W := by
      gcongr
    _ = _ := by ring

end

end Erdos67b
