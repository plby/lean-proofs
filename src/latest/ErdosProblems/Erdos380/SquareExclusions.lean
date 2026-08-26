import ErdosProblems.Erdos380.LongSmoothIntervals
import Mathlib.Analysis.PSeries

/-! # Elementary exclusions using large square divisors -/

open scoped BigOperators

namespace Erdos380

def largeSquareDivisorsUpTo (N D : ℕ) : Finset ℕ :=
  (Finset.Icc 1 N).filter fun n => ∃ d ∈ Finset.Icc D N, d ^ 2 ∣ n

lemma card_positive_multiples (N d : ℕ) :
    ((Finset.Icc 1 N).filter fun n => d ∣ n).card = N / d := by
  have hset : (Finset.Icc 1 N).filter (fun n => d ∣ n) =
      (Finset.range (N + 1)).filter (fun n => n ≠ 0 ∧ d ∣ n) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_Icc, Finset.mem_range]
    omega
  rw [hset]
  exact Nat.card_multiples' N d

lemma largeSquareDivisorsUpTo_card_le_sum (N D : ℕ) :
    (largeSquareDivisorsUpTo N D).card ≤ ∑ d ∈ Finset.Icc D N, N / d ^ 2 := by
  have hset : largeSquareDivisorsUpTo N D =
      (Finset.Icc D N).biUnion (fun d => (Finset.Icc 1 N).filter fun n => d ^ 2 ∣ n) := by
    ext n
    simp only [largeSquareDivisorsUpTo, Finset.mem_filter, Finset.mem_biUnion]
    aesop
  rw [hset]
  exact Finset.card_biUnion_le.trans_eq (by simp_rw [card_positive_multiples])

theorem largeSquareDivisorsUpTo_card_le {N D : ℕ} (hD : 1 ≤ D) :
    ((largeSquareDivisorsUpTo N D).card : ℝ) ≤ 2 * N / D := by
  have hsum : (∑ d ∈ Finset.Icc D N, ((d : ℝ) ^ 2)⁻¹) ≤ 2 / (D : ℝ) := by
    have hset : Finset.Icc D N = Finset.Ioo (D - 1) (N + 1) := by
      ext d
      simp only [Finset.mem_Icc, Finset.mem_Ioo]
      omega
    rw [hset]
    have h := sum_Ioo_inv_sq_le (α := ℝ) (D - 1) (N + 1)
    have hcast : ((D - 1 : ℕ) : ℝ) + 1 = D := by exact_mod_cast (by omega : D - 1 + 1 = D)
    rwa [hcast] at h
  calc
    ((largeSquareDivisorsUpTo N D).card : ℝ) ≤
        ∑ d ∈ Finset.Icc D N, ((N / d ^ 2 : ℕ) : ℝ) := by
      exact_mod_cast largeSquareDivisorsUpTo_card_le_sum N D
    _ ≤ ∑ d ∈ Finset.Icc D N, (N : ℝ) * ((d : ℝ) ^ 2)⁻¹ := by
      apply Finset.sum_le_sum
      intro d hd
      have hdpos : 0 < d := by have := (Finset.mem_Icc.mp hd).1; omega
      rw [← div_eq_mul_inv]
      apply (le_div_iff₀ (pow_pos (show (0 : ℝ) < d by exact_mod_cast hdpos) 2)).mpr
      exact_mod_cast Nat.div_mul_le_self N (d ^ 2)
    _ = (N : ℝ) * ∑ d ∈ Finset.Icc D N, ((d : ℝ) ^ 2)⁻¹ := (Finset.mul_sum ..).symm
    _ ≤ (N : ℝ) * (2 / D) := mul_le_mul_of_nonneg_left hsum (Nat.cast_nonneg N)
    _ = _ := by ring

noncomputable def squareNeighborhoodsUpTo (N W D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => ∃ a ∈ largeSquareDivisorsUpTo (2 * N) D,
    a ≤ n + W ∧ n ≤ a + W

lemma squareNeighborhoodsUpTo_card_le (N W D : ℕ) :
    (squareNeighborhoodsUpTo N W D).card ≤
      (2 * W + 1) * (largeSquareDivisorsUpTo (2 * N) D).card := by
  classical
  have hsub : squareNeighborhoodsUpTo N W D ⊆
      (largeSquareDivisorsUpTo (2 * N) D).biUnion fun a => Finset.Icc (a - W) (a + W) := by
    intro n hn
    simp only [squareNeighborhoodsUpTo, Finset.mem_filter] at hn
    obtain ⟨_, a, ha, hlo, hhi⟩ := hn
    exact Finset.mem_biUnion.mpr ⟨a, ha, Finset.mem_Icc.mpr ⟨by omega, hhi⟩⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ ∑ a ∈ largeSquareDivisorsUpTo (2 * N) D, (Finset.Icc (a - W) (a + W)).card :=
      Finset.card_biUnion_le
    _ ≤ ∑ _ ∈ largeSquareDivisorsUpTo (2 * N) D, (2 * W + 1) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Nat.card_Icc]
      omega
    _ = _ := by simp [mul_comm]

theorem squareNeighborhoodsUpTo_card_bound {N W D : ℕ} (hD : 1 ≤ D) :
    ((squareNeighborhoodsUpTo N W D).card : ℝ) ≤ (8 * W + 4 : ℝ) * N / D := by
  have h₁ := squareNeighborhoodsUpTo_card_le N W D
  have h₂ := largeSquareDivisorsUpTo_card_le (N := 2 * N) hD
  calc
    ((squareNeighborhoodsUpTo N W D).card : ℝ) ≤
        (2 * W + 1 : ℝ) * (largeSquareDivisorsUpTo (2 * N) D).card := by exact_mod_cast h₁
    _ ≤ (2 * W + 1 : ℝ) * (2 * (2 * N : ℕ) / D) := by gcongr
    _ = _ := by push_cast; ring

noncomputable def badPointsWithLargeIntervalPrime (N D : ℕ) : Finset ℕ := by
  classical
  exact (Finset.Icc 1 N).filter fun n => ∃ u v : ℕ,
    BadInterval u v ∧ u ≤ n ∧ n ≤ v ∧ D ≤ intervalPrime u v

lemma badPointsWithLargeIntervalPrime_card_le {u₀ N H D : ℕ}
    (hanchor : ∀ u v : ℕ, u₀ ≤ u → BadInterval u v →
      ∃ a ∈ Finset.Icc u v, intervalPrime u v ^ 2 ∣ a ∧
        largestPrimeFactor a = intervalPrime u v) :
    (badPointsWithLargeIntervalPrime N D).card ≤
      2 * u₀ + (longBadPointsUpTo N H).card + (squareNeighborhoodsUpTo N (2 * H) D).card := by
  classical
  have hsub : badPointsWithLargeIntervalPrime N D ⊆ Finset.Icc 1 (2 * u₀) ∪
      (longBadPointsUpTo N H ∪ squareNeighborhoodsUpTo N (2 * H) D) := by
    intro n hn
    obtain ⟨hnrange, u, v, hbad, hun, hnv, hQ⟩ := Finset.mem_filter.mp hn
    obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
    by_cases hsmall : n ≤ 2 * u₀
    · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, hsmall⟩)
    apply Finset.mem_union_right
    by_cases hlong : 2 * H ≤ v - u + 1
    · apply Finset.mem_union_left
      exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩,
        u, v, hbad, hun, hnv, hlong⟩
    apply Finset.mem_union_right
    have hratio := hbad.right_lt_two_mul_left
    obtain ⟨a, ha, hdiv, _⟩ := hanchor u v (by omega) hbad
    obtain ⟨hua, hav⟩ := Finset.mem_Icc.mp ha
    have hapos : 0 < a := by have := hbad.1; omega
    have hsq : intervalPrime u v ^ 2 ≤ a := Nat.le_of_dvd hapos hdiv
    have hQa : intervalPrime u v ≤ a := by
      have hQ1 := one_le_largestPrimeFactor (intervalProduct u v)
      change 1 ≤ intervalPrime u v at hQ1
      nlinarith
    have hamem : a ∈ largeSquareDivisorsUpTo (2 * N) D := by
      apply Finset.mem_filter.mpr
      exact ⟨Finset.mem_Icc.mpr ⟨by omega, by omega⟩, intervalPrime u v,
        Finset.mem_Icc.mpr ⟨hQ, by omega⟩, hdiv⟩
    simp only [squareNeighborhoodsUpTo, Finset.mem_filter]
    exact ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, a, hamem, by omega, by omega⟩
  calc
    _ ≤ _ := Finset.card_le_card hsub
    _ ≤ (Finset.Icc 1 (2 * u₀)).card +
        (longBadPointsUpTo N H ∪ squareNeighborhoodsUpTo N (2 * H) D).card :=
      Finset.card_union_le _ _
    _ ≤ (Finset.Icc 1 (2 * u₀)).card +
        ((longBadPointsUpTo N H).card + (squareNeighborhoodsUpTo N (2 * H) D).card) :=
      Nat.add_le_add_left (Finset.card_union_le _ _) _
    _ = _ := by rw [Nat.card_Icc]; omega

theorem exists_largeIntervalPrime_card_bound : ∃ E N₀ : ℕ, ∀ N ≥ N₀,
    ∀ H D : ℕ, 0 < H → H ^ 2 ≤ 2 * N → 1 ≤ D →
      ((badPointsWithLargeIntervalPrime N D).card : ℝ) ≤
        E + 7680 * (N : ℝ) * Real.log N / H + (16 * H + 4 : ℝ) * N / D := by
  obtain ⟨u₀, hanchor⟩ := exists_badInterval_square_anchor_threshold
  obtain ⟨E, N₀, hlong⟩ := exists_longBadPoints_card_bound
  refine ⟨2 * u₀ + E, N₀, ?_⟩
  intro N hN H D hH hHN hD
  have h₁ := badPointsWithLargeIntervalPrime_card_le (N := N) (H := H) (D := D) hanchor
  have h₂ := hlong N hN H hH hHN
  have h₃ := squareNeighborhoodsUpTo_card_bound (N := N) (W := 2 * H) hD
  have h₁R : ((badPointsWithLargeIntervalPrime N D).card : ℝ) ≤
      (2 * u₀ : ℕ) + (longBadPointsUpTo N H).card +
        (squareNeighborhoodsUpTo N (2 * H) D).card := by exact_mod_cast h₁
  calc
    _ ≤ _ := h₁R
    _ ≤ ((2 * u₀ : ℕ) : ℝ) +
        (E + 7680 * (N : ℝ) * Real.log N / H) + (8 * (2 * H : ℕ) + 4 : ℝ) * N / D := by
      gcongr
    _ = _ := by push_cast; ring

end Erdos380
