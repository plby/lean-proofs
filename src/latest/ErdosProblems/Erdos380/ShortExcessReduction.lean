import ErdosProblems.Erdos380.AnchorNeighbors
import ErdosProblems.Erdos380.SquareExclusions
import ErdosProblems.Erdos380.CountComparison

/-!
# Exact reduction of the excess in short bad intervals

Every excess point differs from its square anchor. Except for an initial
segment, a cutoff boundary, ineligible anchors, and large square divisors,
the point is one of the neighbors counted by the harmonic probability bound.
-/

open scoped BigOperators Classical

namespace Erdos380

noncomputable def shortExcessPointsUpTo (N W : ℕ) : Finset ℕ :=
  (excessPointsUpTo N).filter fun n => ∃ u v : ℕ,
    BadInterval u v ∧ u ≤ n ∧ n ≤ v ∧ v - u ≤ W

noncomputable def ineligibleSingletons (N Q Y : ℕ) : Finset ℕ :=
  singletonBadUpTo N \ eligibleSingletons N Q Y

def integerNeighborhoods (S : Finset ℕ) (W : ℕ) : Finset ℕ :=
  S.biUnion fun a => Finset.Icc (a - W) (a + W)

lemma integerNeighborhoods_card_le (S : Finset ℕ) (W : ℕ) :
    (integerNeighborhoods S W).card ≤ (2 * W + 1) * S.card := by
  calc
    _ ≤ ∑ a ∈ S, (Finset.Icc (a - W) (a + W)).card := Finset.card_biUnion_le
    _ ≤ ∑ _a ∈ S, (2 * W + 1) := by
      apply Finset.sum_le_sum
      intro a _
      rw [Nat.card_Icc]
      omega
    _ = _ := by simp [mul_comm]

lemma square_divisors_small_outside_neighborhood {N W D n m : ℕ}
    (hn1 : 1 ≤ n) (hnN : n ≤ N) (hm1 : 1 ≤ m) (hmN : m ≤ 2 * N)
    (hmn : m ≤ n + W) (hnm : n ≤ m + W)
    (hnot : n ∉ squareNeighborhoodsUpTo N W (D + 1)) :
    ∀ d : ℕ, d ^ 2 ∣ m → d ≤ D := by
  intro d hd
  by_contra hlarge
  have hsq : d ^ 2 ≤ m := Nat.le_of_dvd (by omega) hd
  have hdN : d ≤ 2 * N := by nlinarith
  have hm : m ∈ largeSquareDivisorsUpTo (2 * N) (D + 1) :=
    Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hm1, hmN⟩, d,
      Finset.mem_Icc.mpr ⟨by omega, hdN⟩, hd⟩
  apply hnot
  simp only [squareNeighborhoodsUpTo, Finset.mem_filter]
  exact ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, m, hm, hmn, hnm⟩

lemma BadInterval.anchor_singletonBad {u v a : ℕ} (hbad : BadInterval u v)
    (ha : a ∈ Finset.Icc u v) (hsq : intervalPrime u v ^ 2 ∣ a)
    (hP : largestPrimeFactor a = intervalPrime u v) : SingletonBad a := by
  have ha1 : 1 ≤ a := hbad.1.trans (Finset.mem_Icc.mp ha).1
  have hp := largestPrimeFactor_prime hbad.2.2.1
  have hle := largestPrimeFactor_le_self ha1
  rw [hP] at hle
  exact ⟨hp.two_le.trans hle, by rwa [hP]⟩

lemma shortExcessPointsUpTo_subset {u₀ N W M Q T D : ℕ} {L : ℝ}
    (hanchor : ∀ u v : ℕ, u₀ ≤ u → BadInterval u v →
      ∃ a ∈ Finset.Icc u v, intervalPrime u v ^ 2 ∣ a ∧
        largestPrimeFactor a = intervalPrime u v)
    (hM : 1 ≤ M) (hL : L ≤ Real.log (M : ℝ)) :
    shortExcessPointsUpTo N W ⊆ Finset.Icc 1 (2 * u₀ + M + W) ∪
      (Finset.Icc (N - W) N ∪
      (integerNeighborhoods (ineligibleSingletons N Q (T ^ 110)) W ∪
      (squareNeighborhoodsUpTo N W (D + 1) ∪ goodAnchorNeighbors N Q T W D L))) := by
  intro n hn
  obtain ⟨hnexcess, u, v, hbad, hun, hnv, hwidth⟩ := Finset.mem_filter.mp hn
  obtain ⟨hnbad, hnnot⟩ := Finset.mem_sdiff.mp hnexcess
  obtain ⟨hn1, hnN, _⟩ := mem_badPointsUpTo.mp hnbad
  by_cases hsmall : n ≤ 2 * u₀ + M + W
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hn1, hsmall⟩)
  apply Finset.mem_union_right
  by_cases hboundary : N - W ≤ n
  · exact Finset.mem_union_left _ (Finset.mem_Icc.mpr ⟨hboundary, hnN⟩)
  apply Finset.mem_union_right
  have hratio := hbad.right_lt_two_mul_left
  have huv := hbad.2.1
  have hu₀ : u₀ ≤ u := by omega
  have huM : M ≤ u := by omega
  obtain ⟨a, ha, hsq, hP⟩ := hanchor u v hu₀ hbad
  obtain ⟨hua, hav⟩ := Finset.mem_Icc.mp ha
  have ha1 : 1 ≤ a := hbad.1.trans hua
  have haN : a ≤ N := by omega
  have haBad := hbad.anchor_singletonBad ha hsq hP
  have haSingleton : a ∈ singletonBadUpTo N := mem_singletonBadUpTo.mpr ⟨ha1, haN, haBad⟩
  by_cases haEligible : a ∈ eligibleSingletons N Q (T ^ 110)
  · apply Finset.mem_union_right
    by_cases hsquare : n ∈ squareNeighborhoodsUpTo N W (D + 1)
    · exact Finset.mem_union_left _ hsquare
    apply Finset.mem_union_right
    have han : a ≠ n := by intro heq; exact hnnot (heq ▸ haSingleton)
    have htop : intervalPrime u v ≤ T ^ 110 := by
      rw [← hP]
      exact (mem_eligibleSingletons.mp haEligible).2.2.2.2
    have hregular (m : ℕ) (hm : m ∈ Finset.Icc u v) :
        0 < m ∧ largestPrimeFactor m ≤ T ^ 110 ∧
          (∀ d : ℕ, d ^ 2 ∣ m → d ≤ D) ∧ L ≤ Real.log m := by
      obtain ⟨hum, hmv⟩ := Finset.mem_Icc.mp hm
      have hm1 : 1 ≤ m := hbad.1.trans hum
      exact ⟨by omega, (largestPrimeFactor_le_intervalPrime hbad.1 hm).trans htop,
        square_divisors_small_outside_neighborhood hn1 hnN hm1 (by omega) (by omega) (by omega) hsquare,
        hL.trans (Real.log_le_log (by exact_mod_cast (by omega : 0 < M)) (by exact_mod_cast huM.trans hum))⟩
    apply Finset.mem_biUnion.mpr
    rcases lt_or_gt_of_ne han with hal | hna
    · let H := n - a
      have hH : 1 ≤ H ∧ H ≤ W := by dsimp [H]; omega
      refine ⟨H, Finset.mem_Icc.mpr hH, Finset.mem_union_left _ ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨haEligible, ?_⟩, by dsimp [H]; omega⟩
      intro j
      let m := a + (j.val + 1)
      have hj := j.isLt
      have hm : m ∈ Finset.Icc u v := by dsimp [m, H] at *; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨hmpos, hmsmooth, hmsq, hmlog⟩ := hregular m hm
      refine ⟨m, hmpos, ?_, hmsmooth, hmsq, hmlog⟩
      simp [m, signedShift, Nat.cast_add]
    · let H := a - n
      have hH : 1 ≤ H ∧ H ≤ W := by dsimp [H]; omega
      refine ⟨H, Finset.mem_Icc.mpr hH, Finset.mem_union_right _ ?_⟩
      apply Finset.mem_image.mpr
      refine ⟨a, Finset.mem_filter.mpr ⟨haEligible, ?_⟩, by dsimp [H]; omega⟩
      intro j
      let m := a - (j.val + 1)
      have hj := j.isLt
      have hja : j.val + 1 ≤ a := by dsimp [H] at hj; omega
      have hm : m ∈ Finset.Icc u v := by dsimp [m, H] at *; exact Finset.mem_Icc.mpr ⟨by omega, by omega⟩
      obtain ⟨hmpos, hmsmooth, hmsq, hmlog⟩ := hregular m hm
      refine ⟨m, hmpos, ?_, hmsmooth, hmsq, hmlog⟩
      simp [m, signedShift, Nat.cast_sub hja, Nat.cast_add, sub_eq_add_neg]
  · apply Finset.mem_union_left
    exact Finset.mem_biUnion.mpr ⟨a, Finset.mem_sdiff.mpr ⟨haSingleton, haEligible⟩,
      Finset.mem_Icc.mpr ⟨by omega, by omega⟩⟩

theorem exists_shortExcess_card_reduction : ∃ E : ℕ, ∀ N W M Q T D : ℕ, ∀ L : ℝ,
    1 ≤ M → L ≤ Real.log (M : ℝ) →
    (shortExcessPointsUpTo N W).card ≤ E + M + 2 * W +
      (2 * W + 1) * (ineligibleSingletons N Q (T ^ 110)).card +
      (squareNeighborhoodsUpTo N W (D + 1)).card + (goodAnchorNeighbors N Q T W D L).card := by
  obtain ⟨u₀, hanchor⟩ := exists_badInterval_square_anchor_threshold
  refine ⟨2 * u₀ + 1, ?_⟩
  intro N W M Q T D L hM hL
  have hsub := shortExcessPointsUpTo_subset (N := N) (W := W) (Q := Q) (T := T) (D := D) hanchor hM hL
  have hc := Finset.card_le_card hsub
  have h₁ := Finset.card_union_le (Finset.Icc 1 (2 * u₀ + M + W))
    (Finset.Icc (N - W) N ∪ (integerNeighborhoods (ineligibleSingletons N Q (T ^ 110)) W ∪
      (squareNeighborhoodsUpTo N W (D + 1) ∪ goodAnchorNeighbors N Q T W D L)))
  have h₂ := Finset.card_union_le (Finset.Icc (N - W) N)
    (integerNeighborhoods (ineligibleSingletons N Q (T ^ 110)) W ∪
      (squareNeighborhoodsUpTo N W (D + 1) ∪ goodAnchorNeighbors N Q T W D L))
  have h₃ := Finset.card_union_le (integerNeighborhoods (ineligibleSingletons N Q (T ^ 110)) W)
    (squareNeighborhoodsUpTo N W (D + 1) ∪ goodAnchorNeighbors N Q T W D L)
  have h₄ := Finset.card_union_le (squareNeighborhoodsUpTo N W (D + 1)) (goodAnchorNeighbors N Q T W D L)
  have hnear := integerNeighborhoods_card_le (ineligibleSingletons N Q (T ^ 110)) W
  have hinit : (Finset.Icc 1 (2 * u₀ + M + W)).card = 2 * u₀ + M + W := by simp
  have hboundary : (Finset.Icc (N - W) N).card ≤ W + 1 := by rw [Nat.card_Icc]; omega
  omega

/-- The complete finite short-interval estimate, normalized at the original
cutoff. Only the ineligible singleton count and parameter estimates remain
to be bounded asymptotically. -/
theorem exists_shortExcess_normalized_bound :
    ∃ C K U₀ : ℝ, 0 < C ∧ 0 < K ∧ 0 < U₀ ∧ ∃ E T₀ d₀ P₀ : ℕ,
      ∀ T ≥ T₀, ∀ N R Q : ℕ, 1 ≤ N → 1 < R → 2 ≤ Q → 2 ^ d₀ < Q →
      2 * T ^ 90 ≤ Q → max P₀ (128 * primeBoxEnlargement 10 * R) ≤ Q →
      ∀ W : ℕ, 0 < W → W ≤ T → (W : ℝ) * (C * (Real.log T ^ 5 / (T : ℝ))) ≤ 1 →
      ∀ D M : ℕ, 0 < D → 1 ≤ M → ∀ U L : ℝ, U₀ ≤ U → (W : ℝ) ≤ U ^ 48 →
      2 * Real.log D + Real.log W + 111 * U * Real.log T ≤ L → L ≤ Real.log (M : ℝ) →
      ((shortExcessPointsUpTo N W).card : ℝ) ≤ E + M + 2 * W +
        (2 * W + 1 : ℝ) * (ineligibleSingletons N Q (T ^ 110)).card +
        (8 * W + 4 : ℝ) * N / (D + 1) +
        K * (1 + Real.log W) * (Real.log (N : ℝ) / Real.log (R : ℝ)) *
          (singletonBadUpTo N).card / U ^ 2 := by
  obtain ⟨E, hred⟩ := exists_shortExcess_card_reduction
  obtain ⟨C, K, U₀, hC, hK, hU₀, T₀, d₀, P₀, hbound⟩ := exists_uniform_goodAnchorNeighbors_bound
  refine ⟨C, K, U₀, hC, hK, hU₀, E, T₀, d₀, P₀, ?_⟩
  intro T hT N R Q hN hR hQ hdQ hTQ hPQ W hW hWT hmix D M hD hM U L hU hWU hL hLM
  have h₁ := hred N W M Q T D L hM hLM
  have h₂ := squareNeighborhoodsUpTo_card_bound (N := N) (W := W) (by omega : 1 ≤ D + 1)
  have h₃ := hbound T hT N R Q hN hR hQ hdQ hTQ hPQ W hW hWT hmix D hD U L hU hWU hL
  have h₁R : ((shortExcessPointsUpTo N W).card : ℝ) ≤ E + M + 2 * W +
      (2 * W + 1 : ℝ) * (ineligibleSingletons N Q (T ^ 110)).card +
      (squareNeighborhoodsUpTo N W (D + 1)).card + (goodAnchorNeighbors N Q T W D L).card := by
    exact_mod_cast h₁
  have h₂' : ((squareNeighborhoodsUpTo N W (D + 1)).card : ℝ) ≤ (8 * W + 4 : ℝ) * N / (D + 1) := by
    simpa only [Nat.cast_add, Nat.cast_one] using h₂
  linarith

end Erdos380
