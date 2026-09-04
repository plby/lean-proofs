import ErdosProblems.Erdos380.SieveOrder
import ErdosProblems.Erdos380.ShortExcessReduction

/-! # A single smoothness cutoff for all nonshort intervals -/

namespace Erdos380

lemma smoothRunStarts_subset_unit_survivors (N H T : ℕ) :
    letI : ∀ q : dyadicPrimes T, NeZero q.1 :=
      fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
    smoothRunStarts N H T ⊆
      residueClassSurvivors (fun q : dyadicPrimes T => unitShiftResidues (1 : (ZMod q.1)ˣ) H) 0 N := by
  classical
  let : ∀ q : dyadicPrimes T, NeZero q.1 :=
    fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
  intro n hn
  obtain ⟨hnrange, hsmooth⟩ := Finset.mem_filter.mp hn
  obtain ⟨hn1, hnN⟩ := Finset.mem_Icc.mp hnrange
  apply Finset.mem_filter.mpr
  refine ⟨Finset.mem_Ioc.mpr ⟨by omega, by omega⟩, ?_⟩
  intro q hres
  obtain ⟨j, hj, hz⟩ := (mem_unitShiftResidues_iff (1 : (ZMod q.1)ˣ)).mp hres
  have hzero : ((n + j : ℕ) : ZMod q.1) = 0 := by
    simpa only [Units.val_one, one_mul, Nat.cast_add] using hz
  have hdiv := (ZMod.natCast_eq_zero_iff (n + j) q.1).mp hzero
  have hle := (prime_le_largestPrimeFactor (by omega : n + j ≠ 0)
    (Finset.mem_filter.mp q.2).2 hdiv).trans (hsmooth j hj)
  exact (not_le_of_gt (Finset.mem_Ioc.mp (Finset.mem_filter.mp q.2).1).1) hle

theorem exists_uniform_smoothRunStarts_highOrder_bound : ∃ T₀ : ℕ, ∀ T ≥ T₀,
    ∀ k H : ℕ, 0 < k → 0 < H → H ≤ T → 20 * (k : ℝ) * Real.log T ≤ T →
    ∀ N : ℕ, (2 * T) ^ (2 * k) ≤ N →
      ((smoothRunStarts N H T).card : ℝ) ≤
        ((N : ℝ) + N) / (((H : ℝ) / (40 * k * Real.log T)) ^ k) := by
  obtain ⟨T₀, hbound⟩ := exists_uniform_dyadicShiftSieve_bound
  refine ⟨T₀, ?_⟩
  intro T hT k H hk hH hHT hkT N hpower
  let : ∀ q : dyadicPrimes T, NeZero q.1 :=
    fun q => ⟨(Finset.mem_filter.mp q.2).2.ne_zero⟩
  have h := hbound T hT k H hk hH hHT hkT 0 N hpower (fun _ => 1)
  exact (show ((smoothRunStarts N H T).card : ℝ) ≤
    (residueClassSurvivors (fun q : dyadicPrimes T => unitShiftResidues (1 : (ZMod q.1)ˣ) H) 0 N).card by
      exact_mod_cast Finset.card_le_card (smoothRunStarts_subset_unit_survivors N H T)).trans h

lemma excessPointsUpTo_subset_short_large_runs {N W H T : ℕ} (hH : 0 < H) (hHW : 2 * H ≤ W + 1) :
    excessPointsUpTo N ⊆ shortExcessPointsUpTo N W ∪
      (badPointsWithLargeIntervalPrime N T ∪
        (smoothRunStarts N H T ∪ (smoothRunStarts N H T).image (fun a => a + H - 1))) := by
  classical
  intro n hn
  by_cases hshort : n ∈ shortExcessPointsUpTo N W
  · exact Finset.mem_union_left _ hshort
  apply Finset.mem_union_right
  have hnB := (Finset.mem_sdiff.mp hn).1
  obtain ⟨hn1, hnN, u, v, hbad, hun, hnv⟩ := mem_badPointsUpTo.mp hnB
  have hlen : W < v - u := by
    by_contra h
    exact hshort (Finset.mem_filter.mpr ⟨hn, u, v, hbad, hun, hnv, by omega⟩)
  by_cases hlarge : T ≤ intervalPrime u v
  · apply Finset.mem_union_left
    exact Finset.mem_filter.mpr ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, u, v, hbad, hun, hnv, hlarge⟩
  apply Finset.mem_union_right
  have hQT : intervalPrime u v ≤ T := by omega
  have hsmooth : ∀ m ∈ Finset.Icc u v, largestPrimeFactor m ≤ T := by
    intro m hm
    exact (largestPrimeFactor_mono_dvd (intervalProduct_pos hbad.1).ne' (dvd_intervalProduct hm)).trans hQT
  by_cases hright : n + H - 1 ≤ v
  · apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    refine ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, ?_⟩
    intro j hj
    have hjH := Finset.mem_range.mp hj
    exact hsmooth (n + j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)
  · apply Finset.mem_union_right
    apply Finset.mem_image.mpr
    refine ⟨n + 1 - H, ?_, by omega⟩
    apply Finset.mem_filter.mpr
    have hleft : u ≤ n + 1 - H := by omega
    refine ⟨Finset.mem_Icc.mpr ⟨by have := hbad.1; omega, by omega⟩, ?_⟩
    intro j hj
    have hjH := Finset.mem_range.mp hj
    exact hsmooth (n + 1 - H + j) (Finset.mem_Icc.mpr ⟨by omega, by omega⟩)

theorem excessPointsUpTo_card_le_short_large_runs {N W H T : ℕ}
    (hH : 0 < H) (hHW : 2 * H ≤ W + 1) :
    (excessPointsUpTo N).card ≤ (shortExcessPointsUpTo N W).card +
      (badPointsWithLargeIntervalPrime N T).card + 2 * (smoothRunStarts N H T).card := by
  have h := Finset.card_le_card (excessPointsUpTo_subset_short_large_runs (N := N) (T := T) hH hHW)
  have h₁ := Finset.card_union_le (shortExcessPointsUpTo N W)
    (badPointsWithLargeIntervalPrime N T ∪
      (smoothRunStarts N H T ∪ (smoothRunStarts N H T).image (fun a => a + H - 1)))
  have h₂ := Finset.card_union_le (badPointsWithLargeIntervalPrime N T)
    (smoothRunStarts N H T ∪ (smoothRunStarts N H T).image (fun a => a + H - 1))
  have h₃ := Finset.card_union_le (smoothRunStarts N H T)
    ((smoothRunStarts N H T).image (fun a => a + H - 1))
  have himage : ((smoothRunStarts N H T).image (fun a => a + H - 1)).card ≤
      (smoothRunStarts N H T).card := Finset.card_image_le
  omega

end Erdos380
