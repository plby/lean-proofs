import ErdosProblems.Erdos380.PrimeRangeCover
import ErdosProblems.Erdos380.DeficientScale
import ErdosProblems.Erdos380.ShortExcessReduction

/-! # The exceptional singleton anchors are negligible -/

open Filter
open scoped Topology BigOperators

namespace Erdos380

lemma ineligibleSingletons_subset_from_bands (N a Q Y D : ℕ) (S : Finset ℕ)
    (hlowBand : singletonPrimeBand N a Q ⊆ S) (hhighBand : singletonPrimeBand N Y D ⊆ S) :
    ineligibleSingletons N Q Y ⊆ Nat.smoothNumbersUpTo N (a + 1) ∪
      (S ∪ (largeSquareDivisorsUpTo N D ∪ cofactorDeficientSingletons N Q Y 9)) := by
  classical
  intro n hn
  simp only [ineligibleSingletons, Finset.mem_sdiff] at hn
  have hnA : n ∈ singletonBadUpTo N := hn.1
  have hnot : n ∉ eligibleSingletons N Q Y := hn.2
  simp only [eligibleSingletons, Finset.mem_filter] at hnot
  have hn1 : 1 ≤ n := (mem_singletonBadUpTo.mp hnA).1
  have hnN : n ≤ N := (mem_singletonBadUpTo.mp hnA).2.1
  have hbad : SingletonBad n := (mem_singletonBadUpTo.mp hnA).2.2
  have hP1 := one_le_largestPrimeFactor n
  have hnot' : ¬ (Q ≤ topPrime (singletonCofactor n) 9 ∧ largestPrimeFactor n ≤ Y) := by
    intro h
    exact hnot ⟨hnA, h⟩
  by_cases hsmall : largestPrimeFactor n ≤ a
  · apply Finset.mem_union_left
    exact Nat.mem_smoothNumbersUpTo.mpr ⟨hnN,
      (mem_smoothNumbers_iff_largestPrimeFactor (hP1.trans hsmall)).mpr ⟨by omega, hsmall⟩⟩
  apply Finset.mem_union_right
  have hsmall' : a < largestPrimeFactor n := by omega
  by_cases hlow : largestPrimeFactor n ≤ Q
  · exact Finset.mem_union_left _ (hlowBand (Finset.mem_filter.mpr ⟨hnA, hsmall', hlow⟩))
  by_cases hupper : largestPrimeFactor n ≤ Y
  · apply Finset.mem_union_right
    apply Finset.mem_union_right
    have hthin : topPrime (singletonCofactor n) 9 < Q := by omega
    exact Finset.mem_filter.mpr ⟨hnA, by omega, hupper, hthin⟩
  have hupper' : Y < largestPrimeFactor n := by omega
  by_cases hlarge : largestPrimeFactor n ≤ D
  · exact Finset.mem_union_left _ (hhighBand (Finset.mem_filter.mpr ⟨hnA, hupper', hlarge⟩))
  · apply Finset.mem_union_right
    apply Finset.mem_union_left
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_Icc.mpr ⟨hn1, hnN⟩, largestPrimeFactor n,
      Finset.mem_Icc.mpr ⟨by omega, (largestPrimeFactor_le_self hn1).trans hnN⟩, hbad.2⟩

lemma ineligibleSingletons_scale_subset (N : ℕ) :
    ineligibleSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) ⊆
      Nat.smoothNumbersUpTo N (scaleBase N ^ 490 + 1) ∪
        (exceptionalPrimeBandSingletons N ∪
          (largeSquareDivisorsUpTo N (scaleBase N ^ 2005) ∪
            cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9)) :=
  ineligibleSingletons_subset_from_bands N (scaleBase N ^ 490) (scaleBase N ^ 920)
    (scaleBase N ^ 1100) (scaleBase N ^ 2005) (exceptionalPrimeBandSingletons N)
    (singletonPrimeBand_power_subset_exceptional N 490 920 (fun _ hj => Finset.mem_union_left _ hj))
    (singletonPrimeBand_power_subset_exceptional N 1100 2005 (fun _ hj => Finset.mem_union_right _ hj))

lemma ineligibleSingletons_scale_card_reduction (N : ℕ) :
    (ineligibleSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100)).card ≤
      smoothCount N (scaleBase N ^ 490) + (exceptionalPrimeBandSingletons N).card +
        (largeSquareDivisorsUpTo N (scaleBase N ^ 2005)).card +
          (cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9).card := by
  have h := Finset.card_le_card (ineligibleSingletons_scale_subset N)
  have h₁ := Finset.card_union_le (Nat.smoothNumbersUpTo N (scaleBase N ^ 490 + 1))
    (exceptionalPrimeBandSingletons N ∪
      (largeSquareDivisorsUpTo N (scaleBase N ^ 2005) ∪
        cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9))
  have h₂ := Finset.card_union_le (exceptionalPrimeBandSingletons N)
    (largeSquareDivisorsUpTo N (scaleBase N ^ 2005) ∪
      cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9)
  have h₃ := Finset.card_union_le (largeSquareDivisorsUpTo N (scaleBase N ^ 2005))
    (cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9)
  unfold smoothCount
  omega

theorem eventually_ineligibleSingletons_scale_bound : ∀ᶠ N : ℕ in atTop,
    ((ineligibleSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100)).card : ℝ) ≤
      (N : ℝ) / (scaleBase N : ℝ) ^ 2004 := by
  let C : ℕ := 2 * exceptionalPrimeBands.card + 4
  filter_upwards [eventually_smoothCount_scale_upper (k := 490) (r := 2040) (by norm_num) (by norm_num) 0,
    eventually_exceptionalPrimeBandSingletons_bound, eventually_cofactorDeficientSingletons_scale_bound,
    scaleBase_tendsto_atTop.eventually (eventually_ge_atTop C)] with N hsmooth hbands hthin hC
  have hS1 := one_le_scaleBase N
  have hS1R : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast hS1
  have hSpos : (0 : ℝ) < scaleBase N := by linarith
  have hsmall := hsmooth N le_rfl (by simp only [pow_zero, mul_one, le_refl])
  have hsmall' : (smoothCount N (scaleBase N ^ 490) : ℝ) ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2005 :=
    hsmall.trans (div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos hSpos 2005)
      (pow_le_pow_right₀ hS1R (by decide : 2005 ≤ 2040)))
  have hlarge := largeSquareDivisorsUpTo_card_le (N := N) (D := scaleBase N ^ 2005) (one_le_pow₀ hS1)
  rw [Nat.cast_pow] at hlarge
  have hred : ((ineligibleSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100)).card : ℝ) ≤
      smoothCount N (scaleBase N ^ 490) + (exceptionalPrimeBandSingletons N).card +
        (largeSquareDivisorsUpTo N (scaleBase N ^ 2005)).card +
          (cofactorDeficientSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100) 9).card := by
    exact_mod_cast ineligibleSingletons_scale_card_reduction N
  have hsum : ((ineligibleSingletons N (scaleBase N ^ 920) (scaleBase N ^ 1100)).card : ℝ) ≤
      (C : ℝ) * N / (scaleBase N : ℝ) ^ 2005 := by
    calc
      _ ≤ _ := hred
      _ ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2005 +
          (2 * exceptionalPrimeBands.card : ℝ) * N / (scaleBase N : ℝ) ^ 2005 +
          2 * N / (scaleBase N : ℝ) ^ 2005 + (N : ℝ) / (scaleBase N : ℝ) ^ 2005 :=
        add_le_add (add_le_add (add_le_add hsmall' hbands) hlarge) hthin
      _ = _ := by dsimp [C]; push_cast; ring
  apply hsum.trans
  calc
    (C : ℝ) * N / (scaleBase N : ℝ) ^ 2005 ≤
        (scaleBase N : ℝ) * N / (scaleBase N : ℝ) ^ 2005 := by
      gcongr
    _ = (N : ℝ) / (scaleBase N : ℝ) ^ 2004 := by
      rw [show 2005 = 2004 + 1 from rfl, pow_succ]
      field_simp

theorem eventually_ineligibleSingletons_parameter_bound : ∀ᶠ N : ℕ in atTop,
    ((ineligibleSingletons N (cofactorScale N) (mixingBase N ^ 110)).card : ℝ) ≤
      (N : ℝ) / (scaleBase N : ℝ) ^ 2004 := by
  filter_upwards [eventually_ineligibleSingletons_scale_bound] with N hN
  change ((ineligibleSingletons N (scaleBase N ^ 920) ((scaleBase N ^ 10) ^ 110)).card : ℝ) ≤ _
  rw [← pow_mul]
  exact hN

end Erdos380
