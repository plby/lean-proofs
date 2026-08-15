import ErdosProblems.Erdos448.Prop3ShiftedMean448

open Finset
open scoped BigOperators

namespace FirstShiftedSmall448

lemma ceilDiv_mul (x q t : ℕ) (hq : 0 < q) (ht : 0 < t) :
    (x ⌈/⌉ q) ⌈/⌉ t = x ⌈/⌉ (q * t) := by
  apply le_antisymm
  · rw [ceilDiv_le_iff_le_mul ht, ceilDiv_le_iff_le_mul hq]
    have hunit : x ≤ (q * t) * (x ⌈/⌉ (q * t)) :=
      (ceilDiv_le_iff_le_mul (Nat.mul_pos hq ht)).1 le_rfl
    simpa [mul_assoc] using hunit
  · rw [ceilDiv_le_iff_le_mul (Nat.mul_pos hq ht)]
    have hqceil : x ≤ q * (x ⌈/⌉ q) :=
      (ceilDiv_le_iff_le_mul hq).1 le_rfl
    have htceil : x ⌈/⌉ q ≤ t * ((x ⌈/⌉ q) ⌈/⌉ t) :=
      (ceilDiv_le_iff_le_mul ht).1 le_rfl
    calc
      x ≤ q * (x ⌈/⌉ q) := hqceil
      _ ≤ q * (t * ((x ⌈/⌉ q) ⌈/⌉ t)) :=
        Nat.mul_le_mul_left q htceil
      _ = (q * t) * ((x ⌈/⌉ q) ⌈/⌉ t) := by ring

lemma one_div_card_divisors_le_sharpWeight {q : ℕ} (hq : q ≠ 0) :
    (1 : ℝ) / (q.divisors.card : ℝ) ≤
      Prop3ShiftedMean448.sharpShiftedReciprocalWeight q := by
  rw [Prop3ShiftedMean448.sharpShiftedReciprocalWeight, if_neg hq]
  have hprod : (1 : ℝ) ≤
      ∏ p ∈ q.primeFactors, Prop3ShiftedMean448.sharpLocalCorrection p := by
    exact Finset.one_le_prod fun p hp ↦
      Prop3ShiftedMean448.one_le_sharpLocalCorrection
        (Nat.prime_of_mem_primeFactors hp)
  have hdiv : 0 ≤ (1 : ℝ) / (q.divisors.card : ℝ) := by positivity
  calc
    (1 : ℝ) / (q.divisors.card : ℝ) =
        (1 / (q.divisors.card : ℝ)) * 1 := by ring
    _ ≤ (1 / (q.divisors.card : ℝ)) *
        ∏ p ∈ q.primeFactors,
          Prop3ShiftedMean448.sharpLocalCorrection p :=
      mul_le_mul_of_nonneg_left hprod hdiv

/-- A first-shifted bound retaining the multiplicative shift weight even
for the one- or two-point cutoff. -/
noncomputable def weightedFirstShiftedBoundAll
    (x q : ℕ) : ℝ :=
  if 3 ≤ x ⌈/⌉ q then
    Prop3ShiftedMean448.shiftedReciprocalMeanConstant *
        ((x ⌈/⌉ q : ℕ) : ℝ) *
      Prop3ShiftedMean448.sharpShiftedReciprocalWeight q /
        Real.sqrt (Real.log (2 * ((x ⌈/⌉ q : ℕ) : ℝ)))
  else Prop3ShiftedMean448.sharpShiftedReciprocalWeight q

theorem shifted_reciprocal_sum_le_weightedFirstShiftedBoundAll
    {x q : ℕ} (hq : 0 < q) :
    (∑ m ∈ (Finset.range x).filter (fun m ↦ q * m < x),
      1 / ((q * m).divisors.card : ℝ)) ≤
      weightedFirstShiftedBoundAll x q := by
  by_cases hlarge : 3 ≤ x ⌈/⌉ q
  · rw [weightedFirstShiftedBoundAll, if_pos hlarge]
    exact Prop3ShiftedMean448.shifted_reciprocal_divisor_mean_sharp_mul_cutoff
      q q x hq hlarge
  · rw [weightedFirstShiftedBoundAll, if_neg hlarge]
    have hz : x ⌈/⌉ q < 3 := Nat.lt_of_not_ge hlarge
    have hsub : (Finset.range x).filter (fun m ↦ q * m < x) ⊆
        Finset.range (x ⌈/⌉ q) := by
      intro m hm
      exact (Prop3ShiftedMean448.mem_range_ceilDiv_iff_mul_lt hq).2
        (Finset.mem_filter.mp hm).2
    have hsmall : (Finset.range x).filter (fun m ↦ q * m < x) ⊆ {0, 1} := by
      intro m hm
      have hmz := Finset.mem_range.mp (hsub hm)
      simp only [Finset.mem_insert, Finset.mem_singleton]
      omega
    calc
      (∑ m ∈ (Finset.range x).filter (fun m ↦ q * m < x),
          1 / ((q * m).divisors.card : ℝ)) ≤
          ∑ m ∈ ({0, 1} : Finset ℕ),
            1 / ((q * m).divisors.card : ℝ) := by
        apply Finset.sum_le_sum_of_subset_of_nonneg hsmall
        intro m hm hnot
        positivity
      _ = 1 / (q.divisors.card : ℝ) := by
        simp [hq]
      _ ≤ Prop3ShiftedMean448.sharpShiftedReciprocalWeight q :=
        one_div_card_divisors_le_sharpWeight hq.ne'

end FirstShiftedSmall448
