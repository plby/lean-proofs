/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos822.PrimeSquareSieve

/-! # A one-prime progression sieve with bounded modulus prime mass -/

namespace Erdos822

open scoped BigOperators Classical

theorem slopeReciprocalMass_self_le_full {d z y : ℕ} (hd : d ≠ 0) :
    slopeReciprocalMass d d z y ≤ primeDivisorReciprocalMass d := by
  unfold slopeReciprocalMass primeDivisorReciprocalMass
  simp only [or_self]
  rw [← Finset.sum_filter]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro p hp
    obtain ⟨hp, hpd⟩ := Finset.mem_filter.mp hp
    exact Nat.mem_primeFactors.mpr ⟨(Erdos851.mem_sievePrimes.mp hp).2.2, hpd, hd⟩
  · intro p hp hnot
    positivity

theorem slopePrimeLoss_self_le_exp_full {d z y : ℕ} (hd : d ≠ 0) (hz : 2 ≤ z) :
    slopePrimeLoss 0 d d z y ≤ Real.exp (6 * primeDivisorReciprocalMass d) :=
  (slopePrimeLoss_le_exp_slopeReciprocalMass 0 d d z y hz).trans
    (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left (slopeReciprocalMass_self_le_full hd) (by norm_num)))

theorem exists_fixed_depth_boundedMass_duplicateCandidates_bound :
    ∃ S : ℕ, 101 ≤ S ∧ ∀ C : ℝ, ∃ D : ℝ, 0 < D ∧
      ∀ d q X y : ℕ, 0 < d → primeDivisorReciprocalMass d ≤ C →
        q.Prime → y < q → 2 ≤ y →
        ((twoAffinePrimeCandidates d q d q X y).card : ℝ) ≤
          (X : ℝ) * (D / Real.log (y : ℝ)) + ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨A, hA, hpair⟩ := exists_twoAffinePrimeCandidates_slopeAware_pair_bound
  obtain ⟨M, hM, hMertens⟩ := exists_oneShift_localEulerProduct_upper
  obtain ⟨T : ℕ, hT⟩ := exists_nat_gt (99 * Real.log A / 4)
  let S := max 101 (T + 100)
  have hS : 101 ≤ S := le_max_left _ _
  have hTS : T ≤ S - 100 := by dsimp [S]; omega
  have hlog : Real.log A ≤ 4 * (S - 100 : ℕ) / 99 := by
    have hTSR : (T : ℝ) ≤ (S - 100 : ℕ) := by exact_mod_cast hTS
    linarith only [hT, hTSR]
  refine ⟨S, hS, ?_⟩
  intro C
  let eta : ℝ := (4 * A / 3) * (1 / 4 : ℝ) ^ (S - 100)
  let D : ℝ := (1 + eta) * M * Real.log 2 * Real.exp (6 * C)
  have hApos : 0 < A := by linarith only [hA]
  have heta : 0 ≤ eta := by dsimp [eta]; positivity
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hD : 0 < D := by dsimp [D]; positivity
  refine ⟨D, hD, ?_⟩
  intro d q X y hd hmass hq hyq hy
  have hbound := hpair d d q q X 2 y S hq hq hyq hyq
    (by norm_num) (by omega) (by omega) hS hlog
  dsimp only at hbound
  have hdet : affineDetNat d q d q = 0 := by simp [affineDetNat]
  rw [hdet, localEulerProduct_pairShift_zero_eq_oneShift] at hbound
  have hV := hMertens 2 y (by norm_num) (by omega)
  have hL : slopePrimeLoss 0 d d 2 y ≤ Real.exp (6 * C) :=
    (slopePrimeLoss_self_le_exp_full hd.ne' (by norm_num)).trans
      (Real.exp_le_exp.mpr (mul_le_mul_of_nonneg_left hmass (by norm_num)))
  have hL0 : 0 ≤ slopePrimeLoss 0 d d 2 y := by
    unfold slopePrimeLoss
    apply Finset.prod_nonneg
    intro p hp
    split_ifs
    · exact inv_nonneg.mpr (Erdos851.pairShift_localFactor_pos
        (Erdos851.mem_sievePrimes.mp hp).2.2 (Erdos851.mem_sievePrimes.mp hp).1).le
    · norm_num
  have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
  have hprod := mul_le_mul hV hL hL0 (show 0 ≤ M * (Real.log 2 / Real.log (y : ℝ)) by positivity)
  have hscaled := mul_le_mul_of_nonneg_left
    (mul_le_mul_of_nonneg_left hprod (show 0 ≤ 1 + eta by positivity)) (Nat.cast_nonneg (α := ℝ) X)
  refine hbound.trans ?_
  have heq : (X : ℝ) * ((1 + eta) *
      (M * (Real.log 2 / Real.log (y : ℝ)) * Real.exp (6 * C))) = X * (D / Real.log (y : ℝ)) := by
    dsimp [D]
    ring
  rw [← heq]
  simpa [eta, mul_assoc] using add_le_add_right hscaled (((y ^ S : ℕ) : ℝ) ^ 2)

theorem exists_fixed_depth_boundedMass_primeResidueInterval_bound :
    ∃ S : ℕ, 101 ≤ S ∧ ∀ C : ℝ, ∃ D : ℝ, 0 < D ∧
      ∀ d a L U y : ℕ, 0 < d → primeDivisorReciprocalMass d ≤ C → 2 ≤ y →
        ((primeResidueInterval d a L U y).card : ℝ) ≤
          (((U - L) / d + 1 : ℕ) : ℝ) * (D / Real.log (y : ℝ)) +
            ((y ^ S : ℕ) : ℝ) ^ 2 := by
  obtain ⟨S, hS, hdup⟩ := exists_fixed_depth_boundedMass_duplicateCandidates_bound
  refine ⟨S, hS, ?_⟩
  intro C
  obtain ⟨D, hD, hbound⟩ := hdup C
  refine ⟨D, hD, ?_⟩
  intro d a L U y hd hmass hy
  by_cases hne : (primeResidueInterval d a L U y).Nonempty
  · let q := (primeResidueInterval d a L U y).min' hne
    have hq := mem_primeResidueInterval_iff.mp (Finset.min'_mem _ hne)
    have hcard := card_primeResidueInterval_le_duplicateCandidates_of_nonempty_of_pos hd hne
    have hcardR : ((primeResidueInterval d a L U y).card : ℝ) ≤
        (twoAffinePrimeCandidates d q d q ((U - L) / d + 1) y).card := by exact_mod_cast hcard
    exact hcardR.trans (hbound d q _ y hd hmass hq.2.2.1 hq.2.2.2.1 hy)
  · rw [Finset.not_nonempty_iff_eq_empty.mp hne]
    simp only [Finset.card_empty, Nat.cast_zero]
    have hlogy : 0 < Real.log (y : ℝ) := Real.log_pos (by exact_mod_cast (show 1 < y by omega))
    positivity

#print axioms exists_fixed_depth_boundedMass_primeResidueInterval_bound

end Erdos822
