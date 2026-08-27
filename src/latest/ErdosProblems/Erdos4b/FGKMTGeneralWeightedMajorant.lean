/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTLongTensorPermutation
import ErdosProblems.Erdos4b.FGKMTGeneralLongTensorMean

/-!
# The arithmetic square-majorant sum for an admissible denominator chain

Finite Cauchy--Schwarz, coordinate permutation, and the proved mixed
mean give a uniform quadratic-dimensional upper bound on the literal
weighted majorant, normalized by the actual profile energy.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

def majorantSieveSum (k M : ℕ) (g : ℕ → ℝ) (R j : ℕ) : ℝ :=
  ∑ e : Fin j → Fin (R ^ 2 + 1),
    sieveProfileMajorant k j (fun q => Real.log (e q).val / Real.log R) ^ 2 *
      roughSieveWeight M g (∏ q, (e q).val)

theorem majorantSieveSum_le_long (k M R j : ℕ) (g : ℕ → ℝ)
    (hg : ∀ p : ℕ, p.Prime → ¬p ∣ M → 0 ≤ g p) :
    majorantSieveSum k M g R (j + 1) ≤ (j + 1 : ℕ) ^ 2 * longTensorSieveSum k M g R j := by
  classical
  let W := fun e : Fin (j + 1) → Fin (R ^ 2 + 1) => roughSieveWeight M g (∏ q, (e q).val)
  let B := fun (e : Fin (j + 1) → Fin (R ^ 2 + 1)) (i : Fin (j + 1)) =>
    oneLongTensor k (j + 1) i (fun q => Real.log (e q).val / Real.log R) ^ 2
  calc
    _ ≤ ∑ e : Fin (j + 1) → Fin (R ^ 2 + 1), ((j + 1 : ℕ) * ∑ i, B e i) * W e := by
      apply Finset.sum_le_sum
      intro e _he
      exact mul_le_mul_of_nonneg_right
        (sieveProfileMajorant_sq_le k (j + 1) _) (roughSieveWeight_nonneg M g hg _)
    _ = (j + 1 : ℕ) * ∑ e : Fin (j + 1) → Fin (R ^ 2 + 1), ∑ i, B e i * W e := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro e _he
      rw [← Finset.sum_mul]
      ring
    _ = (j + 1 : ℕ) * ∑ i : Fin (j + 1), oneLongTensorSieveSum k M g R (j + 1) i := by
      rw [Finset.sum_comm]
      rfl
    _ = (j + 1 : ℕ) * ∑ _i : Fin (j + 1), longTensorSieveSum k M g R j := by
      simp only [oneLongTensorSieveSum_eq_long]
    _ = _ := by simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]; ring

theorem exists_generalMajorantSieveSum_energy_bound :
    ∃ C : ℝ, 0 < C ∧ ∀ {k M R j : ℕ}, 2 ≤ k → 10000 ≤ Real.log k →
      0 < M → 1 < R → j + 1 ≤ k →
      (∀ p : ℕ, p.Prime → p ≤ k ^ 2 → p ∣ M) → ∀ g : ℕ → ℝ,
      (∀ s : ℕ, s < j + 1 → ∀ p : ℕ, p.Prime → ¬p ∣ M →
        (p : ℝ) / 2 ≤ g p + s ∧ |g p + s - p| ≤ 2 * (k : ℝ) ∧ g p + s ≤ p - 1) →
      (j + 1 : ℕ) *
        (C * sieveProfileScale k ^ 2 * modulusLogScale (M * R ^ (2 * k)) ^ 3 / Real.log R) ≤ 1 →
      majorantSieveSum k M g R (j + 1) ≤
        12 * (j + 1 : ℕ) ^ 2 *
          multivariateSieveConstant M g (j + 1) *
          Real.log R ^ (j + 1) * dimensionProfileEnergy k (j + 1) := by
  obtain ⟨C, hC, hbound⟩ := exists_generalLongTensorSieveSum_relative_error
  refine ⟨C, hC, ?_⟩
  intro k M R j hk hlog hM hR hj hsmall g hchain htotal
  have hk0 : 0 < k := by omega
  have hb := profile_scales_bounds hk0 hlog
  let P := multivariateSieveConstant M g (j + 1)
  let L := Real.log R
  let a := dimensionProfileMass k
  let d := dimensionLongMass k
  have hL : 0 < L := Real.log_pos (by exact_mod_cast hR)
  have ha : 0 < a := dimensionProfileMass_pos hk0 hlog
  have hd : 0 < d := sieveFactor_sq_mass_pos (zero_le_one.trans hb.1) (by norm_num)
  have hP : 0 < P := multivariateSieveConstant_pos hk0 hM
    hsmall _ hchain
  have hg (p : ℕ) (hp : p.Prime) (hpM : ¬p ∣ M) :
      0 ≤ g p := by
    have h := (hchain 0 (Nat.zero_lt_succ j) p hp hpM).1
    simp only [Nat.cast_zero, add_zero] at h
    exact (half_pos (show (0 : ℝ) < p by exact_mod_cast hp.pos)).le.trans h
  have hmain : 0 < P * (L * d) * (L * a) ^ j := by positivity
  have hrel := (hbound hk hlog hM hR hj hsmall g hchain htotal).trans htotal
  have hlong : longTensorSieveSum k M g R j ≤
      2 * (P * (L * d) * (L * a) ^ j) := by
    have hh : |longTensorSieveSum k M g R j -
        P * (L * d) * (L * a) ^ j| ≤ P * (L * d) * (L * a) ^ j := by
      simpa only [one_mul] using (div_le_iff₀ hmain).mp hrel
    linarith [le_abs_self (longTensorSieveSum k M g R j -
      P * (L * d) * (L * a) ^ j)]
  have hmainBound : P * (L * d) * (L * a) ^ j ≤ 2 * P * (L * a) ^ (j + 1) := by
    calc
      _ ≤ P * (L * (2 * a)) * (L * a) ^ j :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_left (dimensionLongMass_le_twice hk0 hlog) hL.le) hP.le)
          (pow_nonneg (mul_nonneg hL.le ha.le) j)
      _ = _ := by rw [pow_succ (L * a) j]; ring
  have hI := (dimensionProfileEnergy_bounds hk0 hlog hj).1
  have hmass : a ^ (j + 1) ≤ 3 * dimensionProfileEnergy k (j + 1) := by
    change a ^ (j + 1) / 3 ≤ dimensionProfileEnergy k (j + 1) at hI
    linarith
  calc
    _ ≤ (j + 1 : ℕ) ^ 2 * longTensorSieveSum k M g R j :=
      majorantSieveSum_le_long k M R j _ hg
    _ ≤ (j + 1 : ℕ) ^ 2 * (2 * (P * (L * d) * (L * a) ^ j)) :=
      mul_le_mul_of_nonneg_left hlong (sq_nonneg _)
    _ ≤ (j + 1 : ℕ) ^ 2 * (2 * (2 * P * (L * a) ^ (j + 1))) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hmainBound (by norm_num)) (sq_nonneg _)
    _ = (4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) * a ^ (j + 1) := by rw [mul_pow]; ring
    _ ≤ (4 * (j + 1 : ℕ) ^ 2 * P * L ^ (j + 1)) *
        (3 * dimensionProfileEnergy k (j + 1)) :=
      mul_le_mul_of_nonneg_left hmass (by positivity)
    _ = _ := by dsimp only [P, L]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.majorantSieveSum_le_long
#print axioms Erdos4b.FGKMT.exists_generalMajorantSieveSum_energy_bound
