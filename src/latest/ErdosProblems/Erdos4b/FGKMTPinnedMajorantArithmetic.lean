/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTScalarUpperReindex
import ErdosProblems.Erdos4b.FGKMTPinnedMajorantSlice

/-! # Enlarging the actual pinned arithmetic majorant to its full scalar support -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

omit [DecidableEq α] in
theorem pinnedDivisorFactor_le_harmonic {m : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q) (r : α → Option (Fin m))
    (a : α → Option Unit) : pinnedDivisorFactor p r a ≤ pinnedHarmonicWeight p r a := by
  rw [pinnedDivisorFactor_eq_scalar]
  unfold pinnedHarmonicWeight
  apply assignmentScalarWeight_mono
  · intro q
    split_ifs
    · have hr : 2 * ((m : ℝ) + 1) ^ 2 < p q := by exact_mod_cast hrough q
      exact div_nonneg zero_le_one (by nlinarith : 0 ≤ (p q : ℝ) - (m + 1))
    · exact le_rfl
  · intro q
    split_ifs
    · have hk : (2 : ℝ) ≤ (m : ℝ) + 1 := by exact_mod_cast (by omega : 2 ≤ m + 1)
      have hr : 2 * ((m : ℝ) + 1) ^ 2 < p q := by exact_mod_cast hrough q
      have hpk : 0 < (p q : ℝ) - (m + 1) := by nlinarith
      have hgp : 0 < pinnedLocalDenominator (m + 1) (p q) :=
        mul_pos hpk (pinnedLocalFactor_pos hk hr)
      have hgle : pinnedLocalDenominator (m + 1) (p q) ≤ (p q : ℝ) - (m + 1) := by
        simpa only [pinnedLocalDenominator, mul_one] using mul_le_mul_of_nonneg_left
          (pinnedLocalFactor_lt_one hk hr).le hpk.le
      exact div_le_div_of_nonneg_left zero_le_one hgp hgle
    · exact le_rfl

theorem pinnedMajorantValue_le_full_sum {m M R : ℕ} (hm : 1 ≤ m)
    (hlog : 10000 ≤ Real.log (m + 1 : ℕ)) (hR : 1 < R)
    (hsmall : ∀ l : ℕ, l.Prime → l ≤ 2 * (m + 1) ^ 2 → l ∣ M) {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p) (hnot : ∀ q, ¬p q ∣ M)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    pinnedMajorantValue m R p j r ≤ pinnedBaseFactor p r *
      ∑ a ∈ Finset.Icc 0 (R ^ 2),
        sieveProfileMajorant (m + 1) (m + 1)
          (Fin.cons (Real.log a / Real.log R) (sieveLogTuple R (assignmentPrimeTuple p r))) *
        roughSieveWeight (M * assignmentPrimeProduct p r)
          (fun l => pinnedLocalDenominator (m + 1) l) a := by
  have hrough (q : α) : 2 * (m + 1) ^ 2 < p q := by
    by_contra hh
    exact hnot q (hsmall (p q) (hp q) (by omega))
  let t := sieveLogTuple R (assignmentPrimeTuple p r)
  let F := fun a : ℕ => sieveProfileMajorant (m + 1) (m + 1)
    (Fin.cons (Real.log a / Real.log R) t) *
    roughSieveWeight (M * assignmentPrimeProduct p r)
      (fun l => pinnedLocalDenominator (m + 1) l) a
  have hF0 (a : ℕ) : 0 ≤ F a := by
    apply mul_nonneg (sieveProfileMajorant_nonneg _ _ _)
    apply roughSieveWeight_nonneg
    intro l hl hlMr
    have hr : 2 * (m + 1) ^ 2 < l := by
      by_contra hh
      exact hlMr (dvd_mul_of_dvd_left (hsmall l hl (by omega)) _)
    have h := (pinnedLocalDenominator_bounds (k := (m : ℝ) + 1) (p := (l : ℝ))
      (by exact_mod_cast (by omega : 2 ≤ m + 1)) (by exact_mod_cast hr)).1
    exact (half_pos (show (0 : ℝ) < l by exact_mod_cast hl.pos)).le.trans h.le
  have hFB (a : ℕ) (ha : F a ≠ 0) : a ≤ R ^ 2 := by
    by_contra hh
    have hz := sieveProfileMajorant_logSlice_zero_of_sq_le (Nat.succ_pos m) hlog hR m t
      (by omega : R ^ 2 ≤ a)
    exact ha (by simp only [F, hz, zero_mul])
  have hG := pinnedBaseFactor_nonneg (fun q => (hp q).one_le) r
  calc
    _ ≤ pinnedBaseFactor p r * ∑ a : α → Option Unit,
        pinnedHarmonicWeight p r a *
          sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) := by
      apply mul_le_mul_of_nonneg_left _ hG
      apply Finset.sum_le_sum
      intro a _ha
      exact mul_le_mul_of_nonneg_right (pinnedDivisorFactor_le_harmonic hm hrough r a)
        (sieveProfileMajorant_nonneg _ _ _)
    _ = pinnedBaseFactor p r * ∑ a : α → Option Unit, F (assignmentPrimeProduct p a) := by
      congr 1
      apply Finset.sum_congr rfl
      intro a _ha
      rw [pinnedHarmonicWeight_eq_rough hp hinj hnot, sieveProfileMajorant_pinnedBaseTuple]
      exact mul_comm _ _
    _ ≤ pinnedBaseFactor p r * ∑ a ∈ Finset.Icc 0 (R ^ 2), F a :=
      mul_le_mul_of_nonneg_left (sum_unit_assignments_le_sum_Icc hp hinj _ F hF0 hFB) hG
    _ = _ := rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedDivisorFactor_le_harmonic
#print axioms Erdos4b.FGKMT.pinnedMajorantValue_le_full_sum
