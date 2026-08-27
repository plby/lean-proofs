/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedRegroup

/-! # The full pinned-amplitude error after removing moved factors -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedUnshiftedValue (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) : ℝ :=
  pinnedBaseFactor p r * ∑ a : α → Option Unit, pinnedDivisorFactor p r a *
    (sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) *
      pinnedRemainingEulerProduct p r a)

def pinnedMajorantValue (m R : ℕ) (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) : ℝ :=
  pinnedBaseFactor p r * ∑ a : α → Option Unit, pinnedDivisorFactor p r a *
    sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a))

omit [DecidableEq α] in
theorem pinnedBaseFactor_nonneg {m : ℕ} {p : α → ℕ} (hp : ∀ q, 1 ≤ p q)
    (r : α → Option (Fin m)) : 0 ≤ pinnedBaseFactor p r := by
  apply Finset.prod_nonneg
  intro q _hq
  unfold localPinnedBaseWeight
  split_ifs
  · exact zero_le_one
  · exact div_nonneg (Nat.cast_nonneg _) (sub_nonneg.mpr (by exact_mod_cast hp q))

omit [DecidableEq α] in
theorem pinnedDivisorFactor_nonneg {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, m + 1 ≤ p q) (r : α → Option (Fin m)) (a : α → Option Unit) :
    0 ≤ pinnedDivisorFactor p r a := by
  apply Finset.prod_nonneg
  intro q _hq
  unfold localPinnedDivisorWeight
  split_ifs
  · exact zero_le_one
  · exact div_nonneg zero_le_one (sub_nonneg.mpr (by exact_mod_cast hp q))
  · exact le_rfl

omit [Fintype α] [DecidableEq α] in
theorem exists_commonPinnedProfile_replacement_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → 1 < R →
      ∀ (α : Type*) [DecidableEq α] [Fintype α] (p : α → ℕ),
        (∀ q, (p q).Prime) → Function.Injective p → (∀ q, 2 * (m + 1) ^ 2 < p q) →
        ∀ (j : Fin (m + 1)) (r : α → Option (Fin m)),
          |commonPinnedProfile m R p j r - pinnedUnshiftedValue m R p j r| ≤
            (C * sieveProfileScale (m + 1) / Real.log R) * pinnedMajorantValue m R p j r := by
  obtain ⟨C, hC, hbound⟩ := exists_weightedPinnedMovedProfileSum_error
  refine ⟨C, hC, ?_⟩
  intro m R hm hlog hR α _ _ p hp hinj hrough j r
  have hlarge (q : α) : m + 1 < p q := by
    have hh := hrough q
    nlinarith
  have hG : 0 ≤ pinnedBaseFactor p r := pinnedBaseFactor_nonneg (fun q => (hp q).one_le) r
  have hH (a : α → Option Unit) : 0 ≤ pinnedDivisorFactor p r a :=
    pinnedDivisorFactor_nonneg (fun q => (hlarge q).le) r a
  have hb0 (a : α → Option Unit) (q : α) : 0 ≤ pinnedAvailableWeight p r a q := by
    unfold pinnedAvailableWeight
    split_ifs
    · exact pinnedMovedWeight_nonneg (by exact_mod_cast (by omega : 2 ≤ m + 1))
        (by exact_mod_cast hrough q)
    · exact le_rfl
  have hble (a : α → Option Unit) (q : α) :
      pinnedAvailableWeight p r a q ≤ pinnedMovedWeight (m + 1) (p q) := by
    unfold pinnedAvailableWeight
    split_ifs
    · exact le_rfl
    · exact pinnedMovedWeight_nonneg (by exact_mod_cast (by omega : 2 ≤ m + 1))
        (by exact_mod_cast hrough q)
  have hpoint (a : α → Option Unit) := hbound hm hlog hR α p hp hinj hrough
    (pinnedAvailableWeight p r a) (hb0 a) (hble a) j (pinnedBaseTuple p j r a)
      (pinnedBaseTuple_pos (fun q => (hp q).pos) j r a)
  simp_rw [← pinnedRemainingEulerProduct_eq] at hpoint
  rw [commonPinnedProfile_eq_weightedMovedSums hp hlarge]
  unfold pinnedUnshiftedValue
  rw [← mul_sub, abs_mul, abs_of_nonneg hG, ← Finset.sum_sub_distrib]
  simp_rw [← mul_sub]
  calc
    _ ≤ pinnedBaseFactor p r * ∑ a : α → Option Unit,
        |pinnedDivisorFactor p r a *
          (weightedPinnedMovedProfileSum m R p j (pinnedBaseTuple p j r a)
            (pinnedAvailableWeight p r a) -
            sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) *
              pinnedRemainingEulerProduct p r a)| :=
      mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) hG
    _ ≤ pinnedBaseFactor p r * ∑ a : α → Option Unit, pinnedDivisorFactor p r a *
        ((C * sieveProfileScale (m + 1) / Real.log R) *
          sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a))) := by
      apply mul_le_mul_of_nonneg_left _ hG
      apply Finset.sum_le_sum
      intro a _ha
      rw [abs_mul, abs_of_nonneg (hH a)]
      exact mul_le_mul_of_nonneg_left (hpoint a) (hH a)
    _ = _ := by
      unfold pinnedMajorantValue
      simp only [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro a _ha
      ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_commonPinnedProfile_replacement_error
