/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMovedProfile

/-!
# Profile replacement with arbitrary smaller moved-prime weights

Allowing zero weights enforces excluded prime supports without changing
the finite universe. The error constant is independent of those exclusions.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α]

theorem assignmentScalarWeight_mono {b c : α → ℝ}
    (hb : ∀ q, 0 ≤ b q) (hbc : ∀ q, b q ≤ c q) (r : α → Option ι) :
    assignmentScalarWeight b r ≤ assignmentScalarWeight c r := by
  classical
  apply Finset.prod_le_prod
  · intro q _hq
    split_ifs
    · exact zero_le_one
    · exact hb q
  · intro q _hq
    split_ifs
    · exact le_rfl
    · exact hbc q

def weightedPinnedMovedProfileSum [DecidableEq α] (m R : ℕ) (p : α → ℕ)
    (j : Fin (m + 1)) (a : Fin (m + 1) → ℕ) (b : α → ℝ) : ℝ :=
  ∑ s : α → Option (Fin m), assignmentScalarWeight (fun q => -b q) s *
    sieveProfile (m + 1) (m + 1) (sieveLogTuple R
      (fun i => a i * assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb s) i))

theorem sum_signed_assignmentScalarWeight [DecidableEq α] (m : ℕ) (b : α → ℝ) :
    (∑ s : α → Option (Fin m), assignmentScalarWeight (fun q => -b q) s) =
      ∏ q, (1 - (m : ℝ) * b q) := by
  rw [sum_assignmentScalarWeight]
  apply Finset.prod_congr rfl
  intro q _hq
  simp only [Fintype.card_fin]
  ring

omit [Fintype α] in
theorem exists_weightedPinnedMovedProfileSum_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → 1 < R →
      ∀ (α : Type*) [DecidableEq α] [Fintype α] (p : α → ℕ),
        (∀ q, (p q).Prime) → Function.Injective p → (∀ q, 2 * (m + 1) ^ 2 < p q) →
        ∀ b : α → ℝ, (∀ q, 0 ≤ b q) → (∀ q, b q ≤ pinnedMovedWeight (m + 1) (p q)) →
        ∀ (j : Fin (m + 1)) (a : Fin (m + 1) → ℕ), (∀ i, 0 < a i) →
          |weightedPinnedMovedProfileSum m R p j a b -
            sieveProfile (m + 1) (m + 1) (sieveLogTuple R a) *
              ∏ q, (1 - (m : ℝ) * b q)| ≤
            (C * sieveProfileScale (m + 1) / Real.log R) *
              sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R a) := by
  obtain ⟨C, hC, hvar⟩ := exists_sieveProfile_orthant_variation_bound
  refine ⟨16 * Real.exp 2 * C, by positivity, ?_⟩
  intro m R hm hlog hR α _ _ p hp hinj hrough b hb hupper j a ha
  let F₀ := sieveProfile (m + 1) (m + 1) (sieveLogTuple R a)
  let B := C * sieveProfileScale (m + 1) *
    sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R a) / Real.log R
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg
    (mul_nonneg hC.le (zero_le_one.trans (profile_scales_bounds (by omega) hlog).1))
      (sieveProfileMajorant_nonneg _ _ _)) hlogR.le
  have hmoment : (∑ s : α → Option (Fin m), assignmentScalarWeight b s *
      Real.log (assignmentPrimeProduct p s)) ≤ 16 * Real.exp 2 := by
    apply le_trans _ (pinnedMovedAssignment_masses_le hm hinj hrough).2
    exact Finset.sum_le_sum fun s _hs => mul_le_mul_of_nonneg_right
      (assignmentScalarWeight_mono hb hupper s) (Real.log_natCast_nonneg _)
  have hpoint (s : α → Option (Fin m)) :
      |sieveProfile (m + 1) (m + 1) (sieveLogTuple R
          (fun i => a i * assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb s) i)) - F₀| ≤
        B * Real.log (assignmentPrimeProduct p s) := by
    let t := assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb s)
    have ht : ∀ i, 0 < t i := assignmentPrimeTuple_pos (fun q => (hp q).pos) _
    have hv := hvar (by omega : 0 < m + 1) hlog (m + 1)
      (sieveLogTuple R a) (sieveLogTuple R (fun i => a i * t i))
      (sieveLogTuple_nonneg R a) (sieveLogTuple_le_mul R a t ha ht)
    rw [sieveLogTuple_mul_sub_sum R a t ha ht] at hv
    have hprod : (∏ i, t i) = assignmentPrimeProduct p s := by
      rw [prod_assignmentPrimeTuple, assignmentPrimeProduct_map]
    rw [hprod] at hv
    convert hv using 1
    dsimp only [B]
    ring
  have hexpand : weightedPinnedMovedProfileSum m R p j a b -
      F₀ * ∏ q, (1 - (m : ℝ) * b q) =
      ∑ s : α → Option (Fin m), assignmentScalarWeight (fun q => -b q) s *
        (sieveProfile (m + 1) (m + 1) (sieveLogTuple R
          (fun i => a i * assignmentPrimeTuple p
            (mapPrimeAssignment j.succAboveEmb s) i)) - F₀) := by
    rw [← sum_signed_assignmentScalarWeight m b]
    simp only [weightedPinnedMovedProfileSum, Finset.mul_sum, ← Finset.sum_sub_distrib]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  change |weightedPinnedMovedProfileSum m R p j a b - F₀ * _| ≤ _
  rw [hexpand]
  calc
    _ ≤ ∑ s : α → Option (Fin m), |assignmentScalarWeight (fun q => -b q) s *
        (sieveProfile (m + 1) (m + 1) (sieveLogTuple R
          (fun i => a i * assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb s) i)) - F₀)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ s : α → Option (Fin m), assignmentScalarWeight b s *
        (B * Real.log (assignmentPrimeProduct p s)) := by
      apply Finset.sum_le_sum
      intro s _hs
      rw [abs_mul, abs_assignmentScalarWeight_neg hb]
      exact mul_le_mul_of_nonneg_left (hpoint s) (assignmentScalarWeight_nonneg hb s)
    _ = B * ∑ s : α → Option (Fin m),
        assignmentScalarWeight b s * Real.log (assignmentPrimeProduct p s) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro s _hs
      ring
    _ ≤ B * (16 * Real.exp 2) := mul_le_mul_of_nonneg_left hmoment hB
    _ = _ := by dsimp only [B]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_weightedPinnedMovedProfileSum_error
