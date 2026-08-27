/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedMovedMass
import ErdosProblems.Erdos4b.FGKMTCommonPinnedSupport

/-!
# Removing moved factors from the profile in the pinned amplitude

The signed finite sum is compared with the exact Euler product. The
absolute error is bounded by the reduced-tuple majorant, uniformly in
the dimension, radius, finite prime universe, pin, and positive base.
-/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι : Type*} [Fintype α]

theorem abs_assignmentScalarWeight_neg {b : α → ℝ} (hb : ∀ q, 0 ≤ b q)
    (r : α → Option ι) :
    |assignmentScalarWeight (fun q => -b q) r| = assignmentScalarWeight b r := by
  classical
  rw [assignmentScalarWeight, Finset.abs_prod]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hr : r q = none <;> simp [hr, abs_of_nonneg (hb q)]

theorem assignmentScalarWeight_neg_eq_moebius {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (b : α → ℝ) (r : α → Option ι) :
    assignmentScalarWeight (fun q => -b q) r =
      (ArithmeticFunction.moebius (assignmentPrimeProduct p r) : ℝ) *
        assignmentScalarWeight b r := by
  classical
  rw [assignmentPrimeProduct_moebius hp hinj r, assignmentScalarWeight,
    assignmentScalarWeight, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hr : r q = none <;> simp [hr]

def pinnedMovedProfileSum [DecidableEq α] (m R : ℕ) (p : α → ℕ)
    (j : Fin (m + 1)) (a : Fin (m + 1) → ℕ) : ℝ :=
  ∑ s : α → Option (Fin m),
    assignmentScalarWeight (fun q => -pinnedMovedWeight (m + 1) (p q)) s *
      sieveProfile (m + 1) (m + 1) (sieveLogTuple R
        (fun i => a i * assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb s) i))

theorem sum_signed_pinnedMovedWeight [DecidableEq α] (m : ℕ) (p : α → ℕ) :
    (∑ s : α → Option (Fin m),
      assignmentScalarWeight (fun q => -pinnedMovedWeight (m + 1) (p q)) s) =
      ∏ q, pinnedLocalFactor (m + 1) (p q) := by
  rw [sum_assignmentScalarWeight]
  apply Finset.prod_congr rfl
  intro q _hq
  simp only [Fintype.card_fin, pinnedLocalFactor, pinnedMovedWeight]
  ring

omit [Fintype α] in
theorem exists_pinnedMovedProfileSum_error :
    ∃ C : ℝ, 0 < C ∧ ∀ {m R : ℕ}, 1 ≤ m → 10000 ≤ Real.log (m + 1 : ℕ) → 1 < R →
      ∀ (α : Type*) [DecidableEq α] [Fintype α] (p : α → ℕ),
        (∀ q, (p q).Prime) → Function.Injective p → (∀ q, 2 * (m + 1) ^ 2 < p q) →
        ∀ (j : Fin (m + 1)) (a : Fin (m + 1) → ℕ), (∀ i, 0 < a i) →
          |pinnedMovedProfileSum m R p j a -
            sieveProfile (m + 1) (m + 1) (sieveLogTuple R a) *
              ∏ q, pinnedLocalFactor (m + 1) (p q)| ≤
            (C * sieveProfileScale (m + 1) / Real.log R) *
              sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R a) := by
  obtain ⟨C, hC, hvar⟩ := exists_sieveProfile_orthant_variation_bound
  refine ⟨16 * Real.exp 2 * C, by positivity, ?_⟩
  intro m R hm hlog hR α _ _ p hp hinj hrough j a ha
  let b := fun q => pinnedMovedWeight ((m : ℝ) + 1) (p q)
  let F₀ := sieveProfile (m + 1) (m + 1) (sieveLogTuple R a)
  let B := C * sieveProfileScale (m + 1) *
    sieveProfileMajorant (m + 1) (m + 1) (sieveLogTuple R a) / Real.log R
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  have hB : 0 ≤ B := div_nonneg (mul_nonneg
    (mul_nonneg hC.le (zero_le_one.trans (profile_scales_bounds (by omega) hlog).1))
      (sieveProfileMajorant_nonneg _ _ _)) hlogR.le
  have hb : ∀ q, 0 ≤ b q := fun q => pinnedMovedWeight_nonneg
    (by exact_mod_cast (by omega : 2 ≤ m + 1)) (by exact_mod_cast hrough q)
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
    change |sieveProfile _ _ _ - F₀| ≤ _ at hv
    have hprod : (∏ i, t i) = assignmentPrimeProduct p s := by
      rw [prod_assignmentPrimeTuple, assignmentPrimeProduct_map]
    rw [hprod] at hv
    convert hv using 1
    dsimp only [B]
    ring
  have hexpand : pinnedMovedProfileSum m R p j a -
      F₀ * ∏ q, pinnedLocalFactor (m + 1) (p q) =
      ∑ s : α → Option (Fin m), assignmentScalarWeight (fun q => -b q) s *
        (sieveProfile (m + 1) (m + 1) (sieveLogTuple R
          (fun i => a i * assignmentPrimeTuple p
            (mapPrimeAssignment j.succAboveEmb s) i)) - F₀) := by
    rw [← sum_signed_pinnedMovedWeight m p]
    simp only [pinnedMovedProfileSum, Finset.mul_sum, ← Finset.sum_sub_distrib, b]
    apply Finset.sum_congr rfl
    intro s _hs
    ring
  change |pinnedMovedProfileSum m R p j a - F₀ * _| ≤ _
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
    _ ≤ B * (16 * Real.exp 2) :=
      mul_le_mul_of_nonneg_left (pinnedMovedAssignment_masses_le hm hinj hrough).2 hB
    _ = _ := by dsimp only [B]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_signed_pinnedMovedWeight
#print axioms Erdos4b.FGKMT.exists_pinnedMovedProfileSum_error
