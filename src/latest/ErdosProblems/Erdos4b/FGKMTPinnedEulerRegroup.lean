/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedReplacement

/-! # Collecting the finite pinned Euler factors into the harmonic denominator -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedBaseEulerProduct {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m)) : ℝ :=
  ∏ q, if r q = none then pinnedLocalFactor (m + 1) (p q) else 1

def pinnedHarmonicWeight {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) : ℝ :=
  assignmentScalarWeight
    (fun q => if r q = none then 1 / pinnedLocalDenominator (m + 1) (p q) else 0) a

omit [DecidableEq α] in
theorem pinnedDivisorFactor_mul_remainingEuler {m : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q)
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedDivisorFactor p r a * pinnedRemainingEulerProduct p r a =
      pinnedBaseEulerProduct p r * pinnedHarmonicWeight p r a := by
  unfold pinnedDivisorFactor pinnedRemainingEulerProduct pinnedBaseEulerProduct
    pinnedHarmonicWeight assignmentScalarWeight
  rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q _hq
  have hapos : 0 < pinnedLocalFactor ((m : ℝ) + 1) (p q) :=
    pinnedLocalFactor_pos (by exact_mod_cast (by omega : 2 ≤ m + 1))
      (by exact_mod_cast hrough q)
  by_cases hr : r q = none <;> by_cases ha : a q = none
  · simp [localPinnedDivisorWeight, hr, ha]
  · simp only [localPinnedDivisorWeight, hr, ha, true_and, if_false, if_true]
    unfold pinnedLocalDenominator
    field_simp [hapos.ne']
  · simp [localPinnedDivisorWeight, hr, ha]
  · simp [localPinnedDivisorWeight, hr, ha]

theorem pinnedUnshiftedValue_eq_harmonic {m R : ℕ} (hm : 1 ≤ m) {p : α → ℕ}
    (hrough : ∀ q, 2 * (m + 1) ^ 2 < p q)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    pinnedUnshiftedValue m R p j r =
      (pinnedBaseFactor p r * pinnedBaseEulerProduct p r) *
        ∑ a : α → Option Unit, pinnedHarmonicWeight p r a *
          sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) := by
  unfold pinnedUnshiftedValue
  rw [Finset.mul_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  rw [show pinnedBaseFactor p r * (pinnedDivisorFactor p r a *
      (sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) *
        pinnedRemainingEulerProduct p r a)) =
      pinnedBaseFactor p r * (pinnedDivisorFactor p r a * pinnedRemainingEulerProduct p r a) *
        sieveProfile (m + 1) (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) by ring]
  rw [pinnedDivisorFactor_mul_remainingEuler hm hrough]
  ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedDivisorFactor_mul_remainingEuler
#print axioms Erdos4b.FGKMT.pinnedUnshiftedValue_eq_harmonic
