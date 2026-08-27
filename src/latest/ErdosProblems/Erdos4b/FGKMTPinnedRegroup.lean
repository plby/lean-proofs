/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSplitTuples
import ErdosProblems.Erdos4b.FGKMTWeightedMovedProfile

/-! # Regrouping the actual pinned amplitude into masked moved-profile sums -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedAvailableWeight {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) (q : α) : ℝ :=
  if r q = none ∧ a q = none then pinnedMovedWeight (m + 1) (p q) else 0

def pinnedRemainingEulerProduct {m : ℕ} (p : α → ℕ) (r : α → Option (Fin m))
    (a : α → Option Unit) : ℝ :=
  ∏ q, if r q = none ∧ a q = none then pinnedLocalFactor (m + 1) (p q) else 1

omit [DecidableEq α] in
theorem pinnedMovedFactor_eq_available {m : ℕ} (p : α → ℕ)
    (r : α → Option (Fin m)) (a : α → Option Unit) (b : α → Option (Fin m)) :
    pinnedMovedFactor p r a b = assignmentScalarWeight
      (fun q => -pinnedAvailableWeight p r a q) b := by
  rw [pinnedMovedFactor_eq_scalar]
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hb : b q = none <;>
    by_cases ha : r q = none ∧ a q = none <;> simp [pinnedAvailableWeight, hb, ha]

omit [DecidableEq α] in
theorem pinnedRemainingEulerProduct_eq {m : ℕ} (p : α → ℕ)
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedRemainingEulerProduct p r a =
      ∏ q, (1 - (m : ℝ) * pinnedAvailableWeight p r a q) := by
  apply Finset.prod_congr rfl
  intro q _hq
  by_cases hq : r q = none ∧ a q = none
  · simp only [if_pos hq, pinnedAvailableWeight, pinnedLocalFactor, pinnedMovedWeight]
    ring
  · simp [pinnedAvailableWeight, hq]

theorem commonPinnedProfile_eq_weightedMovedSums {m R : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (hlarge : ∀ q, m + 1 < p q)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) :
    commonPinnedProfile m R p j r = pinnedBaseFactor p r *
      ∑ a : α → Option Unit, pinnedDivisorFactor p r a *
        weightedPinnedMovedProfileSum m R p j (pinnedBaseTuple p j r a)
          (pinnedAvailableWeight p r a) := by
  rw [commonPinnedProfile_eq_split hp hlarge]
  simp only [weightedPinnedMovedProfileSum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _ha
  apply Finset.sum_congr rfl
  intro b _hb
  rw [← pinnedMovedFactor_eq_available]
  let c := pinnedBaseFactor p r * pinnedDivisorFactor p r a * pinnedMovedFactor p r a b
  have hterm : c * primeAssignmentProfile (m + 1) R p (pinnedSplitAssignment j r a b) =
      c * sieveProfile (m + 1) (m + 1) (sieveLogTuple R
        (fun i => pinnedBaseTuple p j r a i *
          assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb b) i)) := by
    by_cases hc : c = 0
    · simp [hc]
    · rw [primeAssignmentProfile, pinnedSplitAssignment_tuple_factorization p j r a b hc]
  calc
    _ = c * primeAssignmentProfile (m + 1) R p (pinnedSplitAssignment j r a b) := by
      dsimp only [c]
      ring
    _ = _ := hterm
    _ = _ := by dsimp only [c]; ring

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedRemainingEulerProduct_eq
#print axioms Erdos4b.FGKMT.commonPinnedProfile_eq_weightedMovedSums
