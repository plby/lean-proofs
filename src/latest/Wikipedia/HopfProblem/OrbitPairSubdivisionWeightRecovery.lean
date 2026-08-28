import Wikipedia.HopfProblem.OrbitPairSubdivisionCoordinateLevels

/-!
# Recovering simplex weights from the chain thresholds

Descending induction recovers each normalized weight from its tail sum.
Multiplying by the nonzero face cardinality then recovers the original
geometric simplex point.
-/

noncomputable section

universe u

open PartialOrder
open scoped BigOperators

namespace Wikipedia.HopfProblem.OrbitPair.Subdivision

open FirstHurewicz

variable {n k : ℕ}
variable (A : Fin (k + 1) → NonemptyFiniteChains (ULift.{u} (Fin (n + 1))))

theorem chainWeight_eq_of_tailWeight_eq (t s : Simplex k)
    (h : tailWeight A t = tailWeight A s) (j : Fin (k + 1)) :
    chainWeight A t j = chainWeight A s j := by
  classical
  induction j using WellFoundedGT.induction with
  | ind j ih =>
    have hr :
        (∑ l ∈ Finset.univ.erase j, if j ≤ l then chainWeight A t l else 0) =
          ∑ l ∈ Finset.univ.erase j, if j ≤ l then chainWeight A s l else 0 := by
      apply Finset.sum_congr rfl
      intro l hl
      by_cases hjl : j ≤ l
      · have hne : l ≠ j := (Finset.mem_erase.mp hl).1
        have hlt : j < l := lt_of_le_of_ne hjl (Ne.symm hne)
        simp only [hjl, ite_true, ih l hlt]
      · simp only [hjl, ite_false]
    have ht := Finset.add_sum_erase Finset.univ
      (fun l ↦ if j ≤ l then chainWeight A t l else 0) (Finset.mem_univ j)
    have hs := Finset.add_sum_erase Finset.univ
      (fun l ↦ if j ≤ l then chainWeight A s l else 0) (Finset.mem_univ j)
    simp only [le_refl, ite_true] at ht hs
    have he := ht.trans ((congrFun h j).trans hs.symm)
    rw [hr] at he
    exact add_right_cancel he

theorem simplex_eq_of_tailWeight_eq (t s : Simplex k)
    (h : tailWeight A t = tailWeight A s) : t = s := by
  apply Subtype.ext
  funext j
  have hw := chainWeight_eq_of_tailWeight_eq A t s h j
  change t j / (A j).finset.card = s j / (A j).finset.card at hw
  exact (div_left_inj' (ne_of_gt (Nat.cast_pos.mpr (A j).nonempty.card_pos :
    (0 : ℝ) < (A j).finset.card))).mp hw

end Wikipedia.HopfProblem.OrbitPair.Subdivision
