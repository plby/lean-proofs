/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedHarmonicArithmetic
import ErdosProblems.Erdos4b.FGKMTCoordinateUpdate

/-! # The literal pinned base tuple and its one-variable profile slice -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α]

theorem pinnedBaseTuple_eq_insertNth {m : ℕ} (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedBaseTuple p j r a =
      j.insertNth (assignmentPrimeProduct p a) (assignmentPrimeTuple p r) := by
  apply Fin.eq_insertNth_iff.mpr
  refine ⟨pinnedBaseTuple_pin p j r a, ?_⟩
  funext i
  exact pinnedBaseTuple_unpinned p j r a i

theorem sieveLogTuple_insertNth (R : ℕ) {m : ℕ} (j : Fin (m + 1))
    (a : ℕ) (r : Fin m → ℕ) :
    sieveLogTuple R (j.insertNth a r) =
      j.insertNth (Real.log a / Real.log R) (sieveLogTuple R r) := by
  apply Fin.eq_insertNth_iff.mpr
  constructor
  · simp [sieveLogTuple]
  · funext i
    simp [Fin.removeNth, sieveLogTuple]

theorem sieveProfile_insertNth (k m : ℕ) (j : Fin (m + 1)) (x : ℝ) (t : Fin m → ℝ) :
    sieveProfile k (m + 1) (j.insertNth x t) =
      sieveProfile k (m + 1) (Fin.cons x t) := by
  unfold sieveProfile
  rw [Fin.sum_univ_succAbove _ j, Fin.prod_univ_succAbove _ j]
  simp only [Fin.insertNth_apply_same, Fin.insertNth_apply_succAbove,
    Fin.sum_univ_succ, Fin.prod_univ_succ, Fin.cons_zero, Fin.cons_succ]

theorem sieveProfile_pinnedBaseTuple (k R : ℕ) {m : ℕ} (p : α → ℕ)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) (a : α → Option Unit) :
    sieveProfile k (m + 1) (sieveLogTuple R (pinnedBaseTuple p j r a)) =
      sieveProfile k (m + 1) (Fin.cons
        (Real.log (assignmentPrimeProduct p a) / Real.log R)
        (sieveLogTuple R (assignmentPrimeTuple p r))) := by
  rw [pinnedBaseTuple_eq_insertNth, sieveLogTuple_insertNth, sieveProfile_insertNth]

theorem sieveProfile_cons_zero_of_one_le (k m : ℕ) (t : Fin m → ℝ)
    (ht : ∀ i, 0 ≤ t i) {x : ℝ} (hx : 1 ≤ x) :
    sieveProfile k (m + 1) (Fin.cons x t) = 0 := by
  apply sieveProfile_zero_of_sum_ge_one
  rw [Fin.sum_univ_succ]
  simp only [Fin.cons_zero, Fin.cons_succ]
  exact hx.trans (le_add_of_nonneg_right (Finset.sum_nonneg fun i _hi => ht i))

theorem sieveProfile_logSlice_zero_of_ge (k m : ℕ) {R : ℕ} (hR : 1 < R)
    (t : Fin m → ℝ) (ht : ∀ i, 0 ≤ t i) {a : ℕ} (ha : R ≤ a) :
    sieveProfile k (m + 1) (Fin.cons (Real.log a / Real.log R) t) = 0 := by
  apply sieveProfile_cons_zero_of_one_le k m t ht
  have hlogR : 0 < Real.log R := Real.log_pos (by exact_mod_cast hR)
  apply (le_div_iff₀ hlogR).mpr
  rw [one_mul]
  exact Real.log_le_log (by exact_mod_cast (Nat.zero_lt_one.trans hR)) (by exact_mod_cast ha)

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedBaseTuple_eq_insertNth
#print axioms Erdos4b.FGKMT.sieveProfile_pinnedBaseTuple
#print axioms Erdos4b.FGKMT.sieveProfile_logSlice_zero_of_ge
