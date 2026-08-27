/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedSplit

/-! # Genuine integer tuple factorization on contributing split terms -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α : Type*} [Fintype α] [DecidableEq α]

def pinnedBaseTuple {m : ℕ} (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (a : α → Option Unit) (i : Fin (m + 1)) : ℕ :=
  assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb r) i *
    if i = j then assignmentPrimeProduct p a else 1

omit [DecidableEq α] in
theorem pinnedBaseTuple_pos {m : ℕ} {p : α → ℕ} (hp : ∀ q, 0 < p q)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) (a : α → Option Unit)
    (i : Fin (m + 1)) : 0 < pinnedBaseTuple p j r a i := by
  apply Nat.mul_pos (assignmentPrimeTuple_pos hp _ i)
  split_ifs
  · exact assignmentPrimeProduct_pos hp a
  · exact Nat.zero_lt_one

omit [DecidableEq α] in
theorem pinnedBaseTuple_pin {m : ℕ} (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (a : α → Option Unit) :
    pinnedBaseTuple p j r a j = assignmentPrimeProduct p a := by
  rw [pinnedBaseTuple, if_pos rfl,
    mapPrimeAssignment_tuple_missing p j.succAboveEmb r j (fun i => Fin.succAbove_ne j i),
    one_mul]

omit [DecidableEq α] in
theorem pinnedBaseTuple_unpinned {m : ℕ} (p : α → ℕ) (j : Fin (m + 1))
    (r : α → Option (Fin m)) (a : α → Option Unit) (i : Fin m) :
    pinnedBaseTuple p j r a (j.succAbove i) = assignmentPrimeTuple p r i := by
  rw [pinnedBaseTuple, if_neg (Fin.succAbove_ne j i), mul_one]
  exact mapPrimeAssignment_tuple_image p j.succAboveEmb r i

theorem localPinnedSplit_integer_factorization {m : ℕ} {v : ℝ}
    (j : Fin (m + 1)) (r : Option (Fin m)) (a : Option Unit) (b : Option (Fin m))
    (h : localPinnedSplitWeight v r a b ≠ 0) (p : ℕ) (i : Fin (m + 1)) :
    (if localPinnedSplitState j r a b = some i then p else 1) =
      (if r.map j.succAboveEmb = some i then p else 1) *
        (if i = j then if a = none then 1 else p else 1) *
        (if b.map j.succAboveEmb = some i then p else 1) := by
  cases r <;> cases a <;> cases b <;>
    simp_all [localPinnedSplitWeight, localPinnedBaseWeight, localPinnedDivisorWeight,
      localPinnedMovedCoeff, localPinnedSplitState, eq_comm]

omit [DecidableEq α] in
theorem pinnedSplitAssignment_tuple_factorization {m : ℕ} (p : α → ℕ)
    (j : Fin (m + 1)) (r : α → Option (Fin m)) (a : α → Option Unit)
    (b : α → Option (Fin m))
    (h : pinnedBaseFactor p r * pinnedDivisorFactor p r a * pinnedMovedFactor p r a b ≠ 0) :
    assignmentPrimeTuple p (pinnedSplitAssignment j r a b) =
      fun i => pinnedBaseTuple p j r a i *
        assignmentPrimeTuple p (mapPrimeAssignment j.succAboveEmb b) i := by
  rw [← pinnedSplitWeight_product] at h
  funext i
  have hpin : (if i = j then assignmentPrimeProduct p a else 1) =
      ∏ q, if i = j then if a q = none then 1 else p q else 1 := by
    by_cases hij : i = j <;> simp [hij, assignmentPrimeProduct]
  simp only [pinnedBaseTuple, hpin, assignmentPrimeTuple, pinnedSplitAssignment,
    mapPrimeAssignment, ← Finset.prod_mul_distrib]
  apply Finset.prod_congr rfl
  intro q hq
  exact localPinnedSplit_integer_factorization j (r q) (a q) (b q)
    ((Finset.prod_ne_zero_iff.mp h) q hq) (p q) i

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.pinnedSplitAssignment_tuple_factorization
