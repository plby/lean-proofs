/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPinnedTransform
import ErdosProblems.Erdos4b.FGKMTAssignmentRecovery
import Mathlib.Data.Fin.Embedding

/-! # Removing a coordinate means exactly that its divisor is one -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

variable {α ι κ : Type*} [Fintype α] [DecidableEq ι] [DecidableEq κ]

theorem mapPrimeAssignment_tuple_image (p : α → ℕ) (e : ι ↪ κ)
    (d : α → Option ι) (i : ι) :
    assignmentPrimeTuple p (mapPrimeAssignment e d) (e i) = assignmentPrimeTuple p d i := by
  apply Finset.prod_congr rfl
  intro q _hq
  cases hd : d q <;> simp [mapPrimeAssignment, hd, e.injective.eq_iff]

omit [DecidableEq ι] in
theorem mapPrimeAssignment_tuple_missing (p : α → ℕ) (e : ι ↪ κ)
    (d : α → Option ι) (j : κ) (hj : ∀ i, e i ≠ j) :
    assignmentPrimeTuple p (mapPrimeAssignment e d) j = 1 := by
  apply Finset.prod_eq_one
  intro q _hq
  cases hd : d q <;> simp [mapPrimeAssignment, hd, hj]

theorem assignmentPrimeTuple_eq_one_iff {p : α → ℕ} (hp : ∀ q, (p q).Prime)
    (d : α → Option ι) (i : ι) :
    assignmentPrimeTuple p d i = 1 ↔ ∀ q, d q ≠ some i := by
  constructor
  · intro h q hq
    have hdiv : p q ∣ assignmentPrimeTuple p d i :=
      (by simp only [if_pos hq, dvd_refl] : p q ∣ if d q = some i then p q else 1).trans
        (Finset.dvd_prod_of_mem _ (Finset.mem_univ q))
    rw [h] at hdiv
    exact (hp q).ne_one (Nat.dvd_one.mp hdiv)
  · intro h
    exact Finset.prod_eq_one fun q _hq => if_neg (h q)

omit [Fintype α] in
theorem exists_map_unpinned_iff {m : ℕ} (j : Fin (m + 1))
    (s : α → Option (Fin (m + 1))) :
    (∃ d : α → Option (Fin m), mapPrimeAssignment j.succAboveEmb d = s) ↔
      ∀ q, s q ≠ some j := by
  constructor
  · rintro ⟨d, rfl⟩ q
    cases d q <;> simp [mapPrimeAssignment]
  · intro hs
    have hpoint (q : α) : ∃ u : Option (Fin m), u.map j.succAboveEmb = s q := by
      cases heq : s q with
      | none => exact ⟨none, rfl⟩
      | some i =>
        have hij : i ≠ j := fun h => hs q (by simpa only [h] using heq)
        obtain ⟨l, hl⟩ := Fin.exists_succAbove_eq hij
        exact ⟨some l, congrArg some hl⟩
    choose d hd using hpoint
    exact ⟨d, funext hd⟩

theorem exists_map_unpinned_iff_divisor_one {m : ℕ} {p : α → ℕ}
    (hp : ∀ q, (p q).Prime) (j : Fin (m + 1))
    (s : α → Option (Fin (m + 1))) :
    (∃ d : α → Option (Fin m), mapPrimeAssignment j.succAboveEmb d = s) ↔
      assignmentPrimeTuple p s j = 1 := by
  rw [exists_map_unpinned_iff, assignmentPrimeTuple_eq_one_iff hp]

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.exists_map_unpinned_iff_divisor_one
