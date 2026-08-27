/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTAssignmentReindex

/-! # Nonnegative upper reindexing into a coordinate box -/

namespace Erdos4b.FGKMT

noncomputable section

open scoped BigOperators

theorem sum_assignments_le_sum_box_of_coord_support {α : Type*} [Fintype α]
    [DecidableEq α] {p : α → ℕ} (hp : ∀ q, (p q).Prime) (hinj : Function.Injective p)
    (m M B : ℕ) (g : ℕ → ℝ) (hg : ∀ l : ℕ, l.Prime → ¬l ∣ M → 0 ≤ g l)
    (F : (Fin m → ℕ) → ℝ) (hF : ∀ t, 0 ≤ F t)
    (hFB : ∀ t, F t ≠ 0 → ∀ i, t i ≤ B) :
    (∑ r : α → Option (Fin m), F (assignmentPrimeTuple p r) *
      roughSieveWeight M g (assignmentPrimeProduct p r)) ≤
      ∑ e : Fin m → Fin (B + 1), F (fun i => (e i).val) *
        roughSieveWeight M g (∏ i, (e i).val) := by
  classical
  let f := fun r : α → Option (Fin m) =>
    F (assignmentPrimeTuple p r) * roughSieveWeight M g (assignmentPrimeProduct p r)
  let G := fun e : Fin m → Fin (B + 1) =>
    F (fun i => (e i).val) * roughSieveWeight M g (∏ i, (e i).val)
  let S := Finset.univ.filter (fun r => f r ≠ 0)
  let code := fun r : α → Option (Fin m) => fun i : Fin m =>
    (⟨min (assignmentPrimeTuple p r i) B, Nat.lt_succ_of_le (min_le_right _ _)⟩ : Fin (B + 1))
  have hcoord {r : α → Option (Fin m)} (hr : r ∈ S) :
      (fun i => (code r i).val) = assignmentPrimeTuple p r := by
    have hnon := (mul_ne_zero_iff.mp (show f r ≠ 0 from (Finset.mem_filter.mp hr).2)).1
    funext i
    exact min_eq_left (hFB _ hnon i)
  have heq {r : α → Option (Fin m)} (hr : r ∈ S) : f r = G (code r) := by
    dsimp only [G]
    rw [hcoord hr, prod_assignmentPrimeTuple]
  have hinjS : Set.InjOn code (↑S : Set (α → Option (Fin m))) := by
    intro r hr s hs hrs
    apply assignmentPrimeTuple_injective hp hinj
    rw [← hcoord hr, ← hcoord hs, hrs]
  have hG (e : Fin m → Fin (B + 1)) : 0 ≤ G e :=
    mul_nonneg (hF _) (roughSieveWeight_nonneg M g hg _)
  calc
    _ = ∑ r ∈ S, f r := by
      rw [Finset.sum_filter]
      apply Finset.sum_congr rfl
      intro r _hr
      change f r = if f r ≠ 0 then f r else 0
      by_cases hz : f r = 0 <;> simp [hz]
    _ = ∑ r ∈ S, G (code r) := Finset.sum_congr rfl (fun r hr => heq hr)
    _ = ∑ e ∈ S.image code, G e := (Finset.sum_image hinjS).symm
    _ ≤ ∑ e, G e := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun e _he _hnot => hG e)
    _ = _ := rfl

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.sum_assignments_le_sum_box_of_coord_support
