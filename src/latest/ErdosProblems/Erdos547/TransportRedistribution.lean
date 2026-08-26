import ErdosProblems.Erdos547.Transport

/-!
# Redistributing transport between two rows without changing any column total
-/

noncomputable section

namespace Erdos547.DPRS.Transport

open Finset
open scoped BigOperators

variable {V : Type*} [Fintype V] {P : V → V → Prop} {a b : V → ℝ}

open scoped Classical in
def redistributeWeight (f : Transport P a b) (x z y : V) (t : ℝ) (u v : V) : ℝ :=
  f.weight u v + (if u = x ∧ v = y then t else 0) - (if u = z ∧ v = y then t else 0)

open scoped Classical in
theorem redistributeWeight_row (f : Transport P a b) (x z y : V) (t : ℝ) (u : V) :
    (∑ v, f.redistributeWeight x z y t u v) =
      f.row u + (if u = x then t else 0) - (if u = z then t else 0) := by
  classical
  have hcell (r : V) : (∑ v, if u = r ∧ v = y then t else (0 : ℝ)) =
      if u = r then t else 0 := by
    by_cases h : u = r
    · simp only [h, true_and, if_true, Finset.sum_ite_eq', Finset.mem_univ]
    · simp only [h, false_and, if_false, Finset.sum_const_zero]
  simp only [redistributeWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib, hcell, row]

theorem redistributeWeight_col (f : Transport P a b) (x z y : V) (t : ℝ) (v : V) :
    (∑ u, f.redistributeWeight x z y t u v) = f.col v := by
  classical
  simp only [redistributeWeight, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  by_cases hv : v = y <;> simp [hv, col]

open scoped Classical in
def redistribute (f : Transport P a b) {x z y : V} (hxz : x ≠ z) (hxy : P x y)
    (t : ℝ) (ht : 0 ≤ t) (hrow : f.row x + t ≤ a x) (hweight : t ≤ f.weight z y) :
    Transport P a b where
  weight := f.redistributeWeight x z y t
  nonnegative u v := by
    by_cases hv : v = y
    · subst v
      by_cases hu : u = x
      · subst u
        simp only [redistributeWeight, and_true, if_true, hxz, if_false, sub_zero]
        exact add_nonneg (f.nonnegative x y) ht
      · by_cases huz : u = z
        · subst u
          simp only [redistributeWeight, hu, false_and, if_false, and_self, if_true, add_zero]
          exact sub_nonneg.mpr hweight
        · simp only [redistributeWeight, hu, huz, false_and, if_false, add_zero, sub_zero]
          exact f.nonnegative u y
    · simp only [redistributeWeight, hv, and_false, if_false, add_zero, sub_zero]
      exact f.nonnegative u v
  supported u v huv := by
    have hx : ¬ (u = x ∧ v = y) := by rintro ⟨rfl, rfl⟩; exact huv hxy
    have hz : ¬ (u = z ∧ v = y) ∨ t = 0 := by
      by_cases h : u = z ∧ v = y
      · right
        obtain ⟨huz, hvy⟩ := h
        rw [← huz, ← hvy, f.supported u v huv] at hweight
        exact le_antisymm hweight ht
      · exact Or.inl h
    rcases hz with hz | rfl
    · simp only [redistributeWeight, f.supported u v huv, if_neg hx, if_neg hz,
        add_zero, sub_zero]
    · simp only [redistributeWeight, f.supported u v huv, ite_self, add_zero, sub_zero]
  row_bound u := by
    rw [f.redistributeWeight_row]
    by_cases hu : u = x
    · subst u
      simpa only [if_pos rfl, if_neg hxz, if_true, sub_zero] using hrow
    · rw [if_neg hu, add_zero]
      split_ifs
      · exact (sub_le_self _ ht).trans (f.row_bound u)
      · rw [sub_zero]
        exact f.row_bound u
  col_bound v := by
    rw [f.redistributeWeight_col]
    exact f.col_bound v

theorem redistribute_total (f : Transport P a b) {x z y : V} (hxz : x ≠ z) (hxy : P x y)
    (t : ℝ) (ht : 0 ≤ t) (hrow : f.row x + t ≤ a x) (hweight : t ≤ f.weight z y) :
    (f.redistribute hxz hxy t ht hrow hweight).total = f.total := by
  rw [← sum_col, ← f.sum_col]
  exact Finset.sum_congr rfl fun v _ ↦ f.redistributeWeight_col x z y t v

end Erdos547.DPRS.Transport

#print axioms Erdos547.DPRS.Transport.redistribute_total
