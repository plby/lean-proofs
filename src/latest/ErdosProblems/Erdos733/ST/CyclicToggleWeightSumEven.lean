import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.BigOperators.Ring.Nat
import ErdosProblems.Erdos733.ST.Preamble

open Classical
noncomputable section

-- [TABLET NODE: CyclicToggleWeightSumEven]
lemma CyclicToggleWeightSumEven {α : Type*} [Fintype α]
    (σ : Equiv.Perm α) (inside : α → Bool) (w : α → ℕ)
    (hw : ∀ p : α, Odd (w p) ↔ inside p ≠ inside (σ p)) :
    Even (∑ p : α, w p) := by
-- BODY
  let f : α → ZMod 2 := fun p => if inside p then 1 else 0
  have hterm : ∀ p : α,
      ((if inside p = inside (σ p) then 0 else 1 : ℕ) : ZMod 2) = f p + f (σ p) := by
    intro p
    by_cases hp : inside p
    · by_cases hq : inside (σ p)
      · simp [f, hp, hq]
        decide
      · simp [f, hp, hq]
    · by_cases hq : inside (σ p)
      · simp [f, hp, hq]
      · simp [f, hp, hq]
  have htoggleSum :
      Even (∑ p : α, if inside p = inside (σ p) then 0 else 1) := by
    have hsum_cast :
        ((∑ p : α, if inside p = inside (σ p) then 0 else 1 : ℕ) : ZMod 2) =
          ∑ p : α, (f p + f (σ p)) := by
      rw [Nat.cast_sum]
      exact Finset.sum_congr rfl (fun p _ => hterm p)
    have hperm : (∑ p : α, f (σ p)) = ∑ p : α, f p := by
      simpa using (Equiv.sum_comp σ f)
    have hzero : ((∑ p : α, if inside p = inside (σ p) then 0 else 1 : ℕ) : ZMod 2) = 0 := by
      rw [hsum_cast]
      rw [Finset.sum_add_distrib, hperm]
      rw [← two_mul]
      rw [show (2 : ZMod 2) = 0 by decide]
      simp
    exact ZMod.natCast_eq_zero_iff_even.mp hzero
  have htoggleCard :
      Even (Finset.univ.filter (fun p : α => inside p ≠ inside (σ p))).card := by
    convert htoggleSum using 1
    rw [Finset.card_eq_sum_ones, Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro p _
    by_cases h : inside p = inside (σ p)
    · simp [h]
    · simp [h]
  rw [Finset.even_sum_iff_even_card_odd]
  have hfilter_eq :
      Finset.univ.filter (fun x => Odd (w x)) =
        Finset.univ.filter (fun x => inside x ≠ inside (σ x)) := by
    apply Finset.filter_congr
    intro p _
    exact hw p
  simpa [hfilter_eq] using htoggleCard
