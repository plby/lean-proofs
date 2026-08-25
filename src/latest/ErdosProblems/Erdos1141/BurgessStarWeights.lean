import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Logic.Equiv.Prod
import Mathlib.Tactic

/-!
# Summing independent difference weights around a distinguished tuple entry
-/

namespace Pollack17.Burgess

open scoped BigOperators

noncomputable def starWeight {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) : ℝ :=
  ∏ j : {j : Fin n // j ≠ i}, w (v i) (v j)

theorem starWeight_nonneg {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (hw : ∀ a b, 0 ≤ w a b) (v : Fin n → α) (i : Fin n) :
    0 ≤ starWeight w v i := Finset.prod_nonneg fun _ _ => hw _ _

theorem starWeight_eq_prod_erase {α : Type*} {n : ℕ} (w : α → α → ℝ)
    (v : Fin n → α) (i : Fin n) :
    starWeight w v i = ∏ j ∈ Finset.univ.erase i, w (v i) (v j) := by
  exact (Finset.prod_subtype (p := fun j => j ≠ i)
    (Finset.univ.erase i) (by simp) (fun j => w (v i) (v j))).symm

theorem sum_starWeight {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) =
      ∑ a : α, (∑ b : α, w a b) ^ (n - 1) := by
  classical
  let e := Equiv.funSplitAt i α
  let F : (α × ({j : Fin n // j ≠ i} → α)) → ℝ :=
    fun ab => ∏ j : {j : Fin n // j ≠ i}, w ab.1 (ab.2 j)
  have heq (v : Fin n → α) : starWeight w v i = F (e v) := rfl
  have hcard : Fintype.card {j : Fin n // j ≠ i} = n - 1 := by
    simp [Fintype.card_subtype_compl]
  calc
    _ = ∑ v : Fin n → α, F (e v) := Finset.sum_congr rfl fun v _ => heq v
    _ = ∑ ab, F ab := e.sum_comp F
    _ = ∑ a : α, ∑ b : ({j : Fin n // j ≠ i} → α),
        ∏ j : {j : Fin n // j ≠ i}, w a (b j) := Fintype.sum_prod_type _
    _ = ∑ a : α, ∏ _j : {j : Fin n // j ≠ i}, ∑ b : α, w a b := by
      apply Finset.sum_congr rfl
      intro a _
      rw [Fintype.prod_sum]
    _ = _ := by simp [hcard]

theorem sum_starWeight_le {α : Type*} [Fintype α] {n : ℕ}
    (w : α → α → ℝ) (hw : ∀ a b, 0 ≤ w a b) {B : ℝ}
    (hB : ∀ a : α, ∑ b : α, w a b ≤ B) (i : Fin n) :
    (∑ v : Fin n → α, starWeight w v i) ≤ (Fintype.card α : ℝ) * B ^ (n - 1) := by
  rw [sum_starWeight]
  calc
    _ ≤ ∑ _a : α, B ^ (n - 1) := Finset.sum_le_sum fun a _ =>
      pow_le_pow_left₀ (Finset.sum_nonneg fun b _ => hw a b) (hB a) _
    _ = _ := by simp

end Pollack17.Burgess
