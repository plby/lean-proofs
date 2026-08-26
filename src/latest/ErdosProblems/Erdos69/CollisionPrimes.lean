import ErdosProblems.Erdos69.AugmentedModulus
import Mathlib.Data.Nat.Dist

/-! # Primes at which two retained shifts coincide -/

open scoped BigOperators

namespace Erdos69.Elementary

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def collisionProduct (r : ι → ℕ) : ℕ :=
  ∏ i, ∏ j, if i = j then 1 else Nat.dist (r i) (r j)

theorem collisionProduct_pos (r : ι → ℕ) (hr : Function.Injective r) :
    0 < collisionProduct r := by
  apply Finset.prod_pos
  intro i hi
  apply Finset.prod_pos
  intro j hj
  split_ifs with hij
  · omega
  · exact Nat.dist_pos_of_ne (fun heq ↦ hij (hr heq))

theorem dist_dvd_collisionProduct (r : ι → ℕ) {i j : ι} (hij : i ≠ j) :
    Nat.dist (r i) (r j) ∣ collisionProduct r := by
  have h₁ : (if i = j then 1 else Nat.dist (r i) (r j)) ∣
      ∏ k, if i = k then 1 else Nat.dist (r i) (r k) :=
    Finset.dvd_prod_of_mem _ (Finset.mem_univ j)
  rw [if_neg hij] at h₁
  exact h₁.trans (Finset.dvd_prod_of_mem _ (Finset.mem_univ i))

theorem dvd_dist_of_modEq {p a b : ℕ} (h : a ≡ b [MOD p]) : p ∣ Nat.dist a b := by
  rcases le_total a b with hab | hba
  · rw [Nat.dist_eq_sub_of_le hab]
    exact (Nat.modEq_iff_dvd' hab).mp h
  · rw [Nat.dist_eq_sub_of_le_right hba]
    exact (Nat.modEq_iff_dvd' hba).mp h.symm

theorem distinct_residues_outside_augmentedModulus (r : ι → ℕ)
    (hr : Function.Injective r) (A p : ℕ) (hp : p.Prime)
    (hpQ : ¬p ∣ augmentedModulus A (collisionProduct r)) :
    ∀ i j, r i ≡ r j [MOD p] → i = j := by
  intro i j hij
  by_contra hne
  apply hpQ
  exact prime_dvd_augmentedModulus (collisionProduct_pos r hr).ne' hp
    ((dvd_dist_of_modEq hij).trans (dist_dvd_collisionProduct r hne))

theorem collisionProduct_le (r : ι → ℕ) (M : ℕ) (hM : 1 ≤ M) (hr : ∀ i, r i ≤ M) :
    collisionProduct r ≤ M ^ (Fintype.card ι * Fintype.card ι) := by
  have hdist (i j : ι) : Nat.dist (r i) (r j) ≤ M := by
    rw [Nat.dist_eq_max_sub_min]
    exact (Nat.sub_le _ _).trans (max_le (hr i) (hr j))
  calc
    collisionProduct r ≤ ∏ _i : ι, ∏ _j : ι, M := by
      apply Finset.prod_le_prod'
      intro i hi
      apply Finset.prod_le_prod'
      intro j hj
      split_ifs <;> first | exact hM | exact hdist i j
    _ = _ := by simp [← pow_mul]

theorem log_collisionProduct_le (r : ι → ℕ) (hr : Function.Injective r)
    (M : ℕ) (hM : 1 ≤ M) (hrM : ∀ i, r i ≤ M) :
    Real.log (collisionProduct r : ℝ) ≤ (Fintype.card ι : ℝ) ^ 2 * Real.log M := by
  have hD := collisionProduct_pos r hr
  have hle := collisionProduct_le r M hM hrM
  have hlog : Real.log (collisionProduct r : ℝ) ≤
      Real.log ((M : ℝ) ^ (Fintype.card ι * Fintype.card ι)) := by
    apply Real.log_le_log (by positivity)
    exact_mod_cast hle
  rw [Real.log_pow, Nat.cast_mul] at hlog
  simpa only [pow_two] using hlog

end Erdos69.Elementary
