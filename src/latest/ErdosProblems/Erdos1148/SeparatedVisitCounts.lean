import ErdosProblems.Erdos1148.DiscreteCuspRuns
import Mathlib.Data.Fintype.Card

/-! # Counting visits whose starting times are uniformly separated -/

namespace Erdos1148.DukeArithmetic

open scoped MatrixGroups

theorem card_le_of_separated_nat (s : Finset ℕ) {N : ℕ} {τ : ℝ} (hτ : 0 < τ)
    (hbound : ∀ k ∈ s, k ≤ N)
    (hsep : ∀ a ∈ s, ∀ b ∈ s, a < b → τ ≤ (b : ℝ) - a) :
    (s.card : ℝ) ≤ (N : ℝ) / τ + 1 := by
  classical
  let f : s → Fin (⌊(N : ℝ) / τ⌋₊ + 1) := fun k =>
    ⟨⌊(k.val : ℝ) / τ⌋₊, Nat.lt_succ_of_le (Nat.floor_mono
      (div_le_div_of_nonneg_right (by exact_mod_cast hbound k.val k.property) hτ.le))⟩
  have hbin (a b : s) (hab : f a = f b) : (b.val : ℝ) - a.val < τ := by
    have heq : ⌊(a.val : ℝ) / τ⌋₊ = ⌊(b.val : ℝ) / τ⌋₊ := congrArg Fin.val hab
    have hlow := (le_div_iff₀ hτ).mp
      (Nat.floor_le (div_nonneg (Nat.cast_nonneg a.val) hτ.le))
    have hupp := (div_lt_iff₀ hτ).mp (Nat.lt_floor_add_one ((b.val : ℝ) / τ))
    rw [heq] at hlow
    nlinarith
  have hinj : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    rcases lt_trichotomy a.val b.val with hlt | heq | hgt
    · have hs := hsep a.val a.property b.val b.property hlt
      linarith [hbin a b hab]
    · exact heq
    · have hs := hsep b.val b.property a.val a.property hgt
      linarith [hbin b a hab.symm]
  have hcard : s.card ≤ ⌊(N : ℝ) / τ⌋₊ + 1 := by
    simpa only [Fintype.card_coe, Fintype.card_fin] using Fintype.card_le_of_injective f hinj
  have hcast : (s.card : ℝ) ≤ (⌊(N : ℝ) / τ⌋₊ : ℝ) + 1 := by exact_mod_cast hcard
  have hfloor := Nat.floor_le (div_nonneg (Nat.cast_nonneg N) hτ.le)
  linarith

theorem cusp_run_starts_card_le (g : SL(2, ℝ)) {H : ℝ} (hH : 1 < H)
    (s : Finset ℕ) {N : ℕ} (hbound : ∀ k ∈ s, k ≤ N)
    (hvisits : ∀ k ∈ s, modularMk (g * diagonalFlow (k : ℝ)) ∈ modularCusp H)
    (hexits : ∀ a ∈ s, ∀ b ∈ s, a < b → ∃ t ∈ Set.Icc (a : ℝ) (b : ℝ),
      modularMk (g * diagonalFlow t) ∉ modularCusp H) :
    (s.card : ℝ) ≤ (N : ℝ) / (4 * Real.log H) + 1 := by
  apply card_le_of_separated_nat s (mul_pos (by norm_num) (Real.log_pos hH)) hbound
  intro a ha b hb hab
  obtain ⟨t, ht, hexit⟩ := hexits a ha b hb hab
  exact (cusp_time_gap_gt_of_intermediate_exit g (by linarith) ht
    (hvisits a ha) (hvisits b hb) hexit).le

end Erdos1148.DukeArithmetic
