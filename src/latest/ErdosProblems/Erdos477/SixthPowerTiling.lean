/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Finite avoidance and the unconditional tiling of the integers by nonnegative sixth powers.
Informal source: Liam Price (GPT 5.6 Sol Pro), Large Powers Tile the Integers.
https://www.overleaf.com/read/whnsywnmykqm#4b6ba0
Formal author: Codex.
-/

import ErdosProblems.Erdos477.Counting.BadShiftCount

namespace Erdos477

open scoped BigOperators

theorem sixth_power_finiteAvoidance : FiniteAvoidance (PowerValues 6) := by
  classical
  intro C hC
  have hex (c : C) := Counting.exists_bad_shift_bound c.val (hC c.val c.property)
  choose M hM hbound using hex
  obtain ⟨N, hN, hgap⟩ := Counting.exists_nat_sublinear_gap (∑ c : C, M c)
  have havoid : ∃ t ∈ Finset.Icc 1 N, ∀ c ∈ C, ¬IsBadShift c t := by
    by_contra! h
    let U : C → Finset ℕ := fun c => (Finset.Icc 1 N).filter (IsBadShift c.val)
    have heach (c : C) : ((U c).card : ℝ) ≤ M c * (N : ℝ) ^ ((249 : ℝ) / 250) := by
      apply hbound c N hN
      intro t ht
      have ht' := Finset.mem_filter.mp ht
      have hrange := Finset.mem_Icc.mp ht'.1
      exact ⟨hrange.1, hrange.2, ht'.2⟩
    have hsub : Finset.Icc 1 N ⊆ Finset.univ.biUnion U := by
      intro t ht
      obtain ⟨c, hc, hbad⟩ := h t ht
      exact Finset.mem_biUnion.mpr
        ⟨⟨c, hc⟩, Finset.mem_univ _, Finset.mem_filter.mpr ⟨ht, hbad⟩⟩
    have hnat : N ≤ ∑ c : C, (U c).card := by
      simpa only [Nat.card_Icc, Nat.add_sub_cancel] using
        (Finset.card_le_card hsub).trans Finset.card_biUnion_le
    have hreal : (N : ℝ) ≤ ∑ c : C, ((U c).card : ℝ) := by exact_mod_cast hnat
    have hsum : (N : ℝ) ≤ (∑ c : C, M c) * (N : ℝ) ^ ((249 : ℝ) / 250) := by
      rw [Finset.sum_mul]
      exact hreal.trans (Finset.sum_le_sum (fun c _ => heach c))
    exact (not_lt_of_ge hsum) hgap
  obtain ⟨t, _, ht⟩ := havoid
  refine ⟨(t : ℤ) ^ 6, ⟨t, rfl⟩, ?_⟩
  intro c hc
  exact fun h => ht c hc ((mem_difference_iff_isBadShift c t).mp h)

theorem exists_sixth_power_tiling : ∃ A : Set ℤ, IsTiling A (PowerValues 6) :=
  exists_tiling_of_finiteAvoidance sixth_power_finiteAvoidance

#print axioms sixth_power_finiteAvoidance
-- 'Erdos477.sixth_power_finiteAvoidance' depends on axioms:
-- [propext, Classical.choice, Quot.sound]
#print axioms exists_sixth_power_tiling
-- 'Erdos477.exists_sixth_power_tiling' depends on axioms:
-- [propext, Classical.choice, Quot.sound]

end Erdos477
