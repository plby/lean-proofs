/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.CliqueExtensionGeometry

/-! # A fixed polynomial-size index family for simultaneous clique-extension estimates -/

namespace Erdos207

open Finset

noncomputable section

def smallCliqueFamily {V : Type*} [DecidableEq V]
    (G : SimpleGraph V) (D : Finset V) : Finset (Finset V) := by
  classical
  exact D.powerset.filter (fun S ↦ 2 ≤ S.card ∧ S.card ≤ 4 ∧ cliquePattern S ≤ G)

theorem mem_smallCliqueFamily_iff
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D S : Finset V) :
    S ∈ smallCliqueFamily G D ↔ S ⊆ D ∧ 2 ≤ S.card ∧ S.card ≤ 4 ∧ cliquePattern S ≤ G := by
  classical
  simp only [smallCliqueFamily, mem_filter, mem_powerset]

theorem smallCliqueFamily_card_le
    {V : Type*} [DecidableEq V] (G : SimpleGraph V) (D : Finset V) :
    (smallCliqueFamily G D).card ≤ 3 * (D.card + 1) ^ 4 := by
  classical
  have hsub : smallCliqueFamily G D ⊆ (Icc 2 4).biUnion (fun k ↦ D.powersetCard k) := by
    intro S hS
    have hm := (mem_smallCliqueFamily_iff G D S).mp hS
    exact mem_biUnion.mpr ⟨S.card, mem_Icc.mpr ⟨hm.2.1, hm.2.2.1⟩,
      mem_powersetCard.mpr ⟨hm.1, rfl⟩⟩
  calc
    _ ≤ ((Icc 2 4).biUnion (fun k ↦ D.powersetCard k)).card := card_le_card hsub
    _ ≤ ∑ k ∈ Icc 2 4, (D.powersetCard k).card := card_biUnion_le
    _ ≤ ∑ _k ∈ Icc 2 4, (D.card + 1) ^ 4 := by
      apply sum_le_sum
      intro k hk
      rw [card_powersetCard]
      exact (Nat.choose_le_pow _ _).trans
        ((Nat.pow_le_pow_left (Nat.le_succ _) k).trans
          (Nat.pow_le_pow_right (by omega) (mem_Icc.mp hk).2))
    _ = _ := by simp only [sum_const, nsmul_eq_mul, Nat.card_Icc]; norm_num

end

end Erdos207
