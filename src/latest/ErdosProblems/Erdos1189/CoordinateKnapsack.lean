/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
The finite score-cutoff inequality for divisor entropy.
Informal source: BBMST Lemma 6.3, retaining the negative cutoff-weight term.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.CountingFibres

namespace Erdos1189

open Finset

noncomputable def coordinateMass (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ c ∈ S, logIncrement c.2

noncomputable def coordinateWeight (S : Finset (ℕ × ℕ)) : ℝ :=
  ∑ c ∈ S, ((c.1 : ℝ) - 1)

lemma coordinateMass_nonneg (S : Finset (ℕ × ℕ)) : 0 ≤ coordinateMass S :=
  sum_nonneg fun c _ => (logIncrement_pos c.2).le

lemma counting_coordinate_weight (x : ℝ) :
    coordinateWeight (countingCoordinates x) = (countingSize x : ℝ) - 1 := by
  rw [countingSize_eq, Nat.cast_add, Nat.cast_one, Nat.cast_sum, add_sub_cancel_left]
  apply sum_congr rfl
  intro c hc
  rw [Nat.cast_sub (mem_countingCoordinates.mp hc).1.one_lt.le, Nat.cast_one]

lemma coordinate_knapsack (S : Finset (ℕ × ℕ)) (hS : ∀ c ∈ S, c.1.Prime)
    {x : ℝ} (hx : 0 < x) :
    coordinateMass S ≤ coordinateMass (countingCoordinates x) +
      (coordinateWeight S - coordinateWeight (countingCoordinates x)) / x := by
  classical
  let f := fun c : ℕ × ℕ => logIncrement c.2 - ((c.1 : ℝ) - 1) / x
  have hneg : ∑ c ∈ S \ countingCoordinates x, f c ≤ 0 := by
    apply sum_nonpos
    intro c hc
    obtain ⟨hcS, hcNot⟩ := mem_sdiff.mp hc
    have hscore : x ≤ coordinateScore c.1 c.2 :=
      le_of_not_gt (fun hs => hcNot (mem_countingCoordinates.mpr ⟨hS c hcS, hs⟩))
    have hprod := (le_div_iff₀ (logIncrement_pos c.2)).mp hscore
    apply sub_nonpos.mpr
    exact (le_div_iff₀ hx).mpr (by nlinarith)
  have hpos : 0 ≤ ∑ c ∈ countingCoordinates x \ S, f c := by
    apply sum_nonneg
    intro c hc
    have hscore := (mem_countingCoordinates.mp (mem_sdiff.mp hc).1).2
    have hprod := (div_lt_iff₀ (logIncrement_pos c.2)).mp hscore
    apply sub_nonneg.mpr
    exact (div_le_iff₀ hx).mpr (by nlinarith)
  have hsplit (U V : Finset (ℕ × ℕ)) :
      (∑ c ∈ U \ V, f c) + ∑ c ∈ U ∩ V, f c = ∑ c ∈ U, f c := by
    have hd : Disjoint (U \ V) (U ∩ V) := disjoint_left.mpr fun c hc hd =>
      (mem_sdiff.mp hc).2 (mem_inter.mp hd).2
    rw [← sum_union hd, sdiff_union_inter]
  have hleft := hsplit S (countingCoordinates x)
  have hright := hsplit (countingCoordinates x) S
  rw [inter_comm (countingCoordinates x) S] at hright
  have hsum : ∑ c ∈ S, f c ≤ ∑ c ∈ countingCoordinates x, f c := by linarith
  dsimp only [f] at hsum
  rw [sum_sub_distrib, sum_sub_distrib, ← sum_div, ← sum_div] at hsum
  change coordinateMass S - coordinateWeight S / x ≤
    coordinateMass (countingCoordinates x) - coordinateWeight (countingCoordinates x) / x at hsum
  rw [sub_div]
  linarith

end Erdos1189
