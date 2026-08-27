/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.IndependentBernoulliRelativeTail

/-! # Extracting one subfamily with all prescribed incidence counts regular -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_regular_subfamily_of_fractional_weights
    {I J : Type*} [Fintype I] [DecidableEq I] [Fintype J]
    (A : Finset I) (incident : J → I → Prop) [∀ j, DecidablePred (incident j)]
    (w : I → ℝ) (mu eta : ℝ)
    (hw : ∀ i ∈ A, 0 ≤ w i ∧ w i ≤ 1)
    (heta : 0 < eta) (heta1 : eta ≤ 1)
    (hmean : ∀ j, (∑ i ∈ A.filter (incident j), w i) = mu)
    (hfailure : 2 * Fintype.card J * Real.exp (-eta ^ 2 * mu / 4) < 1) :
    ∃ R ⊆ A, ∀ j, |((R.filter (incident j)).card : ℝ) - mu| ≤ eta * mu := by
  classical
  let p : I → ℝ≥0 := fun i ↦ ⟨if i ∈ A then w i else 0, by
    split_ifs with hi
    · exact (hw i hi).1
    · exact le_rfl⟩
  have hp : ∀ i, p i ≤ 1 := by
    intro i
    change (if i ∈ A then w i else 0) ≤ (1 : ℝ)
    split_ifs with hi
    · exact (hw i hi).2
    · norm_num
  let S : J → Finset I := fun j ↦ A.filter (incident j)
  have hmu : ∀ j, (∑ i ∈ S j, (p i : ℝ)) = mu := by
    intro j
    calc
      _ = ∑ i ∈ A.filter (incident j), w i := sum_congr rfl
        (fun i hi ↦ if_pos (mem_filter.mp hi).1)
      _ = mu := hmean j
  let L := FiniteLaw.independentBits p hp
  let Bad := fun (ω : I → Bool) ↦ ∃ j,
    eta * mu < |((S j).filter (fun i ↦ ω i = true)).card - mu|
  have htail : (L.probability Bad : ℝ) < 1 :=
    (FiniteLaw.independentBits_probability_any_relative_deviation p hp S mu eta
      heta heta1 hmu).trans_lt hfailure
  have hprob : L.probability Bad < 1 := by exact_mod_cast htail
  have hgood : 0 < L.probability (fun ω ↦ ¬ Bad ω) := by
    rw [L.probability_not]
    exact tsub_pos_of_lt hprob
  obtain ⟨ω, hω⟩ := L.exists_of_probability_pos hgood
  refine ⟨A.filter (fun i ↦ ω i = true), filter_subset _ _, fun j ↦ ?_⟩
  have hcount : ((A.filter (fun i ↦ ω i = true)).filter (incident j)).card =
      ((S j).filter (fun i ↦ ω i = true)).card := by
    congr 1
    ext i
    simp only [S, mem_filter]
    tauto
  rw [hcount]
  exact le_of_not_gt (fun h ↦ hω ⟨j, h⟩)

end

end Erdos207
