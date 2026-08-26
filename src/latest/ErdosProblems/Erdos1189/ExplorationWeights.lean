/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
A uniform bound on the total charge of one box along selected exploration nodes.
Informal source: BBMST Lemmas 4.7--4.8; the rational weights give constant six.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationNesting
import Mathlib.Analysis.SpecificLimits.Basic

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ} {A : Finset α} {I : Finset ι}

lemma ExplorationTree.selected_rank_injOn (tree : ExplorationTree H lam ε δ A I)
    (S : Finset I) (a : α)
    (hS : ∀ i ∈ S, a ∈ (tree.firstEntry i).family ∧
      i.val ∈ fixed (project (tree.firstEntry i).active (H a))) :
    Set.InjOn (fun i : I => (fixed (project (tree.firstEntry i).active (H a))).card) S := by
  intro i hi j hj heq
  change (fixed (project (tree.firstEntry i).active (H a))).card =
    (fixed (project (tree.firstEntry j).active (H a))).card at heq
  rcases lt_trichotomy (tree.firstIndex i) (tree.firstIndex j) with hlt | he | hgt
  · have hjH : j.val ∈ fixed (H a) := by
      have h := (hS j hj).2
      rw [fixed_project] at h
      exact (mem_inter.mp h).1
    have hlt' := tree.shared_fixed_card_lt i j hlt (hS i hi).1 (hS i hi).2 hjH
    omega
  · exact tree.firstIndex_injective he
  · have hiH : i.val ∈ fixed (H a) := by
      have h := (hS i hi).2
      rw [fixed_project] at h
      exact (mem_inter.mp h).1
    have hlt' := tree.shared_fixed_card_lt j i hgt (hS j hj).1 (hS j hj).2 hiH
    omega

lemma ExplorationTree.selected_box_weight_le_six (tree : ExplorationTree H lam ε δ A I)
    (S : Finset I) (a : α)
    (hS : ∀ i ∈ S, a ∈ (tree.firstEntry i).family ∧
      i.val ∈ fixed (project (tree.firstEntry i).active (H a))) :
    ∑ i ∈ S, (5 / 6 : ℝ) ^ (fixed (project (tree.firstEntry i).active (H a))).card ≤ 6 := by
  classical
  let rank := fun i : I => (fixed (project (tree.firstEntry i).active (H a))).card
  have hinj := tree.selected_rank_injOn S a hS
  have hsummable : Summable (fun n : ℕ => (5 / 6 : ℝ) ^ n) :=
    summable_geometric_of_lt_one (by norm_num) (by norm_num)
  calc
    _ = ∑ n ∈ S.image rank, (5 / 6 : ℝ) ^ n := (sum_image hinj).symm
    _ ≤ ∑' n : ℕ, (5 / 6 : ℝ) ^ n := hsummable.sum_le_tsum _ (fun _ _ => by positivity)
    _ = 6 := by rw [tsum_geometric_of_lt_one (by norm_num) (by norm_num)]; norm_num

lemma ExplorationTree.bad_coordinate_sum_le (tree : ExplorationTree H lam ε δ A I)
    (B : Finset I) (G : I → Finset α) (hlam : 0 < lam)
    (hG : ∀ i ∈ B, G i ⊆ (tree.firstEntry i).family)
    (hfixed : ∀ i ∈ B, ∀ a ∈ G i,
      i.val ∈ fixed (project (tree.firstEntry i).active (H a)))
    (hweight : ∀ i ∈ B, (q i : ℝ) / lam ≤
      ∑ a ∈ G i, (5 / 6 : ℝ) ^ (fixed (project (tree.firstEntry i).active (H a))).card) :
    ∑ i ∈ B, (q i : ℝ) ≤ 6 * lam * A.card := by
  classical
  let w := fun (i : I) a => (5 / 6 : ℝ) ^
    (fixed (project (tree.firstEntry i).active (H a))).card
  have hGA : ∀ i ∈ B, G i ⊆ A := fun i hi =>
    (hG i hi).trans (tree.entry_family_subset _ (tree.firstEntry_mem i))
  have hsum : (∑ i ∈ B, (q i : ℝ)) / lam ≤ 6 * A.card := by
    calc
      _ = ∑ i ∈ B, (q i : ℝ) / lam := sum_div _ _ _
      _ ≤ ∑ i ∈ B, ∑ a ∈ G i, w i a := sum_le_sum hweight
      _ = ∑ i ∈ B, ∑ a ∈ A, if a ∈ G i then w i a else 0 := by
        apply sum_congr rfl
        intro i hi
        have hf : A.filter (fun a => a ∈ G i) = G i := by
          ext a
          simp only [mem_filter]
          exact and_iff_right_of_imp (fun ha => hGA i hi ha)
        rw [← sum_filter, hf]
      _ = ∑ a ∈ A, ∑ i ∈ B, if a ∈ G i then w i a else 0 := sum_comm
      _ ≤ ∑ _a ∈ A, (6 : ℝ) := by
        apply sum_le_sum
        intro a _
        rw [← sum_filter]
        apply tree.selected_box_weight_le_six
        intro i hi
        obtain ⟨hiB, ha⟩ := mem_filter.mp hi
        exact ⟨hG i hiB ha, hfixed i hiB a ha⟩
      _ = 6 * A.card := by simp [mul_comm]
  have h := (div_le_iff₀ hlam).mp hsum
  nlinarith

end Erdos1189.Grid
