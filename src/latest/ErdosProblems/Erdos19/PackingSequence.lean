import ErdosProblems.Erdos19.GraphDegreeAccounting
import Mathlib.Data.Fin.Tuple.Basic

/-! # Finite sequences of disjoint prescribed matchings -/

namespace Erdos19

open Finset
open _root_.SimpleGraph

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V]

inductive IsMatchingPacking (G : _root_.SimpleGraph V) (A : ℕ → Set V) :
    ℕ → _root_.SimpleGraph V → Prop
  | nil : IsMatchingPacking G A 0 ⊥
  | snoc {i : ℕ} {U : _root_.SimpleGraph V} (previous : IsMatchingPacking G A i U)
      (M : G.Subgraph) (matching : M.IsMatching) (covers : M.verts = A i)
      (disjoint : Disjoint U M.spanningCoe) :
      IsMatchingPacking G A (i + 1) (U ⊔ M.spanningCoe)

namespace IsMatchingPacking

variable {G U : _root_.SimpleGraph V} {A : ℕ → Set V} {i : ℕ}

theorem used_le (h : IsMatchingPacking G A i U) : U ≤ G := by
  induction h with
  | nil => exact bot_le
  | snoc _ M _ _ _ ih =>
    exact sup_le ih (fun _ _ hadj ↦ (show M.Adj _ _ from hadj).adj_sub)

theorem degree_add_absences (h : IsMatchingPacking G A i U) (v : V) :
    (U.neighborSet v).ncard + ∑ j ∈ range i, (if v ∈ A j then 0 else 1) = i := by
  classical
  induction h with
  | nil => simp
  | @snoc i U previous M matching covers disjoint ih =>
    rw [neighbor_ncard_sup_of_disjoint U M.spanningCoe disjoint,
      matching_neighbor_ncard G M matching, covers, sum_range_succ]
    split_ifs <;> omega

theorem degree_bounds (h : IsMatchingPacking G A i U) (m a : ℕ) (him : i ≤ m)
    (habs : ∀ v, ∑ j ∈ range m, (if v ∈ A j then 0 else 1) ≤ a) :
    (∀ v, i ≤ (U.neighborSet v).ncard + a) ∧
    (∀ v, (U.neighborSet v).ncard ≤ i) := by
  classical
  have hbound : ∀ v, ∑ j ∈ range i, (if v ∈ A j then 0 else 1) ≤ a := by
    intro v
    exact (sum_le_sum_of_subset (range_mono him)).trans (habs v)
  constructor
  · intro v
    have heq := h.degree_add_absences v
    have hb := hbound v
    omega
  · intro v
    have heq := h.degree_add_absences v
    omega

theorem exists_family_exact (h : IsMatchingPacking G A i U) :
    ∃ M : Fin i → G.Subgraph,
      (∀ j, (M j).IsMatching ∧ (M j).verts = A j ∧ (M j).spanningCoe ≤ U) ∧
      Pairwise (fun j k ↦ Disjoint (M j).spanningCoe (M k).spanningCoe) ∧
      (⨆ j, (M j).spanningCoe) = U := by
  induction h with
  | nil =>
    exact ⟨Fin.elim0, fun j ↦ j.elim0, (fun j ↦ j.elim0), by simp⟩
  | @snoc i U previous N hN hNA hUN ih =>
    obtain ⟨M, hM, hpair, hunion⟩ := ih
    refine ⟨Fin.snoc M N, ?_, ?_, ?_⟩
    · intro j
      induction j using Fin.lastCases with
      | last => simpa only [Fin.snoc_last, Fin.val_last] using ⟨hN, hNA, le_sup_right (a := U)⟩
      | cast j =>
        simpa only [Fin.snoc_castSucc, Fin.val_castSucc] using
          ⟨(hM j).1, (hM j).2.1, (hM j).2.2.trans le_sup_left⟩
    · intro j k hne
      induction j using Fin.lastCases with
      | last =>
        induction k using Fin.lastCases with
        | last => exact (hne rfl).elim
        | cast k =>
          simpa only [Fin.snoc_last, Fin.snoc_castSucc] using
            (hUN.mono_left (hM k).2.2).symm
      | cast j =>
        induction k using Fin.lastCases with
        | last =>
          simpa only [Fin.snoc_last, Fin.snoc_castSucc] using hUN.mono_left (hM j).2.2
        | cast k =>
          simpa only [Fin.snoc_castSucc] using hpair (fun heq ↦ hne (congrArg Fin.castSucc heq))
    · apply le_antisymm
      · apply iSup_le
        intro j
        induction j using Fin.lastCases with
        | last => simpa only [Fin.snoc_last] using (le_sup_right (a := U) (b := N.spanningCoe))
        | cast j =>
          simpa only [Fin.snoc_castSucc] using (hM j).2.2.trans (le_sup_left (b := N.spanningCoe))
      · apply sup_le
        · rw [← hunion]
          apply iSup_le
          intro j
          exact (by simpa only [Fin.snoc_castSucc] using
            (le_iSup (fun k ↦ ((Fin.snoc M N : Fin (i + 1) → G.Subgraph) k).spanningCoe) j.castSucc))
        · exact (by simpa only [Fin.snoc_last] using
            (le_iSup (fun k ↦ ((Fin.snoc M N : Fin (i + 1) → G.Subgraph) k).spanningCoe) (Fin.last i)))

theorem exists_family (h : IsMatchingPacking G A i U) :
    ∃ M : Fin i → G.Subgraph,
      (∀ j, (M j).IsMatching ∧ (M j).verts = A j ∧ (M j).spanningCoe ≤ U) ∧
      Pairwise (fun j k ↦ Disjoint (M j).spanningCoe (M k).spanningCoe) := by
  obtain ⟨M, hM, hp, _⟩ := h.exists_family_exact
  exact ⟨M, hM, hp⟩

end IsMatchingPacking

#print axioms IsMatchingPacking.exists_family

end Erdos19
