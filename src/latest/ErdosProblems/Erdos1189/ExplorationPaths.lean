/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Path information retained by the depth-first exploration entries.
Informal source: the ancestor constraints of BBMST Definition 3.2(a).
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationEntries

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ}

def ExplorationEntry.pathLabels (e : ExplorationEntry H lam ε δ) : Finset ι :=
  (e.path.map Sigma.fst).toFinset

lemma ExplorationEntry.pathLabels_prepend (edge : (i : ι) × Fin (q i))
    (e : ExplorationEntry H lam ε δ) :
    (e.prepend edge).pathLabels = insert edge.1 e.pathLabels := by
  simp [pathLabels, prepend]

lemma ExplorationTree.entry_path_subset {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) : ∀ e ∈ tree.entries, e.pathLabels ⊆ I := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · simp [ExplorationStep.entry, ExplorationEntry.pathLabels]
    · rw [ExplorationEntry.pathLabels_prepend]
      exact insert_subset step.coordinate_mem
        ((ih s d hd).trans ((step.active_subset s).trans (erase_subset _ _)))

lemma ExplorationTree.entry_path_disjoint {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, Disjoint e.pathLabels e.active := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · simp [ExplorationStep.entry, ExplorationEntry.pathLabels]
    · rw [ExplorationEntry.pathLabels_prepend]
      apply disjoint_left.mpr
      intro j hj hjActive
      rcases mem_insert.mp hj with rfl | hj
      · have hmem := step.active_subset s ((children s).entry_active_subset d hd hjActive)
        exact (mem_erase.mp hmem).1 rfl
      · exact disjoint_left.mp (ih s d hd) hj hjActive

lemma ExplorationTree.entry_path_compatible {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, ∀ a ∈ e.family, ∀ edge ∈ e.path, Compatible (H a) edge.1 edge.2 := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he a ha edge hedge
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · simp [ExplorationStep.entry] at hedge
    · rcases List.mem_cons.mp hedge with rfl | hedge
      · exact step.compatible s a ((children s).entry_family_subset d hd ha)
      · exact ih s d hd a ha edge hedge

lemma ExplorationTree.entry_original_fixed_subset {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, familyFixed H e.family ⊆
      (familyFixed H A \ I) ∪ (e.pathLabels ∪ e.active) := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · intro j hj
      change j ∈ (familyFixed H step.entry.family \ step.entry.active) ∪
        (∅ ∪ step.entry.active)
      by_cases hjI : j ∈ step.entry.active
      · exact mem_union_right _ (mem_union_right _ hjI)
      · exact mem_union_left _ (mem_sdiff.mpr ⟨hj, hjI⟩)
    · intro j hj
      have hchild := ih s d hd hj
      rw [ExplorationEntry.pathLabels_prepend]
      rcases mem_union.mp hchild with hleft | hright
      · obtain ⟨hjSlice, hjNot⟩ := mem_sdiff.mp hleft
        rcases mem_union.mp (step.original_fixed_subset s hjSlice) with hjOld | hjRest
        · exact mem_union_left _ hjOld
        · rcases mem_insert.mp hjRest with hjEq | hjActive
          · exact mem_union_right _ (mem_union_left _ (mem_insert.mpr (Or.inl hjEq)))
          · exact False.elim (hjNot hjActive)
      · exact mem_union_right _ (by
          rcases mem_union.mp hright with hjPath | hjActive
          · exact mem_union_left _ (mem_insert_of_mem hjPath)
          · exact mem_union_right _ hjActive)

end Erdos1189.Grid
