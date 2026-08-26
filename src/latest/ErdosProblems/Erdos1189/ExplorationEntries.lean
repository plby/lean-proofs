/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Depth-first entries of an exploration tree and coverage of the active labels.
Informal source: BBMST Observation 4.3 and Definition 4.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationTree

namespace Erdos1189.Grid

universe u v

variable {ι : Type u} {α : Type v} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ}

structure ExplorationEntry (H : α → Box q) (lam ε δ : ℝ) where
  family : Finset α
  active : Finset ι
  step : ExplorationStep H family active lam ε δ
  path : List ((i : ι) × Fin (q i))

def ExplorationEntry.label (e : ExplorationEntry H lam ε δ) : ι := e.step.coordinate

def ExplorationEntry.prepend (edge : (i : ι) × Fin (q i)) (e : ExplorationEntry H lam ε δ) :
    ExplorationEntry H lam ε δ := { e with path := edge :: e.path }

def ExplorationStep.entry {A : Finset α} {I : Finset ι} (step : ExplorationStep H A I lam ε δ) :
    ExplorationEntry H lam ε δ := ⟨A, I, step, []⟩

def ExplorationTree.entries {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) : List (ExplorationEntry H lam ε δ) :=
  match tree with
  | .leaf _ => []
  | .node step children => step.entry :: (List.finRange (q step.coordinate)).flatMap fun s =>
      (entries (children s)).map (ExplorationEntry.prepend ⟨step.coordinate, s⟩)
termination_by structural tree

lemma mem_entries_node {A : Finset α} {I : Finset ι} (step : ExplorationStep H A I lam ε δ)
    (children : (s : Fin (q step.coordinate)) →
      ExplorationTree H lam ε δ (step.slices s) (step.active s))
    (e : ExplorationEntry H lam ε δ) :
    e ∈ (ExplorationTree.node step children).entries ↔
      e = step.entry ∨ ∃ s d, d ∈ (children s).entries ∧
        ExplorationEntry.prepend ⟨step.coordinate, s⟩ d = e := by
  simp only [ExplorationTree.entries, List.mem_cons, List.mem_flatMap, List.mem_finRange,
    true_and, List.mem_map]

lemma ExplorationTree.entry_family_subset {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, e.family ⊆ A := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · exact Finset.Subset.rfl
    · exact (ih s d hd).trans (step.slice_subset s)

lemma ExplorationTree.entry_active_subset {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, e.active ⊆ I := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · exact Finset.Subset.rfl
    · exact (ih s d hd).trans ((step.active_subset s).trans (Finset.erase_subset _ _))

lemma ExplorationTree.exists_entry_label_iff {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) (j : ι) :
    (∃ e ∈ tree.entries, e.label = j) ↔ j ∈ I := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    constructor
    · rintro ⟨e, he, hej⟩
      rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
      · exact hej ▸ step.coordinate_mem
      · have hchild : j ∈ step.active s := (ih s).mp ⟨d, hd, hej⟩
        exact Finset.mem_of_mem_erase (step.active_subset s hchild)
    · intro hj
      by_cases hji : j = step.coordinate
      · exact ⟨step.entry, (mem_entries_node step children _).mpr (Or.inl rfl), hji.symm⟩
      · have hmem : j ∈ Finset.univ.biUnion step.active := by
          rw [step.active_union]
          exact Finset.mem_erase.mpr ⟨hji, hj⟩
        obtain ⟨s, _, hjs⟩ := Finset.mem_biUnion.mp hmem
        obtain ⟨d, hd, hdj⟩ := (ih s).mpr hjs
        exact ⟨ExplorationEntry.prepend ⟨step.coordinate, s⟩ d,
          (mem_entries_node step children _).mpr (Or.inr ⟨s, d, hd, rfl⟩), hdj⟩

end Erdos1189.Grid
