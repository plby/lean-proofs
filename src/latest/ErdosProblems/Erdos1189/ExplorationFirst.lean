/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Selecting the first occurrence of each coordinate in the depth-first exploration.
Informal source: BBMST Definition 4.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationPaths

namespace Erdos1189.Grid

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ} {A : Finset α} {I : Finset ι}

def ExplorationTree.firstIndex (tree : ExplorationTree H lam ε δ A I) (j : ι) : ℕ :=
  tree.entries.findIdx (fun e => decide (e.label = j))

lemma ExplorationTree.firstIndex_lt (tree : ExplorationTree H lam ε δ A I) {j : ι}
    (hj : j ∈ I) : tree.firstIndex j < tree.entries.length := by
  obtain ⟨e, he, hej⟩ := (tree.exists_entry_label_iff j).mpr hj
  exact List.findIdx_lt_length_of_exists ⟨e, he, by simpa only [decide_eq_true_eq] using hej⟩

def ExplorationTree.firstEntry (tree : ExplorationTree H lam ε δ A I) (j : I) :
    ExplorationEntry H lam ε δ :=
  tree.entries.get ⟨tree.firstIndex j, tree.firstIndex_lt j.property⟩

lemma ExplorationTree.firstEntry_mem (tree : ExplorationTree H lam ε δ A I) (j : I) :
    tree.firstEntry j ∈ tree.entries := List.get_mem _ _

lemma ExplorationTree.firstEntry_label (tree : ExplorationTree H lam ε δ A I) (j : I) :
    (tree.firstEntry j).label = j := by
  have h := List.findIdx_getElem (xs := tree.entries)
    (p := fun e : ExplorationEntry H lam ε δ => decide (e.label = j.val))
    (w := tree.firstIndex_lt j.property)
  exact of_decide_eq_true h

lemma ExplorationTree.firstIndex_injective (tree : ExplorationTree H lam ε δ A I) :
    Function.Injective (fun j : I => tree.firstIndex j) := by
  intro i j hij
  have hfin : (⟨tree.firstIndex i, tree.firstIndex_lt i.property⟩ : Fin tree.entries.length) =
      ⟨tree.firstIndex j, tree.firstIndex_lt j.property⟩ := Fin.ext hij
  have hentry : tree.firstEntry i = tree.firstEntry j := congrArg tree.entries.get hfin
  apply Subtype.ext
  have hlabel := congrArg ExplorationEntry.label hentry
  simpa only [tree.firstEntry_label] using hlabel

lemma ExplorationTree.label_ne_before_first (tree : ExplorationTree H lam ε δ A I) (j : ι)
    {e : ExplorationEntry H lam ε δ} (he : e ∈ tree.entries.take (tree.firstIndex j)) :
    e.label ≠ j := by
  have h : decide (e.label = j) = false := List.false_of_mem_take_findIdx
    (p := fun d : ExplorationEntry H lam ε δ => decide (d.label = j)) he
  exact of_decide_eq_false h

end Erdos1189.Grid
