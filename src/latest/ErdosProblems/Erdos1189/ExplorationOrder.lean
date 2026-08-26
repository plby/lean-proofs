/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Ancestor labels occur before their descendants in the exploration order.
Informal source: BBMST Definition 4.1(d), verified after Definition 4.4.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationFirst

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ}

def PathsSeen (seen : Finset ι) : List (ExplorationEntry H lam ε δ) → Prop
  | [] => True
  | e :: es => e.pathLabels ⊆ seen ∧ PathsSeen (insert e.label seen) es

lemma PathsSeen.mono {seen seen' : Finset ι} {es : List (ExplorationEntry H lam ε δ)}
    (h : PathsSeen seen es) (hsub : seen ⊆ seen') : PathsSeen seen' es := by
  induction es generalizing seen seen' with
  | nil => trivial
  | cons e es ih => exact ⟨h.1.trans hsub, ih h.2 (insert_subset_insert _ hsub)⟩

lemma PathsSeen.append {seen : Finset ι} {xs ys : List (ExplorationEntry H lam ε δ)}
    (hx : PathsSeen seen xs) (hy : PathsSeen seen ys) : PathsSeen seen (xs ++ ys) := by
  induction xs generalizing seen with
  | nil => exact hy
  | cons e xs ih =>
    exact ⟨hx.1, ih hx.2 (hy.mono (subset_insert _ _))⟩

lemma PathsSeen.flatMap {σ : Type*} {seen : Finset ι} (xs : List σ)
    (f : σ → List (ExplorationEntry H lam ε δ)) (h : ∀ s ∈ xs, PathsSeen seen (f s)) :
    PathsSeen seen (xs.flatMap f) := by
  induction xs with
  | nil => trivial
  | cons s xs ih =>
    exact (h s (List.mem_cons_self)).append (ih (fun t ht => h t (List.mem_cons_of_mem _ ht)))

lemma PathsSeen.map_prepend {seen : Finset ι} {es : List (ExplorationEntry H lam ε δ)}
    (h : PathsSeen seen es) (edge : (i : ι) × Fin (q i)) (he : edge.1 ∈ seen) :
    PathsSeen seen (es.map (ExplorationEntry.prepend edge)) := by
  induction es generalizing seen with
  | nil => trivial
  | cons e es ih =>
    refine ⟨?_, ih h.2 (mem_insert_of_mem he)⟩
    rw [ExplorationEntry.pathLabels_prepend]
    exact insert_subset he h.1

lemma ExplorationTree.pathsSeen {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) : PathsSeen ∅ tree.entries := by
  induction tree with
  | leaf A => trivial
  | node step children ih =>
    refine ⟨by simp [ExplorationStep.entry, ExplorationEntry.pathLabels], ?_⟩
    apply PathsSeen.flatMap
    intro s _
    exact ((ih s).mono (empty_subset _)).map_prepend ⟨step.coordinate, s⟩ (mem_insert_self _ _)

lemma PathsSeen.path_subset_prefix {seen : Finset ι}
    (pre post : List (ExplorationEntry H lam ε δ)) (e : ExplorationEntry H lam ε δ)
    (h : PathsSeen seen (pre ++ e :: post)) :
    e.pathLabels ⊆ seen ∪ (pre.map ExplorationEntry.label).toFinset := by
  induction pre generalizing seen with
  | nil => simpa only [List.map_nil, List.toFinset_nil, union_empty] using h.1
  | cons d pre ih =>
    have hs := ih h.2
    convert hs using 1
    ext i
    simp only [mem_union, mem_insert, List.map_cons, List.toFinset_cons]
    tauto

lemma ExplorationTree.path_firstIndex_lt {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) (i : I) {j : ι}
    (hj : j ∈ (tree.firstEntry i).pathLabels) : tree.firstIndex j < tree.firstIndex i := by
  let n := tree.firstIndex i
  have hn : n < tree.entries.length := tree.firstIndex_lt i.property
  have hsplit : tree.entries.take n ++ tree.firstEntry i :: tree.entries.drop (n + 1) =
      tree.entries := by
    have h := List.take_append_drop n tree.entries
    rw [List.drop_eq_getElem_cons hn] at h
    exact h
  have hseen : PathsSeen ∅ (tree.entries.take n ++ tree.firstEntry i ::
      tree.entries.drop (n + 1)) := hsplit.symm ▸ tree.pathsSeen
  have hpath := hseen.path_subset_prefix (tree.entries.take n) (tree.entries.drop (n + 1))
    (tree.firstEntry i) hj
  rw [empty_union] at hpath
  obtain ⟨d, hd, hdj⟩ := List.mem_map.mp (List.mem_toFinset.mp hpath)
  have hfind : (tree.entries.take n).findIdx (fun d => decide (d.label = j)) <
      (tree.entries.take n).length := List.findIdx_lt_length_of_exists
        ⟨d, hd, by simpa only [decide_eq_true_eq] using hdj⟩
  have heq := (List.take_prefix n tree.entries).findIdx_eq_of_findIdx_lt_length hfind
  change tree.entries.findIdx (fun d => decide (d.label = j)) < n
  rw [heq]
  exact hfind.trans_le (by simp only [List.length_take]; exact min_le_left _ _)

end Erdos1189.Grid
