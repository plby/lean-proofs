/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Nesting of the first exploration entries sharing a fixed coordinate.
Informal source: BBMST Lemma 4.7.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationBlocks

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ} {A : Finset α} {I : Finset ι}

lemma ExplorationTree.firstIndex_lt_of_prefix_label
    (tree : ExplorationTree H lam ε δ A I)
    {pre : List (ExplorationEntry H lam ε δ)} (hpre : pre <+: tree.entries)
    {e : ExplorationEntry H lam ε δ} (he : e ∈ pre) {j : ι} (hj : e.label = j) :
    tree.firstIndex j < pre.length := by
  have hfind : pre.findIdx (fun d => decide (d.label = j)) < pre.length :=
    List.findIdx_lt_length_of_exists ⟨e, he, by simpa only [decide_eq_true_eq] using hj⟩
  change tree.entries.findIdx (fun d => decide (d.label = j)) < pre.length
  rw [hpre.findIdx_eq_of_findIdx_lt_length hfind]
  exact hfind

lemma ExplorationTree.firstEntry_mem_prefix (tree : ExplorationTree H lam ε δ A I) (j : I)
    {pre : List (ExplorationEntry H lam ε δ)} (hpre : pre <+: tree.entries)
    (hj : ∃ e ∈ pre, e.label = j) : tree.firstEntry j ∈ pre := by
  obtain ⟨e, he, hej⟩ := hj
  have hn := tree.firstIndex_lt_of_prefix_label hpre he hej
  obtain ⟨post, hsplit⟩ := hpre
  change tree.entries[tree.firstIndex j]'(tree.firstIndex_lt j.property) ∈ pre
  simpa only [← hsplit, List.getElem_append_left hn] using List.getElem_mem hn

lemma ExplorationTree.firstEntry_mem_subtree (tree : ExplorationTree H lam ε δ A I)
    (i j : I) (hij : tree.firstIndex i < tree.firstIndex j)
    {pre inside post : List (ExplorationEntry H lam ε δ)}
    (hsplit : tree.entries = pre ++ tree.firstEntry i :: inside ++ post)
    (hj : ∃ e ∈ tree.firstEntry i :: inside, e.label = j) :
    tree.firstEntry j ∈ inside := by
  have hp : pre.length = tree.firstIndex i :=
    tree.firstEntry_split_length i pre (inside ++ post) (by simpa using hsplit)
  have hprefix : pre ++ tree.firstEntry i :: inside <+: tree.entries := ⟨post, hsplit.symm⟩
  obtain ⟨e, he, hej⟩ := hj
  have hm := tree.firstEntry_mem_prefix j hprefix ⟨e, List.mem_append_right _ he, hej⟩
  rcases List.mem_append.mp hm with hm | hm
  · have hpre : pre <+: tree.entries :=
      ⟨tree.firstEntry i :: inside ++ post, by simpa only [List.append_assoc] using hsplit.symm⟩
    have hlt := tree.firstIndex_lt_of_prefix_label hpre hm (tree.firstEntry_label j)
    omega
  · rcases List.mem_cons.mp hm with heq | hm
    · have hji : j.val = i.val := by
        simpa only [tree.firstEntry_label] using congrArg ExplorationEntry.label heq
      have := congrArg tree.firstIndex hji
      omega
    · exact hm

lemma ExplorationTree.firstEntry_active_subset (tree : ExplorationTree H lam ε δ A I)
    (i j : I) (hij : tree.firstIndex i < tree.firstIndex j)
    (hj : j.val ∈ familyFixed H (tree.firstEntry i).family) :
    (tree.firstEntry j).active ⊆ (tree.firstEntry i).active.erase i.val := by
  have horiginal := tree.entry_original_fixed_subset _ (tree.firstEntry_mem i) hj
  have hactive : j.val ∈ (tree.firstEntry i).active := by
    rcases mem_union.mp horiginal with houtside | hinside
    · exact False.elim ((mem_sdiff.mp houtside).2 j.property)
    · rcases mem_union.mp hinside with hpath | hact
      · have := tree.path_firstIndex_lt i hpath
        omega
      · exact hact
  obtain ⟨pre, inside, post, hsplit, hsub, hlabels⟩ :=
    tree.entry_subtree_block _ (tree.firstEntry_mem i)
  have hmem := tree.firstEntry_mem_subtree i j hij hsplit (hlabels j hactive)
  simpa only [tree.firstEntry_label] using hsub _ hmem

lemma ExplorationTree.shared_fixed_card_lt (tree : ExplorationTree H lam ε δ A I)
    (i j : I) (hij : tree.firstIndex i < tree.firstIndex j) {a : α}
    (ha : a ∈ (tree.firstEntry i).family)
    (hi : i.val ∈ fixed (project (tree.firstEntry i).active (H a)))
    (hj : j.val ∈ fixed (H a)) :
    (fixed (project (tree.firstEntry j).active (H a))).card <
      (fixed (project (tree.firstEntry i).active (H a))).card := by
  have hsub := tree.firstEntry_active_subset i j hij (Grid.mem_familyFixed.mpr ⟨a, ha, hj⟩)
  have hfixed : fixed (project (tree.firstEntry j).active (H a)) ⊆
      (fixed (project (tree.firstEntry i).active (H a))).erase i.val := by
    intro t ht
    rw [fixed_project] at ht
    obtain ⟨htH, htJ⟩ := mem_inter.mp ht
    obtain ⟨hti, htI⟩ := mem_erase.mp (hsub htJ)
    exact mem_erase.mpr ⟨hti, by rw [fixed_project]; exact mem_inter.mpr ⟨htH, htI⟩⟩
  exact (card_le_card hfixed).trans_lt (card_erase_lt_of_mem hi)

end Erdos1189.Grid
