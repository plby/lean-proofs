/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Contiguous subtree blocks in the depth-first exploration.
Informal source: BBMST Observation 4.3 and Lemma 4.7.
Formal author: OpenAI Codex.
-/

import ErdosProblems.Erdos1189.ExplorationOrder

namespace Erdos1189.Grid

open Finset

variable {ι α : Type*} {q : ι → ℕ} [Fintype ι] [DecidableEq ι]
variable {H : α → Box q} {lam ε δ : ℝ}

lemma ExplorationEntry.prepend_injective (edge : (i : ι) × Fin (q i)) :
    Function.Injective (ExplorationEntry.prepend (H := H) (lam := lam) (ε := ε) (δ := δ) edge) := by
  intro e d h
  exact congrArg (fun x : ExplorationEntry H lam ε δ => { x with path := x.path.tail }) h

lemma ExplorationTree.entries_nodup {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) : tree.entries.Nodup := by
  induction tree with
  | leaf A => exact List.nodup_nil
  | node step children ih =>
    apply List.nodup_cons.mpr
    constructor
    · intro h
      obtain ⟨s, _, hs⟩ := List.mem_flatMap.mp h
      obtain ⟨d, _, hd⟩ := List.mem_map.mp hs
      have hp := congrArg ExplorationEntry.path hd
      exact List.cons_ne_nil _ _ hp
    · apply List.nodup_flatMap.mpr
      refine ⟨fun s _ => (ih s).map (ExplorationEntry.prepend_injective _), ?_⟩
      apply (List.nodup_finRange (q step.coordinate)).imp
      intro s t hst d hds hdt
      obtain ⟨e, _, he⟩ := List.mem_map.mp hds
      obtain ⟨f, _, hf⟩ := List.mem_map.mp hdt
      have hp := congrArg ExplorationEntry.path (he.trans hf.symm)
      have hedge := (List.cons.inj hp).1
      apply hst
      simpa using hedge

lemma ExplorationTree.entry_subtree_block {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) :
    ∀ e ∈ tree.entries, ∃ pre inside post : List (ExplorationEntry H lam ε δ),
      tree.entries = pre ++ e :: inside ++ post ∧
      (∀ d ∈ inside, d.active ⊆ e.active.erase e.label) ∧
      (∀ j ∈ e.active, ∃ d ∈ e :: inside, d.label = j) := by
  induction tree with
  | leaf A => simp [entries]
  | node step children ih =>
    intro e he
    let f := fun s => ((children s).entries).map
      (ExplorationEntry.prepend ⟨step.coordinate, s⟩)
    rcases (mem_entries_node step children e).mp he with rfl | ⟨s, d, hd, rfl⟩
    · refine ⟨[], (List.finRange (q step.coordinate)).flatMap f, [], by simp [entries, f],
        ?_, ?_⟩
      · intro d hd
        obtain ⟨s, _, hs⟩ := List.mem_flatMap.mp hd
        obtain ⟨d', hd', rfl⟩ := List.mem_map.mp hs
        exact ((children s).entry_active_subset d' hd').trans (step.active_subset s)
      · intro j hj
        exact (ExplorationTree.node step children).exists_entry_label_iff j |>.mpr hj
    · obtain ⟨pre, inside, post, hsplit, hactive, hlabels⟩ := ih s d hd
      obtain ⟨before, after, houter⟩ := List.mem_iff_append.mp (List.mem_finRange s)
      let lift : ExplorationEntry H lam ε δ → ExplorationEntry H lam ε δ :=
        ExplorationEntry.prepend ⟨step.coordinate, s⟩
      refine ⟨step.entry :: before.flatMap f ++ pre.map lift, inside.map lift,
        post.map lift ++ after.flatMap f, ?_, ?_, ?_⟩
      · simp only [entries, houter, List.flatMap_append, List.flatMap_cons, f, hsplit,
          List.map_append, List.map_cons, List.cons_append, List.append_assoc, lift]
      · intro d' hd'
        obtain ⟨d'', hd'', rfl⟩ := List.mem_map.mp hd'
        exact hactive d'' hd''
      · intro j hj
        obtain ⟨d', hd', hd'j⟩ := hlabels j hj
        refine ⟨lift d', ?_, hd'j⟩
        simpa only [List.map_cons] using List.mem_map_of_mem (f := lift) hd'

lemma ExplorationTree.firstEntry_split_length {A : Finset α} {I : Finset ι}
    (tree : ExplorationTree H lam ε δ A I) (i : I)
    (pre post : List (ExplorationEntry H lam ε δ))
    (hsplit : tree.entries = pre ++ tree.firstEntry i :: post) :
    pre.length = tree.firstIndex i := by
  have hp : pre.length < tree.entries.length := by simp [hsplit]
  apply tree.entries_nodup.getElem_inj_iff.mp
    (show tree.entries[pre.length] = tree.entries[tree.firstIndex i]'(tree.firstIndex_lt i.property)
      from ?_)
  change tree.entries[pre.length] = tree.firstEntry i
  simp [hsplit]

end Erdos1189.Grid
