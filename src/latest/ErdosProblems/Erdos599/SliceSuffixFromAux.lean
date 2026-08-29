/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.LadderSuccessorBridge

/-!
# Finite complementary suffixes

This file records the two exact geometric facts about `suffixFromAux` used
when a finite stage path is split at the endpoint of one of its prefixes.
The selected suffix is literally a subpath of its ambient path, and
concatenating it back onto the prefix reconstructs that path.
-/

noncomputable section

open Cardinal Set

namespace Erdos599
namespace CardinalInduction
namespace SliceCandidate

open DirectedPath

universe u

variable {V : Type u}

private theorem finitePath_eq_of_walk_support_eq_aux
    {D : Digraph V} (p q : FinitePath D)
    (hstart : p.start = q.start) (hfinish : p.finish = q.finish)
    (hsupport : p.walk.support = q.walk.support) : p = q := by
  rcases p with ⟨a, b, p, hp⟩
  rcases q with ⟨c, d, q, hq⟩
  dsimp only at hstart hfinish hsupport
  subst c
  subst d
  have hpq : p = q := DirectedPath.Walk.eq_of_support_eq p q hsupport
  subst q
  rfl

/-- The finite suffix selected at a support vertex is a subpath of its
ambient finite path. -/
theorem suffixFromAux_isSubpathOf_stage
    {D : Digraph V} (q : FinitePath D) (x : V) (hx : x ∈ q.support) :
    (q.suffixFromAux x hx).IsSubpathOf (.inl q) := by
  constructor
  · exact q.suffixFromAux_support_subset x hx
  · exact (q.suffixData x hx).walk.edgeSet_subset_of_support_suffix
      q.walk (q.suffixData_support_suffix x hx)

/-- Appending a finite prefix to the complementary `suffixFromAux`
reconstructs the original finite path literally. -/
theorem appendFinite_suffixFromAux_eq_of_prefix
    {D : Digraph V} {p q : FinitePath D} (hpq : p.IsPrefixOf q) :
    let hx : p.finish ∈ q.support :=
      hpq.support_subset p.finish_mem_support
    let s := q.suffixFromAux p.finish hx
    ∃ (hstart : s.start = p.finish)
      (hinter : p.support ∩ s.support ⊆ {p.finish}),
      p.support ∩ s.support = {p.finish} ∧
        p.appendFinite s hstart hinter = q := by
  let hx : p.finish ∈ q.support :=
    hpq.support_subset p.finish_mem_support
  let s := q.suffixFromAux p.finish hx
  have hpqStart : p.start = q.start := hpq.start_eq
  obtain ⟨tail, htail⟩ := hpq
  have hdesired : p.finish :: tail <:+ q.walk.support := by
    refine ⟨p.walk.support.dropLast, ?_⟩
    calc
      p.walk.support.dropLast ++ p.finish :: tail =
          (p.walk.support.dropLast ++ [p.finish]) ++ tail := by simp
      _ = p.walk.support ++ tail := by
        have hlast := List.dropLast_append_getLast p.walk.support_ne_nil
        simpa only [p.walk.getLast_support] using
          congrArg (fun l : List V ↦ l ++ tail) hlast
      _ = q.walk.support := htail
  have hselected : (q.suffixData p.finish hx).walk.support <:+
      q.walk.support := q.suffixData_support_suffix p.finish hx
  have hsuffix : (q.suffixData p.finish hx).walk.support =
      p.finish :: tail := by
    rcases List.suffix_total hselected hdesired with h | h
    · apply List.Nodup.eq_of_head_mem_of_suffix (hne := by simp) h
      · change p.finish ∈ (q.suffixData p.finish hx).walk.support
        exact (q.suffixData p.finish hx).walk.start_mem_support
      · exact hdesired.nodup q.isPath
    · symm
      apply List.Nodup.eq_of_head_mem_of_suffix
        (hne := (q.suffixData p.finish hx).walk.support_ne_nil) h
      · rw [(q.suffixData p.finish hx).walk.head_support]
        exact List.mem_cons_self
      · exact hselected.nodup q.isPath
  have hnodup : (p.walk.support ++ tail).Nodup := by
    rw [htail]
    exact q.isPath
  have hdis := (List.nodup_append.mp hnodup).2.2
  have hinterEq : p.support ∩ s.support = {p.finish} := by
    ext y
    constructor
    · rintro ⟨hyp, hys⟩
      change y ∈ p.walk.support at hyp
      change y ∈ (q.suffixData p.finish hx).walk.support at hys
      rw [hsuffix] at hys
      rcases List.mem_cons.mp hys with rfl | hytail
      · exact Set.mem_singleton p.finish
      · exact (hdis y hyp y hytail rfl).elim
    · intro hy
      have hyfinish : y = p.finish := Set.mem_singleton_iff.mp hy
      subst y
      exact ⟨p.finish_mem_support,
        (q.suffixData p.finish hx).walk.start_mem_support⟩
  let hstart : s.start = p.finish := q.suffixFromAux_start p.finish hx
  let hinter : p.support ∩ s.support ⊆ {p.finish} := hinterEq.subset
  refine ⟨hstart, hinter, hinterEq, ?_⟩
  apply finitePath_eq_of_walk_support_eq_aux
  · exact (p.appendFinite_start s hstart hinter).trans hpqStart
  · exact p.appendFinite_finish s hstart hinter
  · rw [p.appendFinite_walk_support s hstart hinter]
    change p.walk.support ++
        (q.suffixData p.finish hx).walk.support.tail = q.walk.support
    rw [hsuffix]
    simpa only [List.tail_cons] using htail

end SliceCandidate
end CardinalInduction
end Erdos599
