/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.FiniteColouredOccurrenceSwitch
import ErdosProblems.Erdos599.GroundingFinitePerturbationRooting

/-!
# Rooting sinks of a finite coloured occurrence transaction

An interval-safe occurrence word already contains the exact signed boundary
accounting of a finite owner-cluster transaction.  The reference warp may
contain rays: finite inserted edges preserve the absence of reverse rays,
and cycle deletion therefore realizes every nonisolated sink as a path from
an old reference initial or from the first occurrence of the word.
-/

noncomputable section

open Set

namespace Erdos599
namespace Alternating
namespace FiniteColouredOccurrenceWord

open DirectedPath SwitchingCore.RelationalInterval

universe u

variable {V : Type u} {Gamma : DWeb V} {W Y : Set Gamma.DPath}

/-- Every positive-balance vertex of the exact occurrence switch is either
an old reference initial or the first occurrence of the transaction.  No
finite-character assumption is used for the reference warp. -/
theorem IsIntervalSafe.positiveBoundary_mem_initial_union_first
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x : V}
    (hx : edgeBalance
      ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) x = 1) :
    x ∈ Gamma.initialSet Y ∪ {Q.vertex 0} := by
  have hswitchBalance := edgeBalance_eq_of_incidence
    hW hY Q.backwardEdges_subset_familyEdges
      Q.forwardEdges_subset_familyEdges hQ.incoming_removed
        hQ.outgoing_removed x
  have hwordBalance := Q.edgeBalance_forward_sub_backward hW hY x
  by_cases hxs : x = Q.vertex 0
  · exact Or.inr (Set.mem_singleton_iff.mpr hxs)
  by_cases hxt : x = Q.vertex (Fin.last Q.length)
  · have hbaseImpossible : False := by
      rw [hswitchBalance] at hx
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
          propInt (x = Q.vertex 0) -
            propInt (x = Q.vertex (Fin.last Q.length)) at hwordBalance
      have hlastNotFirst : Q.vertex (Fin.last Q.length) ≠ Q.vertex 0 := by
        intro h
        exact hxs (hxt.trans h)
      have hdelta0 : edgeBalance Q.forwardEdges x -
          edgeBalance Q.backwardEdges x = (0 : ℤ) - 1 := by
        simpa only [hxt, propInt, if_true, hlastNotFirst, if_false] using
          hwordBalance
      have hdelta : edgeBalance Q.forwardEdges x -
          edgeBalance Q.backwardEdges x = -1 := by
        omega
      have hbase : edgeBalance (familyEdges Y) x = 2 := by
        omega
      by_cases hout : HasOutgoing (familyEdges Y) x <;>
        by_cases hin : HasIncoming (familyEdges Y) x <;>
          simp [edgeBalance, propInt, hout, hin] at hbase
    exact False.elim hbaseImpossible
  · left
    have hbase : edgeBalance (familyEdges Y) x = 1 := by
      rw [hswitchBalance] at hx
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
          propInt (x = Q.vertex 0) -
            propInt (x = Q.vertex (Fin.last Q.length)) at hwordBalance
      simp only [hxs, hxt, propInt, if_false] at hwordBalance
      omega
    exact
      (_root_.Erdos599.Alternating.TerminalContactSwitch.mem_initialSet_iff_isolated_or_edgeBalance_eq_one_anyWarp
        hY).mpr
        (Or.inr hbase)

/-- Actual reachability of every nonisolated sink of the exact finite
occurrence switch.  This is the transaction consumer needed by grounding:
cycles are harmless, reference rays are allowed, and the conclusion is a
literal path in the switched relation. -/
theorem IsIntervalSafe.sink_rooted_from_initial_union_first
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {t : V}
    (ht : t ∈ Gamma.initialSet Y ∪ {Q.vertex 0} ∨
      HasIncoming ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t)
    (hsink : ¬HasOutgoing
      ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t) :
    ∃ a ∈ Gamma.initialSet Y ∪ {Q.vertex 0},
      Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈
          (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) a t := by
  let E := (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges
  apply GroundingFinitePerturbationRooting.sink_rooted_of_finitePerturbation
    hY E Q.forwardEdges (Gamma.initialSet Y ∪ {Q.vertex 0})
  · rintro e (he | he)
    · exact familyEdges_subset_adj Y he.1
    · exact familyEdges_subset_adj W
        (Q.forwardEdges_subset_familyEdges he)
  · exact biUnique_of_incident_reference_edges_removed
      hW hY Q.forwardEdges_subset_familyEdges
        hQ.incoming_removed hQ.outgoing_removed
  · exact Q.forwardEdges_finite
  · intro e he
    exact he.elim (fun h ↦ Or.inl h.1) Or.inr
  · intro x hx
    exact hQ.positiveBoundary_mem_initial_union_first hW hY hx
  · exact ht
  · exact hsink

/-- A reference initial genuinely consumed by one finite occurrence word is
necessarily the final occurrence of that word.  In particular, a single
word cannot consume two distinct disallowed reference initials.  This is
the signed-balance restriction behind the more convenient
`positiveBoundary_mem_of_initial_consumed` interface below. -/
theorem IsIntervalSafe.initial_consumed_eq_last
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    {x : V}
    (hx : x ∈ Gamma.initialSet Y)
    (hback : HasOutgoing Q.backwardEdges x)
    (hnoForward : ¬HasOutgoing Q.forwardEdges x) :
    x = Q.vertex (Fin.last Q.length) := by
  have hnoBaseIncoming : ¬HasIncoming (familyEdges Y) x := by
    intro hin
    have hx' := hx
    rw [_root_.Erdos599.Alternating.TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
      hY] at hx'
    exact hx'.2 hin
  have hnoBackwardIncoming : ¬HasIncoming Q.backwardEdges x := by
    rintro ⟨y, hy⟩
    exact hnoBaseIncoming ⟨y, Q.backwardEdges_subset_familyEdges hy⟩
  have hnoForwardIncoming : ¬HasIncoming Q.forwardEdges x := by
    rintro ⟨y, hy⟩
    exact (hQ.endpoint_pure hy).1 hx
  have hbalance := Q.edgeBalance_forward_sub_backward hW hY x
  by_contra hlast
  simp only [edgeBalance, hnoForward, hnoForwardIncoming,
    hback, hnoBackwardIncoming, propInt, if_false, if_true, hlast] at hbalance
  split at hbalance <;> omega

/-- Sharpen the positive boundary to an externally supplied allowed-source
set.  Every old reference initial outside `A` must be consumed as the lower
end of a removed interval, and no inserted edge may leave it.  This is the
exact condition needed for hanging-owner pruning: a terminal request at the
owner's marker removes the old initial instead of preserving it as a new
root. -/
theorem IsIntervalSafe.positiveBoundary_mem_of_initial_consumed
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (A : Set V)
    (hfirst : Q.vertex 0 ∈ A)
    (hconsume : ∀ x ∈ Gamma.initialSet Y, x ∉ A →
      HasOutgoing Q.backwardEdges x ∧ ¬HasOutgoing Q.forwardEdges x)
    {x : V}
    (hx : edgeBalance
      ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) x = 1) :
    x ∈ A := by
  have hxCoarse := hQ.positiveBoundary_mem_initial_union_first hW hY hx
  rcases hxCoarse with hxInitial | hxFirst
  · by_contra hxA
    obtain ⟨hremoved, hnoForward⟩ := hconsume x hxInitial hxA
    have hnoOut : ¬HasOutgoing
        ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) x := by
      rintro ⟨y, hy⟩
      rcases hy with hyOld | hyForward
      · obtain ⟨z, hzRemoved⟩ := hremoved
        have hyz : y = z := (IsWarp.familyEdges_biUnique hY).2
          hyOld.1 (Q.backwardEdges_subset_familyEdges hzRemoved)
        exact hyOld.2 (hyz ▸ hzRemoved)
      · exact hnoForward ⟨y, hyForward⟩
    have hnoIn : ¬HasIncoming
        ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) x := by
      rintro ⟨y, hy⟩
      rcases hy with hyOld | hyForward
      · exact
          (by
            have hxInitial' := hxInitial
            rw [_root_.Erdos599.Alternating.TerminalContactSwitch.initialSet_eq_vertexSet_diff_hasIncoming_anyWarp
              hY] at hxInitial'
            exact hxInitial'.2 ⟨y, hyOld.1⟩)
      · exact (hQ.endpoint_pure hyForward).1 hxInitial
    simp [edgeBalance, propInt, hnoOut, hnoIn] at hx
  · rw [Set.mem_singleton_iff] at hxFirst
    rw [hxFirst]
    exact hfirst

/-- Allowed-source sink rooting for an interval-safe finite transaction.
The reference warp may contain rays and may have disallowed hanging
initials, provided the word genuinely consumes each such initial. -/
theorem IsIntervalSafe.sink_rooted_of_initial_consumed
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (A : Set V)
    (hfirst : Q.vertex 0 ∈ A)
    (hconsume : ∀ x ∈ Gamma.initialSet Y, x ∉ A →
      HasOutgoing Q.backwardEdges x ∧ ¬HasOutgoing Q.forwardEdges x)
    {t : V}
    (ht : t ∈ A ∨
      HasIncoming ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t)
    (hsink : ¬HasOutgoing
      ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun x y ↦ (x, y) ∈
        (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) a t := by
  let E := (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges
  apply GroundingFinitePerturbationRooting.sink_rooted_of_finitePerturbation
    hY E Q.forwardEdges A
  · rintro e (he | he)
    · exact familyEdges_subset_adj Y he.1
    · exact familyEdges_subset_adj W
        (Q.forwardEdges_subset_familyEdges he)
  · exact biUnique_of_incident_reference_edges_removed
      hW hY Q.forwardEdges_subset_familyEdges
        hQ.incoming_removed hQ.outgoing_removed
  · exact Q.forwardEdges_finite
  · intro e he
    exact he.elim (fun h ↦ Or.inl h.1) Or.inr
  · intro x hx
    exact hQ.positiveBoundary_mem_of_initial_consumed
      hW hY A hfirst hconsume hx
  · exact ht
  · exact hsink

/-- Local alternative to consuming every disallowed reference initial.  It
is enough to prove that no such initial reaches the particular sink being
settled.  This is the form used after a last-contact split: the discarded
hanging prefix may keep its marker initial, while the relevant sink lies on
the source-attached suffix and hence outside that component. -/
theorem IsIntervalSafe.sink_rooted_of_disallowed_initial_not_reaches
    {Q : FiniteColouredOccurrenceWord W Y} (hQ : Q.IsIntervalSafe)
    (hW : Gamma.IsWarp W) (hY : Gamma.IsWarp Y)
    (A : Set V)
    (hfirst : Q.vertex 0 ∈ A)
    {t : V}
    (hbad : ∀ x ∈ Gamma.initialSet Y, x ∉ A →
      ¬Relation.ReflTransGen
        (fun u v ↦ (u, v) ∈
          (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) x t)
    (ht : t ∈ A ∨
      HasIncoming ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t)
    (hsink : ¬HasOutgoing
      ((familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) t) :
    ∃ a ∈ A, Relation.ReflTransGen
      (fun u v ↦ (u, v) ∈
        (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges) a t := by
  let E := (familyEdges Y \ Q.backwardEdges) ∪ Q.forwardEdges
  let B := A ∪ {x | edgeBalance E x = 1}
  have hrootB : ∃ b ∈ B,
      Relation.ReflTransGen (fun u v ↦ (u, v) ∈ E) b t := by
    apply GroundingFinitePerturbationRooting.sink_rooted_of_finitePerturbation
      hY E Q.forwardEdges B
    · rintro e (he | he)
      · exact familyEdges_subset_adj Y he.1
      · exact familyEdges_subset_adj W
          (Q.forwardEdges_subset_familyEdges he)
    · exact biUnique_of_incident_reference_edges_removed
        hW hY Q.forwardEdges_subset_familyEdges
          hQ.incoming_removed hQ.outgoing_removed
    · exact Q.forwardEdges_finite
    · intro e he
      exact he.elim (fun h ↦ Or.inl h.1) Or.inr
    · intro x hx
      exact Or.inr hx
    · exact ht.elim (fun h ↦ Or.inl (Or.inl h)) Or.inr
    · exact hsink
  obtain ⟨b, hbB, hbt⟩ := hrootB
  rcases hbB with hbA | hbBalance
  · exact ⟨b, hbA, hbt⟩
  · have hbCoarse := hQ.positiveBoundary_mem_initial_union_first
        hW hY hbBalance
    rcases hbCoarse with hbInitial | hbFirst
    · by_cases hbA : b ∈ A
      · exact ⟨b, hbA, hbt⟩
      · exact False.elim (hbad b hbInitial hbA hbt)
    · rw [Set.mem_singleton_iff] at hbFirst
      refine ⟨b, ?_, hbt⟩
      rw [hbFirst]
      exact hfirst

end FiniteColouredOccurrenceWord
end Alternating
end Erdos599

#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.positiveBoundary_mem_initial_union_first
#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.sink_rooted_from_initial_union_first
#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.initial_consumed_eq_last
#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.positiveBoundary_mem_of_initial_consumed
#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.sink_rooted_of_initial_consumed
#print axioms
  Erdos599.Alternating.FiniteColouredOccurrenceWord.IsIntervalSafe.sink_rooted_of_disallowed_initial_not_reaches
