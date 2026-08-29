/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingPreStoppedSelfOwnerDescent

/-!
# Length descent for finite initial prefixes

The root recursion in the proof of Assertion 8.22 uses finite rooted
prefixes even when their ambient ladder member is a ray.  This file proves
that strict intrinsic order of their terminal vertices is exactly strict
order of their lengths.  The proof does not assume that the ambient member
is finite: a walk which starts at the initial vertex and uses only ray
edges reaches ray index equal to its length.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingPathPrefix

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace InitialPrefixMeasure

/-- A walk contained in a finite path reaches, after `q.length` edges, the
ambient support position obtained by advancing `q.length` from its start. -/
theorem finitePath_getElem_start_add_length
    (P : FinitePath Gamma.graph) {a b : V}
    (q : Walk Gamma.graph a b) (hq : q.edgeSet ⊆ P.edgeSet)
    {s : ℕ} (hs : s < P.walk.support.length)
    (hstart : P.walk.support[s] = a) :
    ∃ h : s + q.length < P.walk.support.length,
      P.walk.support[s + q.length] = b := by
  induction q generalizing s with
  | nil =>
      exact ⟨by simpa using hs, by simpa using hstart⟩
  | @cons a c b hac q ih =>
      have hacP : (a, c) ∈ P.edgeSet := by
        apply hq
        simp
      obtain ⟨n, hn, hna, hnc⟩ :=
        P.walk.exists_adjacent_getElem_of_mem_edgeSet hacP
      have hsn : s = n := by
        have hget : P.walk.support[s] = P.walk.support[n] :=
          hstart.trans hna.symm
        exact congrArg Fin.val <| P.isPath.get_inj_iff.mp hget
      have htail : q.edgeSet ⊆ P.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr he
      have hnc' : P.walk.support[n + 1] = c := hnc
      obtain ⟨hbound, hend⟩ :=
        ih htail (s := n + 1) hn hnc'
      subst s
      refine ⟨?_, ?_⟩
      · simpa only [Walk.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hbound
      · simpa only [Walk.length_cons, Nat.add_assoc, Nat.add_comm,
          Nat.add_left_comm] using hend

/-- Ray analogue of `finitePath_getElem_start_add_length`. -/
theorem ray_get_start_add_length
    (r : Ray Gamma.graph) {a b : V}
    (q : Walk Gamma.graph a b) (hq : q.edgeSet ⊆ r.edgeSet)
    {s : ℕ} (hstart : r s = a) : r (s + q.length) = b := by
  induction q generalizing s with
  | nil => simpa using hstart
  | @cons a c b hac q ih =>
      have hacR : (a, c) ∈ r.edgeSet := by
        apply hq
        simp
      rcases hacR with ⟨n, hn⟩
      have hsn : s = n := by
        apply r.injective
        exact hstart.trans (congrArg Prod.fst hn)
      have htail : q.edgeSet ⊆ r.edgeSet := by
        intro e he
        apply hq
        simp only [Walk.edgeSet_cons, Set.mem_union,
          Set.mem_singleton_iff]
        exact Or.inr he
      have hnext : r (n + 1) = c := (congrArg Prod.snd hn).symm
      have hend := ih htail (s := n + 1) hnext
      subst s
      simpa only [Walk.length_cons, Nat.add_assoc, Nat.add_comm,
        Nat.add_left_comm] using hend

/-- A finite path starting at the ambient initial vertex and using only
ambient edges has its finish at the occurrence indexed by its length. -/
theorem occursAt_finish_at_length
    (P : Gamma.DPath) (q : FinitePath Gamma.graph)
    (hstart : q.start = P.initial) (hq : q.edgeSet ⊆ P.edgeSet) :
    GroundingCut.OccursAt P q.walk.length q.finish := by
  cases P with
  | inl p =>
      change q.start = p.start at hstart
      have hzero : p.walk.support[0] = q.start := by
        exact p.support_getElem_zero.trans hstart.symm
      obtain ⟨hbound, hend⟩ :=
        finitePath_getElem_start_add_length p q.walk hq
          p.support_length_pos hzero
      exact ⟨by simpa using hbound, by simpa using hend⟩
  | inr r =>
      change q.start = r.initial at hstart
      have hzero : r 0 = q.start := by
        exact (by rfl : r 0 = r.initial).trans hstart.symm
      change r q.walk.length = q.finish
      simpa using ray_get_start_add_length r q.walk hq hzero

/-- Strict ambient order of the finishes of two finite initial prefixes is
strict order of their edge lengths.  This is the secondary natural-number
measure used by the recursive grounding repair. -/
theorem length_lt_of_strictly_before_finishes
    (P : Gamma.DPath)
    (q r : FinitePath Gamma.graph)
    (hqStart : q.start = P.initial)
    (hrStart : r.start = P.initial)
    (hqEdges : q.edgeSet ⊆ P.edgeSet)
    (hrEdges : r.edgeSet ⊆ P.edgeSet)
    (hbefore : GroundingCut.Before P q.finish r.finish) :
    q.walk.length < r.walk.length := by
  rcases hbefore.1 with ⟨m, n, hmq, hnr, hmn⟩
  have hqOccurs := occursAt_finish_at_length P q hqStart hqEdges
  have hrOccurs := occursAt_finish_at_length P r hrStart hrEdges
  have hqm : q.walk.length = m :=
    GroundingCutDecoder.occursAt_index_injective hqOccurs hmq
  have hrn : r.walk.length = n :=
    GroundingCutDecoder.occursAt_index_injective hrOccurs hnr
  rw [hqm, hrn]
  apply lt_of_le_of_ne hmn
  intro hnm
  apply hbefore.2
  cases P with
  | inl p =>
      rcases hmq with ⟨hm, hmq⟩
      rcases hnr with ⟨hn, hnr⟩
      exact hmq.symm.trans (by simpa only [hnm] using hnr)
  | inr ray =>
      change ray m = q.finish at hmq
      change ray n = r.finish at hnr
      exact hmq.symm.trans (by simpa only [hnm] using hnr)

end InitialPrefixMeasure

end GroundingPathPrefix
end Erdos599
