/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.SingularNonSourceArrowProfile

/-!
# Target endpoints obstruct the whole-carrier non-source arrow

The meeting premise in `SingularNonSourceArrowProfile.NonSourceArrowExchange`
cannot hold when the quotient commitment contains a target vertex.  Such a
vertex is both a source and a target of the quotient.  A quotient wave must
therefore catch its trivial target path at that vertex.  Since the quotient
has no edge entering the commitment, the catching member is itself trivial,
and hence has no support vertex outside the commitment.

This applies in particular to a source--target linkage carrier: its
non-source part normally contains its terminal target vertices.  Thus the
whole non-source carrier cannot be restored by a single direct application
of the deletion--quotient arrow.  Target endpoints have to be excluded from
the commitment and restored jointly with the selected linkage (or by an
equivalent rerouting construction).
-/

noncomputable section

open Set

namespace Erdos599
namespace CardinalInduction
namespace SingularNonSourceArrowTargetObstruction

open DirectedPath SingularNonSourceArrowProfile

universe u

variable {V : Type u}

/-- No edge of the quotient enters the set by which we quotient. -/
theorem quotient_walk_start_eq_finish_of_finish_mem
    (G : DWeb V) (Z : Set V) {a b : V}
    (p : Walk (G.quotient Z).graph a b) (hb : b ∈ Z) :
    a = b := by
  induction p with
  | nil => rfl
  | @cons a c b hac p ih =>
      have hcb : c = b := ih hb
      subst c
      exact (hac.2.2.2 hb).elim

/-- A simple walk with equal endpoints has singleton list support. -/
private theorem walk_support_eq_singleton_of_isPath_of_endpoints_eq
    {D : Digraph V} {a b : V} (w : Walk D a b)
    (hw : w.IsPath) (h : a = b) : w.support = [a] := by
  induction w with
  | nil => rfl
  | @cons a b c hab w ih =>
      have hn : a ∉ w.support := (List.nodup_cons.1 hw).1
      exact (hn (h ▸ w.end_mem_support)).elim

/-- A simple finite path with equal endpoints has singleton support. -/
private theorem finitePath_support_eq_singleton_of_start_eq_finish
    {D : Digraph V} (p : FinitePath D) (h : p.start = p.finish) :
    p.support = {p.start} := by
  have hwalk : p.walk.support = [p.start] :=
    walk_support_eq_singleton_of_isPath_of_endpoints_eq p.walk p.isPath h
  ext x
  change x ∈ p.walk.support ↔ x ∈ ({p.start} : Set V)
  rw [hwalk]
  simp only [List.mem_singleton, Set.mem_singleton_iff]

/-- The proposed whole-non-source-carrier exchange is impossible as soon as
the carrier contains a target which is not an ambient source. -/
theorem not_nonSourceArrowExchange_of_target_mem
    (G : DWeb V) (X : Set V)
    (hbad : ((X \ G.source) ∩ G.target).Nonempty) :
    ¬ NonSourceArrowExchange G X := by
  intro hexchange
  obtain ⟨x, hxZ, hxTarget⟩ := hbad
  obtain ⟨M, hMmax⟩ := (G.delete X).exists_maximal_wave
  obtain ⟨W, hmeet⟩ := hexchange M hMmax
  have hxQSource : x ∈ (G.quotient (X \ G.source)).source := by
    exact target_mem_essential hxTarget (Or.inr hxZ)
  let trivial : FinitePath (G.quotient (X \ G.source)).graph :=
    FinitePath.trivial (G.quotient (X \ G.source)).graph x
  obtain ⟨y, hyTrivial, hyFrontier⟩ := W.2.2.2 hxQSource trivial
    ⟨rfl, hxTarget⟩
  have hyx : y = x := by
    simpa only [trivial, FinitePath.support_trivial,
      Set.mem_singleton_iff] using hyTrivial
  subst y
  obtain ⟨q, hqW, hqTerminal⟩ := hyFrontier
  obtain ⟨u, huq, huOutside, _huRoof⟩ := hmeet q hqW
  rcases q with q | ray
  · have hqFinish : q.finish = x := Option.some.inj hqTerminal
    have hqFinishZ : q.finish ∈ X \ G.source := hqFinish ▸ hxZ
    have hqEnds : q.start = q.finish :=
      quotient_walk_start_eq_finish_of_finish_mem G (X \ G.source)
        q.walk hqFinishZ
    have hqStart : q.start = x := hqEnds.trans hqFinish
    have hqSupport : q.support = {q.start} :=
      finitePath_support_eq_singleton_of_start_eq_finish q hqEnds
    have hux : u = x := by
      change u ∈ q.support at huq
      rw [hqSupport, Set.mem_singleton_iff] at huq
      exact huq.trans hqStart
    exact huOutside (hux ▸ hxZ)
  · simp at hqTerminal

/-- Consequently the whole-non-source-carrier exchange fails for every
nonempty source--target linkage when the ambient source and target are
disjoint.  This is the exact situation of the normalized web encoding of
the original disjoint endpoint sets. -/
theorem not_nonSourceArrowExchange_vertexSet_of_nonempty_linkage
    {G : DWeb V} (hSourceTarget : Disjoint G.source G.target)
    {A : Set V} {P : Set G.DPath}
    (hP : IsLinkageBetween G A G.target P) (hPnonempty : P.Nonempty) :
    ¬ NonSourceArrowExchange G (G.vertexSet P) := by
  apply not_nonSourceArrowExchange_of_target_mem
  obtain ⟨p, hpP⟩ := hPnonempty
  obtain ⟨q, rfl⟩ := hP.finiteCharacter hpP
  have hqTarget : q.finish ∈ G.target :=
    hP.terminalFrontier_subset ⟨Sum.inl q, hpP, rfl⟩
  have hqNotSource : q.finish ∉ G.source := by
    intro hqSource
    exact Set.disjoint_left.1 hSourceTarget hqSource hqTarget
  exact ⟨q.finish, ⟨⟨Sum.inl q, hpP, q.finish_mem_support⟩,
    hqNotSource⟩, hqTarget⟩

#print axioms quotient_walk_start_eq_finish_of_finish_mem
#print axioms not_nonSourceArrowExchange_of_target_mem
#print axioms not_nonSourceArrowExchange_vertexSet_of_nonempty_linkage

end SingularNonSourceArrowTargetObstruction
end CardinalInduction
end Erdos599
