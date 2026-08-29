/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ArcSubdivisionNoStrong
import ErdosProblems.Erdos599.ColouredSafeShortcutGraph
import ErdosProblems.Erdos599.MarkedRaySubset

/-!
# Native strong shortcuts are not real subdivision edges

The native coloured-safe definition of a strong shortcut is phrased using
ambient occurrence words, rather than the legacy alternating-path hammock.
At two exposed finite endpoints the exact signed word balance forces a
forward edge leaving the source and a forward edge entering the terminal.
If the ambient real edge has subdivision incidence, uniqueness on one of
those two sides identifies that forward edge with the real edge itself.
The one-edge real path is then already contained in the switched relation,
contradicting native nondegeneracy.

The final section uses the shared owner-tail theorem for rays contained in
a warp relation. It is not enough to mark only literal ray members of a
warp: a contained ray may start in the middle of such a member.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

open DirectedPath Alternating

universe u

variable {V : Type u} {Gamma : DWeb V}

namespace ColouredSafeAmbientOccurrence

open ColouredSafeReverseReachability

variable {Y : Set Gamma.DPath} {s t : V}

private def terminalDefect (A : Occurrence Y s) (x : V) : Int :=
  match A.terminal? with
  | none => 0
  | some z => propInt (x = z)

private theorem backwardEdges_subset_reference (A : Occurrence Y s) :
    A.backwardEdges ⊆ familyEdges Y := by
  cases A with
  | infinite Q => exact Q.backwardEdges_subset_familyEdges
  | finite z Q => exact Q.backwardEdges_subset_familyEdges

/-- Exact signed balance of a valid ambient occurrence, independent of any
roof localization. -/
theorem Valid.edgeBalance_forward_sub_backward
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y) (x : V) :
    edgeBalance A.forwardEdges x - edgeBalance A.backwardEdges x =
      propInt (x = s) - terminalDefect A x := by
  obtain ⟨W, hW, _hWfinite, hforward⟩ := hA
  cases A with
  | infinite Q hQ hfirst =>
      have hbalance :=
        (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hY x
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
        propInt (x = Q.vertex 0) at hbalance
      simpa only [ColouredSafeReverseReachability.CurrentSafeOccurrence.forwardEdges,
        ColouredSafeReverseReachability.CurrentSafeOccurrence.backwardEdges,
        terminalDefect,
        ColouredSafeReverseReachability.CurrentSafeOccurrence.terminal?, hfirst,
        sub_zero] using hbalance
  | finite z Q hQ hfirst hlast =>
      have hbalance :=
        (Q.retypeForward hforward).edgeBalance_forward_sub_backward hW hY x
      change edgeBalance Q.forwardEdges x - edgeBalance Q.backwardEdges x =
        propInt (x = Q.vertex 0) -
          propInt (x = Q.vertex (Fin.last Q.length)) at hbalance
      simpa only [ColouredSafeReverseReachability.CurrentSafeOccurrence.forwardEdges,
        ColouredSafeReverseReachability.CurrentSafeOccurrence.backwardEdges,
        terminalDefect,
        ColouredSafeReverseReachability.CurrentSafeOccurrence.terminal?, hfirst,
        hlast] using hbalance

/-- At distinct endpoints outside the reference warp, a valid finite ambient
occurrence has a literal forward edge leaving its source and one entering
its terminal. -/
theorem Valid.forward_endpoint_incidence
    {A : Occurrence Y s} (hA : Valid A) (hY : Gamma.IsWarp Y)
    (hend : A.terminal? = some t) (hne : s ≠ t)
    (hsOff : s ∉ Gamma.vertexSet Y) (htOff : t ∉ Gamma.vertexSet Y) :
    HasOutgoing A.forwardEdges s ∧ HasIncoming A.forwardEdges t := by
  have hback := backwardEdges_subset_reference A
  have hBOutS : ¬HasOutgoing A.backwardEdges s := by
    rintro ⟨z, hsz⟩
    exact hsOff (familyEdges_subset_vertexSet_prod Y (hback hsz)).1
  have hBInS : ¬HasIncoming A.backwardEdges s := by
    rintro ⟨z, hzs⟩
    exact hsOff (familyEdges_subset_vertexSet_prod Y (hback hzs)).2
  have hBOutT : ¬HasOutgoing A.backwardEdges t := by
    rintro ⟨z, htz⟩
    exact htOff (familyEdges_subset_vertexSet_prod Y (hback htz)).1
  have hBInT : ¬HasIncoming A.backwardEdges t := by
    rintro ⟨z, hzt⟩
    exact htOff (familyEdges_subset_vertexSet_prod Y (hback hzt)).2
  have hBalS := hA.edgeBalance_forward_sub_backward hY s
  have hBalT := hA.edgeBalance_forward_sub_backward hY t
  have hBackS : edgeBalance A.backwardEdges s = 0 := by
    simp [edgeBalance, hBOutS, hBInS]
  have hBackT : edgeBalance A.backwardEdges t = 0 := by
    simp [edgeBalance, hBOutT, hBInT]
  have hForwardS : edgeBalance A.forwardEdges s = 1 := by
    simp [terminalDefect, hend, propInt, hne, hBackS] at hBalS
    exact hBalS
  have hForwardT : edgeBalance A.forwardEdges t = -1 := by
    have hts : t ≠ s := Ne.symm hne
    simp [terminalDefect, hend, propInt, hts, hBackT] at hBalT
    exact hBalT
  exact ⟨(edgeBalance_eq_one_iff.mp hForwardS).1,
    (edgeBalance_eq_neg_one_iff.mp hForwardT).1⟩

end ColouredSafeAmbientOccurrence

namespace Blueprint.ColouredSafeShortcutGraph

open ColouredSafeReverseReachability ColouredSafeAmbientOccurrence

variable {Y W : Set Gamma.DPath} {rho : Cardinal.{u}} {s t : V}

private def oneEdgeFinitePath (hst : Gamma.graph.Adj s t) (hne : s ≠ t) :
    FinitePath Gamma.graph where
  start := s
  finish := t
  walk := .cons hst .nil
  isPath := by
    simp only [Walk.IsPath, Walk.support_cons, Walk.support_nil]
    simp [hne]

private theorem oneEdgeFinitePath_edgeSet
    (hst : Gamma.graph.Adj s t) (hne : s ≠ t) :
    (oneEdgeFinitePath hst hne).edgeSet = {(s, t)} := by
  simp [oneEdgeFinitePath, FinitePath.edgeSet, Walk.edgeSet]

/-- Subdivision incidence turns the endpoint balance of any admissible
native finite occurrence into the literal direct switched path. -/
theorem hasFiniteSwitchedPathTo_of_subdivisionIncidence
    (hY : Gamma.IsWarp Y) (hinc : HasSubdivisionIncidenceAt Gamma.graph s t)
    {A : Occurrence Y s} (hvalid : Valid A)
    (hend : A.terminal? = some t)
    (hsOff : s ∉ Gamma.vertexSet Y) (htOff : t ∉ Gamma.vertexSet Y) :
    A.HasFiniteSwitchedPathTo t := by
  obtain ⟨hne, hinc | hinc⟩ := hinc
  all_goals
    obtain ⟨hOut, hIn⟩ :=
      hvalid.forward_endpoint_incidence hY hend hne hsOff htOff
    obtain ⟨W, _hW, _hWfinite, hforward⟩ := hvalid
  · obtain ⟨x, hxt⟩ := hIn
    obtain ⟨w, _hws, _hwt, huniq, _hout⟩ := hinc
    have hxtAdj : Gamma.graph.Adj x t :=
      familyEdges_subset_adj W (hforward hxt)
    have hxs : x = s := huniq hxtAdj
    have hstForward : (s, t) ∈ A.forwardEdges := by simpa [hxs] using hxt
    let p := oneEdgeFinitePath hxtAdj (hxs ▸ hne)
    refine ⟨p, ?_, rfl, ?_⟩
    · exact hxs
    · intro e he
      have heq : e = (s, t) := by
        simpa only [p, oneEdgeFinitePath_edgeSet, Set.mem_singleton_iff,
          hxs] using he
      subst e
      exact Or.inr hstForward
  · obtain ⟨y, hsy⟩ := hOut
    obtain ⟨w, _hws, _hwt, huniq, _hin⟩ := hinc
    have hsyAdj : Gamma.graph.Adj s y :=
      familyEdges_subset_adj W (hforward hsy)
    have hyt : y = t := huniq hsyAdj
    have hstForward : (s, t) ∈ A.forwardEdges := by simpa [hyt] using hsy
    have hsyne : s ≠ y := fun hsyEq ↦ hne (hsyEq.trans hyt)
    let p := oneEdgeFinitePath hsyAdj hsyne
    refine ⟨p, rfl, ?_, ?_⟩
    · exact hyt
    · intro e he
      have heq : e = (s, t) := by
        simpa only [p, oneEdgeFinitePath_edgeSet, Set.mem_singleton_iff,
          hyt] using he
      subst e
      exact Or.inr hstForward

/-- A real edge with hereditary subdivision incidence cannot be a native
strong shortcut.  This is the native occurrence theorem, not a cast from
the legacy alternating-path predicate. -/
theorem not_isStrong_of_subdivisionIncidence
    (hY : Gamma.IsWarp Y) (hinc : HasSubdivisionIncidenceAt Gamma.graph s t) :
    ¬IsStrong Y rho s t := by
  rintro ⟨H, hH, hcard⟩
  have hEmpty : H = ∅ := by
    ext A
    constructor
    · intro hAH
      obtain ⟨hvalid, hend, hsOff, htOff, hnondeg⟩ := hH.1 hAH
      exact False.elim <| hnondeg
        (hasFiniteSwitchedPathTo_of_subdivisionIncidence hY hinc hvalid hend
          hsOff (htOff t rfl))
    · simp
  have hzero : succ rho = 0 := by
    simpa [hEmpty] using hcard.symm
  have hrho : rho < 0 := by simpa [hzero] using (lt_succ rho)
  exact (not_lt_of_ge (zero_le : (0 : Cardinal) ≤ rho)) hrho

theorem HasHereditarySubdivisionIncidence.no_nativeStrong_realEdge
    (hGamma : HasHereditarySubdivisionIncidence Gamma.graph)
    (hY : Gamma.IsWarp Y) (hst : Gamma.graph.Adj s t) :
    ¬IsStrong Y rho s t :=
  not_isStrong_of_subdivisionIncidence hY (hGamma hst)

end Blueprint.ColouredSafeShortcutGraph

namespace Blueprint.ColouredSafeShortcutGraph

variable {Y W : Set Gamma.DPath} {rho : Cardinal.{u}}

/-- A warp whose ray members have infinitely many native strong marks cannot
contain a real directed ray when the real web has hereditary subdivision
incidence.  The owner-tail theorem above handles rays starting mid-owner. -/
theorem DWeb.IsWarp.not_exists_realRay_of_nativeStrong_marks
    (hW : Gamma.IsWarp W)
    (hmarked : Gamma.InfinitelyManyMarkedEdges W (IsStrong Y rho))
    (hY : Gamma.IsWarp Y)
    (hGamma : HasHereditarySubdivisionIncidence Gamma.graph) :
    ¬∃ r : Ray Gamma.graph, r.edgeSet ⊆ familyEdges W := by
  rintro ⟨r, hr⟩
  have hinfinite := hW.markedIndices_infinite_of_edgeSet_subset hmarked r hr
  obtain ⟨n, hn⟩ := hinfinite.nonempty
  exact (not_isStrong_of_subdivisionIncidence hY (hGamma (r.adj_succ n))) hn

/-- Canonical native form: the marked warp lives in the imaginary web, but
the forbidden contained ray consists entirely of original real edges. -/
theorem not_exists_originalRay_in_nativeWarp_of_strong_marks
    {W : Set (imaginaryWeb Y rho).DPath}
    (hW : (imaginaryWeb Y rho).IsWarp W)
    (hmarked : (imaginaryWeb Y rho).InfinitelyManyMarkedEdges W
      (IsStrong Y rho))
    (hY : Gamma.IsWarp Y)
    (hGamma : HasHereditarySubdivisionIncidence Gamma.graph) :
    ¬∃ r : Ray Gamma.graph, r.edgeSet ⊆ familyEdges W := by
  rintro ⟨r, hr⟩
  let q : Ray (imaginaryWeb Y rho).graph := {
    toFun := r
    adj_succ := by
      intro n
      change Gamma.graph.Adj (r n) (r (n + 1)) ∨
        IsImaginary Y rho (r n) (r (n + 1))
      exact Or.inl (r.adj_succ n)
    injective := r.injective }
  have hq : q.edgeSet ⊆ familyEdges W := by
    simpa only [q, Ray.edgeSet] using hr
  have hinfinite := hW.markedIndices_infinite_of_edgeSet_subset hmarked q hq
  obtain ⟨n, hn⟩ := hinfinite.nonempty
  have hnStrong : IsStrong Y rho (r n) (r (n + 1)) := by
    change IsStrong Y rho (q n) (q (n + 1)) at hn
    simpa only [q] using hn
  exact (not_isStrong_of_subdivisionIncidence hY
    (hGamma (r.adj_succ n))) hnStrong

/-- Relation-facing form used by native blueprint limits.  A directed ray in
the intersection of the warp relation with the original graph would induce
the original-graph ray excluded above. -/
theorem nativeWarp_realEdges_not_containsDirectedRay
    {W : Set (imaginaryWeb Y rho).DPath}
    (hW : (imaginaryWeb Y rho).IsWarp W)
    (hmarked : (imaginaryWeb Y rho).InfinitelyManyMarkedEdges W
      (IsStrong Y rho))
    (hY : Gamma.IsWarp Y)
    (hGamma : HasHereditarySubdivisionIncidence Gamma.graph) :
    ¬ContainsDirectedRay
      (familyEdges W ∩ {e | Gamma.graph.Adj e.1 e.2}) := by
  rintro ⟨R, hR⟩
  let r : Ray Gamma.graph := {
    toFun := R.vertex
    adj_succ := fun n ↦ (hR ⟨n, rfl⟩).2
    injective := R.injective }
  apply not_exists_originalRay_in_nativeWarp_of_strong_marks
    hW hmarked hY hGamma
  refine ⟨r, ?_⟩
  rintro e ⟨n, rfl⟩
  exact (hR ⟨n, rfl⟩).1

#print axioms ColouredSafeAmbientOccurrence.Valid.forward_endpoint_incidence
#print axioms hasFiniteSwitchedPathTo_of_subdivisionIncidence
#print axioms not_isStrong_of_subdivisionIncidence
#print axioms DWeb.IsWarp.markedIndices_infinite_of_edgeSet_subset
#print axioms DWeb.IsWarp.not_exists_realRay_of_nativeStrong_marks
#print axioms not_exists_originalRay_in_nativeWarp_of_strong_marks
#print axioms nativeWarp_realEdges_not_containsDirectedRay

end Blueprint.ColouredSafeShortcutGraph

end Erdos599
