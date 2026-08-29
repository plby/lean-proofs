/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRelaxedEscape
import ErdosProblems.Erdos599.GroundingFiniteDescent

/-!
# Forward corridors into relaxed escapes

The finite descent in Assertion 8.18 repeatedly follows a piece of the
ambient source--cut path in the forward direction and then an already
constructed auxiliary suffix.  At its first ladder contact this forward
piece need not be an ordinary path in `Lambda`: its first connector is
allowed to leave an old ladder vertex virtually.  This file isolates the
two endpoint operations needed to compile that corridor.

The first theorem turns a relaxed connector into an ordinary connector as
soon as its old start is retained by `Lambda`.  The second theorem deals
with the other endpoint.  If an original edge enters a ladder vertex which
already has an ordinary escaping suffix, then either the old endpoint is
retained, or the first vertex of the suffix is necessarily the gadget of an
edge whose head is that endpoint.  In the latter case the original edge is
exactly the virtual connector required by `RelaxedForwardStep`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingRelaxedCorridor

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-- Consecutive support entries of a walk are adjacent.  This local copy
keeps the corridor module independent of the much later limits file. -/
private theorem walk_adj_getElem_succ {a b : V}
    (p : Walk Gamma.graph a b) (n : ℕ)
    (hn : n + 1 < p.support.length) :
    Gamma.graph.Adj p.support[n] p.support[n + 1] := by
  induction p generalizing n with
  | nil => simp at hn
  | @cons a c b e p ih =>
      cases n with
      | zero =>
          have hp0 : 0 < p.support.length :=
            List.length_pos_iff.mpr p.support_ne_nil
          have h0 : p.support[0] = c := by
            calc
              p.support[0] = p.support.head p.support_ne_nil :=
                List.getElem_zero hp0
              _ = c := p.head_support
          simpa [h0] using e
      | succ n =>
          have hn' : n + 1 < p.support.length := by simpa using hn
          simpa only [Walk.support_cons, List.getElem_cons_succ,
            Nat.add_assoc] using ih n hn'

/-- Loop-erase one new auxiliary edge in front of an avoiding route. -/
private theorem exists_avoiding_prepend
    (L : Input Gamma I) (C : Set (LV L))
    {a : LV L} (ha : a ∉ C)
    (q : FinitePath L.lambda.graph)
    (h : L.lambda.graph.Adj a q.start)
    (hq : L.lambda.Avoids q C) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = a ∧ r.finish = q.finish ∧ L.lambda.Avoids r C := by
  let w : Walk L.lambda.graph a q.finish := .cons h q.walk
  obtain ⟨p, hpSupport⟩ :=
    RelationalRoof.exists_pathTo_support_subset
      (R := L.lambda.graph.Adj) w
  let r : FinitePath L.lambda.graph :=
    { start := a
      finish := q.finish
      walk := p.1
      isPath := p.2 }
  refine ⟨r, rfl, rfl, ?_⟩
  change Disjoint r.support C
  rw [Set.disjoint_left]
  intro z hzr hzC
  have hzw : z ∈ w.support := hpSupport hzr
  simp only [w, Walk.support_cons, List.mem_cons] at hzw
  exact hzw.elim (fun hza ↦ ha (hza ▸ hzC))
    (fun hzq ↦ Set.disjoint_left.1 hq hzq hzC)

/-- At a retained old vertex, a start-relaxed escape is an ordinary
`C`-avoiding route.  In the virtual case we insert its first forward
connector and loop-erase the result. -/
theorem exists_ordinaryEscape_of_relaxed_of_start_mem
    (L : Input Gamma I) (C : Set (LV L)) {x : V}
    (hx : x ∈ L.offLadder ∪ L.finiteSource)
    (E : GroundingRelaxedEscape.RelaxedEscape L C x) :
    ∃ r : FinitePath L.lambda.graph,
      r.start = .old x ∧ r.finish ∈ L.lambda.target ∧
        L.lambda.Avoids r C := by
  rcases E.start_eq with hordinary | hrelaxed
  · exact ⟨E.route, hordinary, E.target, E.avoids⟩
  · have hadj : L.lambda.graph.Adj (.old x) E.route.start := by
      cases hstart : E.route.start with
      | old y =>
          rw [hstart] at hrelaxed
          have hrelaxed' : y ∈ L.offLadder ∪ L.targetMarkers ∧
              Gamma.graph.Adj x y := by
            change y ∈ L.offLadder ∪ L.targetMarkers ∧
              Gamma.graph.Adj x y at hrelaxed
            exact hrelaxed
          exact (L.lambda_adj_old_old x y).2
            ⟨hx, hrelaxed'.1, hrelaxed'.2⟩
      | edge u y =>
          rw [hstart] at hrelaxed
          have hrelaxed' : (u, y) ∈ L.familyEdges ∧
              Gamma.graph.Adj x y := by
            change (u, y) ∈ L.familyEdges ∧
              Gamma.graph.Adj x y at hrelaxed
            exact hrelaxed
          exact (L.lambda_adj_old_edge x u y).2
            ⟨hrelaxed'.1, Or.inr ⟨hx, hrelaxed'.2⟩⟩
      | proxy i =>
          rw [hstart] at hrelaxed
          change False at hrelaxed
          exact hrelaxed.elim
    obtain ⟨r, hrStart, hrFinish, hrAvoid⟩ :=
      exists_avoiding_prepend L C E.old_not_mem E.route hadj E.avoids
    exact ⟨r, hrStart, hrFinish ▸ E.target, hrAvoid⟩

/-- An ordinary escaping suffix at `y`, preceded by an original edge
`x → y`, is a start-relaxed escape at `x` whenever `y` is either an
ordinary retained right endpoint or a ladder vertex.

In the ladder case auxiliary separation rules out `y ∈ finiteSource`.
Since a ladder vertex is not in `offLadder`, the first edge of the suffix
must use the equality join into a represented edge with head `y`.  The
original edge `x → y` then supplies precisely the relaxed first
connector. -/
theorem relaxedEscape_of_adjacent_ordinary
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    {x y : V} (hxy : Gamma.graph.Adj x y)
    (hxNotC : (PopularAuxiliary.Input.LambdaVertex.old x : LV L) ∉ C)
    (hyBoundary :
      y ∈ L.offLadder ∪ L.targetMarkers ∨
        y ∈ Gamma.vertexSet L.ladder.paths)
    (q : FinitePath L.lambda.graph)
    (hqStart : q.start = .old y)
    (hqTarget : q.finish ∈ L.lambda.target)
    (hqAvoid : L.lambda.Avoids q C) :
    Nonempty (GroundingRelaxedEscape.RelaxedEscape L C x) := by
  rcases hyBoundary with hyRight | hyLadder
  · exact ⟨{
      route := q
      start_eq := Or.inr (by
        change L.RelaxedForwardStep x q.start
        rw [hqStart]
        exact ⟨hyRight, hxy⟩)
      target := hqTarget
      avoids := hqAvoid
      old_not_mem := hxNotC }⟩
  · have hyNotOff : y ∉ L.offLadder := by
      intro hyOff
      exact hyOff.2 hyLadder
    by_cases hyMarker : y ∈ L.targetMarkers
    · exact ⟨{
        route := q
        start_eq := Or.inr (by
          change L.RelaxedForwardStep x q.start
          rw [hqStart]
          exact ⟨Or.inr hyMarker, hxy⟩)
        target := hqTarget
        avoids := hqAvoid
        old_not_mem := hxNotC }⟩
    have hyNotFinite : y ∉ L.finiteSource := by
      intro hyFinite
      have hqSource : q.start ∈ L.lambda.source := by
        simpa only [hqStart] using
          (L.mem_lambda_source_old y).2 hyFinite
      exact PopularAuxiliary.Input.no_avoiding_source_target_path
        L.lambda C hC q hqSource hqTarget hqAvoid
    have hyNotLeft : y ∉ L.offLadder ∪ L.finiteSource := by
      exact fun h ↦ h.elim hyNotOff hyNotFinite
    have hyNotTarget :
        (PopularAuxiliary.Input.LambdaVertex.old y : LV L) ∉
          L.lambda.target := by
      intro hyTarget
      exact hyMarker ((L.mem_lambda_target_old y).1 hyTarget)
    have hstartNeFinish : q.start ≠ q.finish := by
      intro hEq
      have hOldFinish :
          (PopularAuxiliary.Input.LambdaVertex.old y : LV L) = q.finish :=
        hqStart.symm.trans hEq
      exact hyNotTarget (hOldFinish.symm ▸ hqTarget)
    obtain ⟨a, ha, tail, hwalk⟩ :=
      RelationalRoof.exists_cons_of_start_ne_finish
        L.lambda.graph.Adj q.walk hstartNeFinish
    have hya : L.lambda.graph.Adj (.old y) a := by
      simpa only [hqStart] using ha
    have htailPath : tail.IsPath := by
      have hconsPath : (Walk.cons ha tail).IsPath := hwalk ▸ q.isPath
      rw [Walk.isPath_iff] at hconsPath ⊢
      exact hconsPath.tail
    let rtail : FinitePath L.lambda.graph :=
      { start := a
        finish := q.finish
        walk := tail
        isPath := htailPath }
    have hrouteAvoid : L.lambda.Avoids rtail C := by
      change Disjoint rtail.support C
      rw [Set.disjoint_left]
      intro z hztail hzC
      apply Set.disjoint_left.1 hqAvoid _ hzC
      change z ∈ q.walk.support
      rw [hwalk]
      exact List.mem_cons_of_mem _ hztail
    cases a with
    | old z =>
        have hyLeft : y ∈ L.offLadder ∪ L.finiteSource :=
          (L.lambda_adj_old_old y z).1 hya |>.1
        exact False.elim (hyNotLeft hyLeft)
    | edge u z =>
        have haz := (L.lambda_adj_old_edge y u z).1 hya
        have hyz : y = z := haz.2.resolve_right (fun h ↦ hyNotLeft h.1)
        let r : FinitePath L.lambda.graph :=
          { start := .edge u z
            finish := q.finish
            walk := tail
            isPath := htailPath }
        refine ⟨{
          route := r
          start_eq := Or.inr ?_
          target := hqTarget
          avoids := ?_
          old_not_mem := hxNotC }⟩
        · change (u, z) ∈ L.familyEdges ∧ Gamma.graph.Adj x z
          exact ⟨haz.1, hyz ▸ hxy⟩
        · exact hrouteAvoid
    | proxy i =>
        exact False.elim (L.lambda_not_adj_to_proxy (.old y) i hya)

/-! ## Re-entering the finite last-contact descent -/

/-- Every vertex of an ambient path avoiding `BB` has its old auxiliary
copy outside `C`. -/
theorem old_not_mem_cut_of_ambient_avoids
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB L C))
    (i : Fin R.walk.support.length) :
    (PopularAuxiliary.Input.LambdaVertex.old R.walk.support[i] : LV L) ∉ C := by
  intro hiC
  have hiBB : R.walk.support[i] ∈ GroundingCut.BB L C :=
    GroundingCut.CV_subset_BB L C (by simpa only [GroundingCut.mem_CV])
  exact Set.disjoint_left.1 havoid (List.getElem_mem i.2) hiBB

/-- Compile the open interval between two contacts of the ambient finite
path.  Every strict interior vertex is off the ladder, while the right
endpoint is either retained on the right or lies on the ladder.  The result
is a relaxed escape at the left contact.

The recursion is on the numerical length of the interval.  At an interior
vertex the recursively obtained relaxed route becomes ordinary by
`exists_ordinaryEscape_of_relaxed_of_start_mem`; the preceding original
edge is then compiled by `relaxedEscape_of_adjacent_ordinary`. -/
theorem relaxedEscape_of_offLadder_interval
    (L : Input Gamma I) (C : Set (LV L))
    (hC : Popular.IsSeparator L.lambda C)
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB L C))
    (j i : Fin R.walk.support.length) (hji : j.1 < i.1)
    (hInterior : ∀ k : Fin R.walk.support.length,
      j.1 < k.1 → k.1 < i.1 → R.walk.support[k] ∈ L.offLadder)
    (hiBoundary :
      R.walk.support[i] ∈ L.offLadder ∪ L.targetMarkers ∨
        R.walk.support[i] ∈ Gamma.vertexSet L.ladder.paths)
    (q : FinitePath L.lambda.graph)
    (hqStart : q.start = .old R.walk.support[i])
    (hqTarget : q.finish ∈ L.lambda.target)
    (hqAvoid : L.lambda.Avoids q C) :
    Nonempty
      (GroundingRelaxedEscape.RelaxedEscape L C R.walk.support[j]) := by
  let k : Fin R.walk.support.length := ⟨j.1 + 1, by omega⟩
  have hjk : j.1 < k.1 := by simp only [k]; omega
  have hAdj : Gamma.graph.Adj R.walk.support[j] R.walk.support[k] := by
    simpa [k] using walk_adj_getElem_succ R.walk j.1 (by omega)
  by_cases hki : k.1 = i.1
  · have hkiFin : k = i := Fin.ext hki
    exact relaxedEscape_of_adjacent_ordinary L C hC
      (by simpa only [hkiFin] using hAdj)
      (old_not_mem_cut_of_ambient_avoids L C R havoid j)
      hiBoundary q hqStart hqTarget hqAvoid
  · have hkiLt : k.1 < i.1 := by
      dsimp only [k] at hki ⊢
      omega
    have hkOff : R.walk.support[k] ∈ L.offLadder :=
      hInterior k hjk hkiLt
    have hInterior' : ∀ l : Fin R.walk.support.length,
        k.1 < l.1 → l.1 < i.1 →
          R.walk.support[l] ∈ L.offLadder := by
      intro l hkl hli
      exact hInterior l (hjk.trans hkl) hli
    obtain ⟨Ek⟩ := relaxedEscape_of_offLadder_interval
      L C hC R havoid k i hkiLt hInterior' hiBoundary
        q hqStart hqTarget hqAvoid
    obtain ⟨qk, hqkStart, hqkTarget, hqkAvoid⟩ :=
      exists_ordinaryEscape_of_relaxed_of_start_mem
        L C (Or.inl hkOff) Ek
    exact relaxedEscape_of_adjacent_ordinary L C hC hAdj
      (old_not_mem_cut_of_ambient_avoids L C R havoid j)
      (Or.inl (Or.inl hkOff)) qk hqkStart hqkTarget hqkAvoid
termination_by i.1 - j.1
decreasing_by omega

/-- A strict backwards traversal in a retained fragment turns a relaxed
escape at its earlier fragment point into the ordinary suffix required by
an `EscapeSuffixState`.  The ambient `BB`-avoidance supplies endpoint
avoidance, and the relaxed escape itself proves that the fragment meets
`RR`.

This is the state-construction half of one recursive last-fragment step;
the other half is the finite choice of the earlier position and fragment. -/
theorem exists_strictlyEarlier_escapeSuffixState
    (L : Input Gamma I) (C : Set (LV L))
    (R : FinitePath Gamma.graph)
    (havoid : Gamma.Avoids R (GroundingCut.BB L C))
    (S : GroundingFiniteDescent.EscapeSuffixState L C R)
    (j : Fin R.walk.support.length) (hji : j.1 < S.position.1)
    (Q : L.Fragment) (hQ : Q ∈ GroundingCut.G0 L C)
    {b : V} (hbQ : b ∈ Q.path.support)
    (hbBefore : GroundingCut.Before Q.path b R.walk.support[j])
    (E : GroundingRelaxedEscape.RelaxedEscape L C b) :
    ∃ T : GroundingFiniteDescent.EscapeSuffixState L C R,
      T.position.1 < S.position.1 := by
  have hQescape :
      PopularAuxiliary.Input.Fragment.MeetsEscape L C Q :=
    ⟨b, hbQ, ⟨E⟩⟩
  have hjQ : R.walk.support[j] ∈ Q.path.support := by
    rcases hbBefore.1 with ⟨_m, _n, _hmb, hnj, _hmn⟩
    exact GroundingCut.occursAt_mem_support hnj
  obtain ⟨q, hqStart, hqTarget, hqAvoid⟩ :=
    GroundingRelaxedEscape.exists_avoiding_reverse_to_relaxedEscape
      L C Q hQ.1 hbBefore
        (old_not_mem_cut_of_ambient_avoids L C R havoid j) E
  let T : GroundingFiniteDescent.EscapeSuffixState L C R :=
    { position := j
      fragment := Q
      fragment_mem := hQ
      fragment_escape := hQescape
      contact_mem := hjQ
      suffix := q
      suffix_start := hqStart
      suffix_target := hqTarget
      suffix_avoids := hqAvoid }
  exact ⟨T, hji⟩

end GroundingRelaxedCorridor
end Erdos599
