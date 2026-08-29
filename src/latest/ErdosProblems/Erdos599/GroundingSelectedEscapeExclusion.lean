/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingSelectedBackwardOrder
import ErdosProblems.Erdos599.LambdaRawPortIncidence

/-!
# Selected departures cannot start relaxed escapes

An edge gadget absorbs either kind of relaxed first step. An old forward
departure does the same when it belongs to the forward-source domain.
Proper selected prefixes avoid the cut, so either escape would contradict
auxiliary separation. These are statements about the original selected
paths, without chronological erasure or a switched-relation assumption.
-/

noncomputable section

namespace Erdos599.GroundingSelectedEscapeExclusion

open Set DirectedPath PopularAuxiliary.Input PopularGroundingBridge GroundingSimultaneousDecode

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

private theorem prepend_avoiding {C : Set L.LV} {a : L.LV}
    (q : FinitePath L.lambda.graph) (ha : L.lambda.graph.Adj a q.start)
    (haC : a ∉ C) (hfinish : q.finish ∈ L.lambda.target)
    (havoid : L.lambda.Avoids q C) : L.lambda.CanReachTargetAvoiding C a := by
  let w : Walk L.lambda.graph a q.finish := .cons ha q.walk
  obtain ⟨s, hs⟩ := RelationalRoof.exists_pathTo_support_subset
    (R := L.lambda.graph.Adj) w
  let p : FinitePath L.lambda.graph := ⟨a, q.finish, s.1, s.2⟩
  refine ⟨p, ⟨rfl, hfinish⟩, ?_⟩
  apply Set.disjoint_left.2
  intro z hz hzC
  have hzw := hs hz
  change z ∈ a :: q.walk.support at hzw
  rcases List.mem_cons.mp hzw with rfl | hzq
  · exact haC hzC
  · exact Set.disjoint_left.1 havoid hzq hzC

/-- A represented edge tail can realize either kind of relaxed escape. -/
theorem canReach_from_edge_of_relaxedEscape {C : Set L.LV} {x y : V}
    (hxy : (x, y) ∈ L.familyEdges) (hnot : LambdaVertex.edge x y ∉ C)
    (E : L.RelaxedEscape C x) :
    L.lambda.CanReachTargetAvoiding C (.edge x y) := by
  apply prepend_avoiding L E.route _ hnot E.target E.avoids
  rcases E.start_eq with hstart | hstep
  · rw [hstart]
    exact (L.lambda_adj_edge_old x y x).2 ⟨hxy, Or.inl rfl⟩
  · exact GroundingCutDecoder.lambda_adj_edge_of_relaxedForwardStep L hxy hstep

/-- Ordinary-forward source vertices also realize relaxed escapes. -/
theorem canReach_from_old_of_relaxedEscape {C : Set L.LV} {x : V}
    (hx : x ∈ L.offLadder ∪ L.finiteSource) (E : L.RelaxedEscape C x) :
    L.lambda.CanReachTargetAvoiding C (.old x) := by
  rcases E.start_eq with hstart | hstep
  · exact ⟨E.route, ⟨hstart, E.target⟩, E.avoids⟩
  · apply prepend_avoiding L E.route _ E.old_not_mem E.target E.avoids
    cases ha : E.route.start with
    | old y =>
        have h : y ∈ L.offLadder ∪ L.targetMarkers ∧ Gamma.graph.Adj x y :=
          by simpa only [ha, RelaxedForwardStep] using hstep
        exact (L.lambda_adj_old_old x y).2 ⟨hx, h⟩
    | edge z y =>
        have h : (z, y) ∈ L.familyEdges ∧ Gamma.graph.Adj x y :=
          by simpa only [ha, RelaxedForwardStep] using hstep
        exact (L.lambda_adj_old_edge x z y).2 ⟨h.1, Or.inr ⟨hx, h.2⟩⟩
    | proxy i => simp only [ha, RelaxedForwardStep] at hstep

/-- A proper original connector leaving an old gadget has the ordinary
forward-source membership needed above. -/
theorem forwardSource_of_old_connector {b : L.LV} {x y : V}
    (hadj : L.lambda.graph.Adj (.old x) b)
    (hc : L.ForwardConnector (.old x) b x y) (hne : x ≠ y) :
    x ∈ L.offLadder ∪ L.finiteSource := by
  cases b with
  | old z => exact ((L.lambda_adj_old_old x z).1 hadj).1
  | edge z w =>
      have hwy : w = y := Option.some.inj hc.2.1
      have h := ((L.lambda_adj_old_edge x z w).1 hadj).2
      exact (h.resolve_left (fun hxw ↦ hne (hxw.trans hwy))).1
  | proxy i => exact (L.lambda_not_adj_to_proxy (.old x) i hadj).elim

variable {L} {kappa : Cardinal.{u}} (U : Popular.KappaIndexed L.lambda kappa)
variable (S : Popular.PopularSeparator U) (K : GroundingSelection.Controls S)

/-- No nonfinal gadget of an actual selected path has a cut-avoiding
auxiliary continuation to a target. -/
theorem offApex_not_canReachTargetAvoiding (r : Request L S.cut) {a : L.LV}
    (ha : a ∈ (strongSelectedPath U S K r).support) (hne : a ≠ requestAuxVertex r) :
    ¬ L.lambda.CanReachTargetAvoiding S.cut a := by
  let p := strongSelectedPath U S K r
  let F := GroundingAssembly.normalizedRequestFan S K r
  have hp : p ∈ F.paths := (strongSelectedPath_mem_controlledRequestFan U S K r).1
  let hm : p.walk.Meets ({a} : Set L.LV) := ⟨a, ha, Set.mem_singleton _⟩
  let q := p.firstHit {a} hm
  have hjoin : Disjoint q.support {requestAuxVertex r} :=
    PopularSwitching.firstHit_support_disjoint_join F (by simpa using hne) hp hm
  have havoid : L.lambda.Avoids q S.cut := by
    apply Set.disjoint_left.2
    intro z hz hzC
    have hzJoin := GroundingAssembly.normalizedRequestFan_cut_normalized S K r hp
      ⟨p.firstHit_support_subset {a} hm hz, hzC⟩
    exact Set.disjoint_left.1 hjoin hz hzJoin
  intro hreach
  have hqa : q.finish = a := Set.mem_singleton_iff.mp (p.firstHit_finish_mem {a} hm)
  exact L.not_canReachTargetAvoiding_of_source S.cut S.separates (F.starts_in_source hp)
    (GroundingCut.canReachTargetAvoiding_of_avoiding_path L S.cut q rfl hqa havoid hreach)

theorem edgeTail_not_mem_escapeRegion (r : Request L S.cut) {x y : V}
    (hxy : (x, y) ∈ L.familyEdges)
    (ha : LambdaVertex.edge x y ∈ (strongSelectedPath U S K r).support)
    (hne : LambdaVertex.edge x y ≠ requestAuxVertex r) : x ∉ L.escapeRegion S.cut := by
  rintro ⟨E⟩
  apply offApex_not_canReachTargetAvoiding U S K r ha hne
  apply canReach_from_edge_of_relaxedEscape L hxy _ E
  intro hcut
  exact hne (Set.mem_singleton_iff.mp
    (GroundingAssembly.normalizedRequestFan_cut_normalized S K r
      (strongSelectedPath_mem_controlledRequestFan U S K r).1 ⟨ha, hcut⟩))

theorem oldForward_not_mem_escapeRegion (r : Request L S.cut) {x : V}
    (hx : x ∈ L.offLadder ∪ L.finiteSource)
    (ha : LambdaVertex.old x ∈ (strongSelectedPath U S K r).support)
    (hne : LambdaVertex.old x ≠ requestAuxVertex r) : x ∉ L.escapeRegion S.cut := by
  rintro ⟨E⟩
  exact offApex_not_canReachTargetAvoiding U S K r ha hne
    (canReach_from_old_of_relaxedEscape L hx E)

#print axioms offApex_not_canReachTargetAvoiding
#print axioms edgeTail_not_mem_escapeRegion
#print axioms oldForward_not_mem_escapeRegion

end Erdos599.GroundingSelectedEscapeExclusion
