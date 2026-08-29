/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.DeferredGroundingSelectedAssembly

/-!
# Reduced presentations of the selected grounding routes

This file isolates the lossless finite-list construction needed by the
separator arm of Section 8.  A continuous signed trace whose traversed
vertex list is nonempty and duplicate-free gives an exact
`CutReducedRunPresentation`: maximal-run compression neither creates nor
deletes any decoded edge.

The final section states the corresponding family constructor for the
canonical deferred collision controls.  Its only geometric input is the
literal vertex-simplicity of every selected decoded trace.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

namespace Alternating
namespace RunCompressor

/-- Every raw edge position belongs to a unique maximal colour run. -/
theorem exists_run_offset_of_lt_flatten_length
    (runs : List (List Direction)) {n : Nat}
    (hn : n < runs.flatten.length) :
    ∃ (i : Fin runs.length) (k : Nat), k < (runs.get i).length ∧
      n = runLower runs i + k := by
  induction runs generalizing n with
  | nil => simp at hn
  | cons r runs ih =>
      by_cases hnr : n < r.length
      · exact ⟨⟨0, by simp⟩, n, by simpa using hnr, by simp [runLower]⟩
      · have hnTail : n - r.length < runs.flatten.length := by
          have hlen : n < r.length + runs.flatten.length := by
            simpa only [List.flatten_cons, List.length_append] using hn
          omega
        obtain ⟨i, k, hk, hnk⟩ := ih hnTail
        refine ⟨⟨i.1 + 1, by simp⟩, k, by simpa using hk, ?_⟩
        simp only [runLower, List.take_succ_cons, List.map_cons,
          List.sum_cons, List.get_cons_succ]
        change n = r.length + runLower runs i + k
        have hnGe : r.length ≤ n := Nat.le_of_not_gt hnr
        omega

namespace FiniteInput

open Set

universe u
variable {V : Type u} {D : Digraph V}

/-- The maximal-run definition of `orientedEdgeSet` is exactly the union
of the direction-oriented raw successor pairs. -/
theorem orientedEdgeSet_eq_indexed (S : FiniteInput D) :
    S.orientedEdgeSet =
      {e | ∃ n : Fin S.lastEdge,
        e = if S.colour n = .forward then
          (S.vertex n, S.vertex (n + 1))
        else (S.vertex (n + 1), S.vertex n)} := by
  ext e
  constructor
  · intro he
    simp only [orientedEdgeSet, Set.mem_iUnion] at he
    obtain ⟨i, he⟩ := he
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd] at he
      obtain ⟨k, hk, rfl⟩ := he
      let n : Fin S.lastEdge := ⟨runLower S.runs i + k, by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge i)⟩
      refine ⟨n, ?_⟩
      have hc : S.colour n = .forward :=
        (S.colour_run_offset i hk).trans hd
      simp [hc, n]
    · rw [if_neg hd] at he
      obtain ⟨k, hk, rfl⟩ := he
      let n : Fin S.lastEdge := ⟨runLower S.runs i + k, by
        exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
          (S.runUpper_le_lastEdge i)⟩
      refine ⟨n, ?_⟩
      have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      have hc : S.colour n = .backward :=
        (S.colour_run_offset i hk).trans hb
      simp [hc, n]
  · rintro ⟨n, rfl⟩
    have hn : n.1 < S.runs.flatten.length := by
      rw [S.runs_flatten, S.colours_length]
      exact n.2
    obtain ⟨i, k, hk, hnk⟩ :=
      exists_run_offset_of_lt_flatten_length S.runs hn
    simp only [orientedEdgeSet, Set.mem_iUnion]
    refine ⟨i, ?_⟩
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd]
      refine ⟨k, hk, ?_⟩
      have hc : S.colour n = .forward := by
        have hc' := S.colour_run_offset i hk
        simpa only [hnk] using hc'.trans hd
      rw [if_pos hc]
      simp only [hnk]
    · rw [if_neg hd]
      refine ⟨k, hk, ?_⟩
      have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      have hc : S.colour n = .backward := by
        have hc' := S.colour_run_offset i hk
        simpa only [hnk] using hc'.trans hb
      rw [if_neg (by simpa [hc])]
      simp only [hnk]

end FiniteInput
end RunCompressor
end Alternating

namespace PopularAuxiliary
namespace Input

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}
variable {L : PopularAuxiliary.Input Gamma I}

/-- Vertices visited by a continuous signed trace, including its initial
vertex. -/
def traceVertices (x : V) (q : List (SignedEdge V)) : List V :=
  x :: q.map SignedEdge.exit

@[simp]
theorem traceVertices_length (x : V) (q : List (SignedEdge V)) :
    (traceVertices x q).length = q.length + 1 := by
  simp [traceVertices]

theorem RunsFromTo.traceVertices_get_entry_exit
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) (n : Nat) (hn : n < q.length) :
    (traceVertices x q)[n]'(by simp [traceVertices]; omega) =
        (q[n]'hn).entry ∧
      (traceVertices x q)[n + 1]'(by simp [traceVertices]; omega) =
        (q[n]'hn).exit := by
  induction h generalizing n with
  | nil => simp at hn
  | @cons s z r tail ih =>
      cases n with
      | zero => simp [traceVertices]
      | succ n =>
          have hn' : n < r.length := by simpa using hn
          have hi := ih n hn'
          simpa [traceVertices, Nat.succ_eq_add_one, Nat.add_assoc] using hi

theorem RunsFromTo.traceVertices_get_last
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) :
    (traceVertices x q)[q.length]'(by simp [traceVertices]) = y := by
  induction h with
  | nil => simp [traceVertices]
  | @cons s z r tail ih =>
      change (s.entry :: s.exit :: r.map SignedEdge.exit)[r.length + 1] = z
      rw [List.getElem_cons_succ]
      simpa [traceVertices] using ih

def traceVertex (x y : V) (q : List (SignedEdge V)) (n : Nat) : V :=
  (traceVertices x q).getD n y

theorem traceVertex_eq_getElem {x y : V} {q : List (SignedEdge V)}
    {n : Nat} (hn : n < (traceVertices x q).length) :
    traceVertex x y q n = (traceVertices x q)[n] := by
  exact List.getD_eq_getElem _ _ hn

/-- A Lambda walk whose signed expansion is empty cannot move.  Equality
joins do not create signed edges, but every such join is incident with an
edge gadget, and that gadget itself contributes its backward edge. -/
theorem decodeWalkSteps_eq_nil_imp_start_eq_finish
    {a b : L.LV} (q : Walk L.lambda.graph a b)
    (hzero : L.decodeWalkSteps q = []) : a = b := by
  induction q with
  | nil => rfl
  | @cons a c b hac q ih =>
      simp only [decodeWalkSteps_cons] at hzero
      have hparts := List.append_eq_nil.mp hzero
      have hleft := List.append_eq_nil.mp hparts.1
      have hga : L.gadgetSteps a = [] := hleft.1
      have hconnector : L.connectorSteps a c = [] := hleft.2
      have htail : L.decodeWalkSteps q = [] := hparts.2
      have hcb : c = b := ih htail
      have hgc : L.gadgetSteps c = [] := by
        subst b
        cases q with
        | nil => simpa only [decodeWalkSteps_nil] using htail
        | @cons c d e hcd r =>
            simp only [decodeWalkSteps_cons] at htail
            exact (List.append_eq_nil.mp
              (List.append_eq_nil.mp htail).1).1
      have hnone : L.chosenConnector? a c = none := by
        cases hc : L.chosenConnector? a c with
        | none => rfl
        | some e =>
            simp [connectorSteps, hc] at hconnector
      have hjoin : L.BackwardJoin a c :=
        L.chosenConnector?_eq_none_of_adj hac hnone
      exfalso
      cases a <;> cases c <;>
        simp [gadgetSteps, BackwardJoin] at hga hgc hjoin

/-- A positive vertex-simple signed trace is an admissible input to the
finite maximal-run compressor. -/
noncomputable def CutMicroTrace.reducedFiniteInput
    {p : FinitePath L.lambda.graph} (T : L.CutMicroTrace p)
    (hpos : T.steps ≠ [])
    (hnodup : (traceVertices T.initial T.steps).Nodup) :
    Alternating.RunCompressor.FiniteInput Gamma.graph where
  lastEdge := T.steps.length
  lastEdge_pos := List.length_pos_iff_ne_nil.mpr hpos
  vertex := traceVertex T.initial T.terminal T.steps
  vertex_injective_on := by
    intro i j hi hj hij
    have hil : i < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
      omega
    have hjl : j < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
      omega
    rw [traceVertex_eq_getElem hil, traceVertex_eq_getElem hjl] at hij
    let i' : Fin (traceVertices T.initial T.steps).length := ⟨i, hil⟩
    let j' : Fin (traceVertices T.initial T.steps).length := ⟨j, hjl⟩
    have hij' : (traceVertices T.initial T.steps).get i' =
        (traceVertices T.initial T.steps).get j' := hij
    exact congrArg Fin.val ((List.Nodup.get_inj_iff hnodup).mp hij')
  colour := fun n => (T.steps.get n).direction
  forward_adj := by
    intro n hn
    have hstep := T.runs.traceVertices_get_entry_exit n n.2
    have hv := T.valid (T.steps.get n) (List.get_mem T.steps n)
    have hnv : n.1 < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
    have hsnv : n.1 + 1 < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
    rw [traceVertex_eq_getElem hnv, traceVertex_eq_getElem hsnv,
      hstep.1, hstep.2]
    change Gamma.graph.Adj (T.steps[n]).entry (T.steps[n]).exit
    change (T.steps[n]).direction = .forward at hn
    change SignedEdge.Valid (Gamma := Gamma) (T.steps[n]) at hv
    rcases hsn : T.steps[n] with ⟨e, d⟩
    cases d <;> simp [hsn, SignedEdge.entry, SignedEdge.exit,
      SignedEdge.Valid] at hn hv ⊢
    exact hv
  backward_adj := by
    intro n hn
    have hstep := T.runs.traceVertices_get_entry_exit n n.2
    have hv := T.valid (T.steps.get n) (List.get_mem T.steps n)
    have hnv : n.1 < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
    have hsnv : n.1 + 1 < (traceVertices T.initial T.steps).length := by
      simp [traceVertices]
    rw [traceVertex_eq_getElem hsnv, traceVertex_eq_getElem hnv,
      hstep.2, hstep.1]
    change Gamma.graph.Adj (T.steps[n]).exit (T.steps[n]).entry
    change (T.steps[n]).direction = .backward at hn
    change SignedEdge.Valid (Gamma := Gamma) (T.steps[n]) at hv
    rcases hsn : T.steps[n] with ⟨e, d⟩
    cases d <;> simp [hsn, SignedEdge.entry, SignedEdge.exit,
      SignedEdge.Valid] at hn hv ⊢
    exact hv

/-- Exact reduced-run presentation of a positive vertex-simple cut trace. -/
noncomputable def CutMicroTrace.reducedRunPresentation
    {p : FinitePath L.lambda.graph} (T : L.CutMicroTrace p)
    (hpos : T.steps ≠ [])
    (hnodup : (traceVertices T.initial T.steps).Nodup) :
    L.CutReducedRunPresentation T where
  input := T.reducedFiniteInput hpos hnodup
  initial_eq := by
    change traceVertex T.initial T.terminal T.steps 0 = T.initial
    rw [traceVertex_eq_getElem (by simp [traceVertices])]
    simp [traceVertices]
  terminal_eq := by
    change traceVertex T.initial T.terminal T.steps T.steps.length = T.terminal
    rw [traceVertex_eq_getElem (by simp [traceVertices])]
    exact T.runs.traceVertices_get_last
  rawEdgeSet_eq := by
    rw [Alternating.RunCompressor.FiniteInput.orientedEdgeSet_eq_indexed]
    ext e
    constructor
    · rintro ⟨n, rfl⟩
      have hstep := T.runs.traceVertices_get_entry_exit n n.2
      have hn0 : n.1 < (traceVertices T.initial T.steps).length := by
        simp [traceVertices]
      have hn1 : n.1 + 1 < (traceVertices T.initial T.steps).length := by
        simp [traceVertices]
      change (if (T.steps.get n).direction = .forward then
          (traceVertex T.initial T.terminal T.steps n,
            traceVertex T.initial T.terminal T.steps (n + 1))
        else
          (traceVertex T.initial T.terminal T.steps (n + 1),
            traceVertex T.initial T.terminal T.steps n)) ∈
        signedEdgeSet T.steps
      rw [traceVertex_eq_getElem hn0, traceVertex_eq_getElem hn1,
        hstep.1, hstep.2]
      refine ⟨T.steps.get n, List.get_mem T.steps n, ?_⟩
      rcases hs : T.steps.get n with ⟨f, d⟩
      cases d <;> simp [hs, SignedEdge.entry, SignedEdge.exit]
    · rintro ⟨s, hs, rfl⟩
      obtain ⟨n, hn⟩ := List.get_of_mem hs
      refine ⟨n, ?_⟩
      have hstep := T.runs.traceVertices_get_entry_exit n n.2
      have hn0 : n.1 < (traceVertices T.initial T.steps).length := by
        simp [traceVertices]
      have hn1 : n.1 + 1 < (traceVertices T.initial T.steps).length := by
        simp [traceVertices]
      change s.edge = if (T.steps.get n).direction = .forward then
          (traceVertex T.initial T.terminal T.steps n,
            traceVertex T.initial T.terminal T.steps (n + 1))
        else
          (traceVertex T.initial T.terminal T.steps (n + 1),
            traceVertex T.initial T.terminal T.steps n)
      rw [traceVertex_eq_getElem hn0, traceVertex_eq_getElem hn1,
        hstep.1, hstep.2, hn]
      rcases s with ⟨f, d⟩
      cases d <;> simp [SignedEdge.entry, SignedEdge.exit]

end Input
end PopularAuxiliary

namespace DWeb
namespace KappaLadder
namespace Deferred

open _root_.Erdos599.DirectedPath
open _root_.Erdos599.PopularGroundingBridge

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

private abbrev AuxInput
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :=
  popularAuxiliaryInput L hL.legal

private abbrev AuxIndexed
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L) :=
  popularAuxiliaryIndexed L hL

private abbrev CanonicalControls
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL)) :=
  selectionControls L hL S

private abbrev AuxRequest
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL)) :=
  Request (AuxInput L hL) S.cut

/-- Every canonical selected request path has at least one decoded signed
edge.  Its Lambda start lies in the source, whereas its request endpoint
does not; an empty decoding would force those two auxiliary vertices to be
equal. -/
theorem canonicalSelectedCutMicroTrace_steps_ne_nil
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (r : AuxRequest L hL S) :
    (GroundingSelectedDecoder.selectedCutMicroTrace S
      (CanonicalControls L hL S) r).steps ≠ [] := by
  intro hzero
  let K := CanonicalControls L hL S
  let p := GroundingAssembly.selectedPath (AuxIndexed L hL) S K r
  have hdecode : (AuxInput L hL).decodeWalkSteps p.walk = [] := by
    simpa only [p, K, GroundingSelectedDecoder.selectedCutMicroTrace_steps]
      using hzero
  have hstartFinish : p.start = p.finish :=
    PopularAuxiliary.Input.decodeWalkSteps_eq_nil_imp_start_eq_finish
      p.walk hdecode
  have hstart : p.start ∈ (AuxInput L hL).lambda.source :=
    (GroundingAssembly.selectedWarp (AuxIndexed L hL) S K).starts_in_source
      ⟨r, rfl⟩
  have hfinish : p.finish = requestAuxVertex r := by
    exact GroundingAssembly.selectedPath_finish (AuxIndexed L hL) S K r
  exact requestAuxVertex_not_mem_source r
    (hfinish ▸ hstartFinish ▸ hstart)

/-- The exact geometric reducedness statement needed for the canonical
selected family. -/
def CanonicalSelectedTracesVertexSimple
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL)) : Prop :=
  ∀ r : AuxRequest L hL S,
    let T := GroundingSelectedDecoder.selectedCutMicroTrace S
      (CanonicalControls L hL S) r
    T.steps ≠ [] ∧
      (PopularAuxiliary.Input.traceVertices T.initial T.steps).Nodup

/-- Vertex-simplicity of the canonical selected traces gives the entire
selected reduced-run family with exact raw edge sets. -/
noncomputable def selectedReducedRunFamily_of_vertexSimple
    (L : Gamma.KappaLadder kappa) (hL : IsKappaHindrance L)
    (S : Popular.PopularSeparator (AuxIndexed L hL))
    (H : CanonicalSelectedTracesVertexSimple L hL S) :
    SelectedReducedRunFamily L hL S (CanonicalControls L hL S) where
  presentation := fun r ↦
    let T := GroundingSelectedDecoder.selectedCutMicroTrace S
      (CanonicalControls L hL S) r
    T.reducedRunPresentation (H r).1 (H r).2

end Deferred
end KappaLadder
end DWeb
end Erdos599
