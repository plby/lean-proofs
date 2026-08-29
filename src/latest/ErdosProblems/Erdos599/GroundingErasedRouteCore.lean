/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingDecodedCarrier
import ErdosProblems.Erdos599.LambdaCompressionBridge

/-!
# Loop-erased decoding for the Section 8 grounding routes

A simple path in the auxiliary web can project to a signed original-web
walk with repeated old vertices.  Consequently its raw decoded edge set
need not itself be switchable.  This file performs the shortcutting which
is explicit in Assertion 8.22: it deletes closed intervals of the signed
walk, retains the endpoints, and produces a projected-simple signed
subroute.  Maximal constant-direction compression then gives an honest
alternating path whose edge set is a subset, not necessarily all, of the
raw decoded edge set.
-/

noncomputable section

namespace Erdos599
namespace PopularAuxiliary.Input

open Set DirectedPath Alternating

universe u

variable {V I : Type u} {Gamma : DWeb V}
variable (L : PopularAuxiliary.Input Gamma I)

theorem SignedEdge.entry_eq_fst_of_direction_forward (s : SignedEdge V)
    (h : s.direction = .forward) : s.entry = s.edge.1 := by
  cases s with
  | mk edge direction =>
      cases direction <;> simp_all [SignedEdge.entry]

theorem SignedEdge.exit_eq_snd_of_direction_forward (s : SignedEdge V)
    (h : s.direction = .forward) : s.exit = s.edge.2 := by
  cases s with
  | mk edge direction =>
      cases direction <;> simp_all [SignedEdge.exit]

theorem SignedEdge.exit_eq_fst_of_direction_backward (s : SignedEdge V)
    (h : s.direction = .backward) : s.exit = s.edge.1 := by
  cases s with
  | mk edge direction =>
      cases direction <;> simp_all [SignedEdge.exit]

theorem SignedEdge.entry_eq_snd_of_direction_backward (s : SignedEdge V)
    (h : s.direction = .backward) : s.entry = s.edge.2 := by
  cases s with
  | mk edge direction =>
      cases direction <;> simp_all [SignedEdge.entry]

/-! ## Suffixes and chronological loop erasure of signed walks -/

/-- The projected vertices of a traversable signed list. -/
def signedVertexChain (x : V) (q : List (SignedEdge V)) : List V :=
  x :: q.map SignedEdge.exit

@[simp] theorem signedVertexChain_nil (x : V) :
    signedVertexChain x [] = [x] := rfl

@[simp] theorem signedVertexChain_cons (s : SignedEdge V)
    (q : List (SignedEdge V)) :
    signedVertexChain s.entry (s :: q) =
      s.entry :: signedVertexChain s.exit q :=
  rfl

theorem RunsFromTo.signedVertexChain_getLast
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) :
    (signedVertexChain x q).getLast (by simp [signedVertexChain]) = y := by
  induction h with
  | nil => simp [signedVertexChain]
  | cons s tail ih => simpa [signedVertexChain] using ih

/-- Every signed step occurs between the corresponding consecutive
vertices of the traversed vertex chain. -/
theorem RunsFromTo.signedVertexChain_get_entry_exit
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) (n : Nat) (hn : n < q.length) :
    (signedVertexChain x q)[n]'(by simp [signedVertexChain]; omega) =
        (q[n]'hn).entry ∧
      (signedVertexChain x q)[n + 1]'(by
        simp [signedVertexChain]
        omega) = (q[n]'hn).exit := by
  induction h generalizing n with
  | nil => simp at hn
  | @cons s z r tail ih =>
      cases n with
      | zero => simp [signedVertexChain]
      | succ n =>
          have hn' : n < r.length := by simpa using hn
          have hi := ih n hn'
          simpa [signedVertexChain, Nat.succ_eq_add_one,
            Nat.add_assoc] using hi

/-! ## Recovering the maximal run containing a raw edge index -/

/-- Every index of a flattened nonempty-run list has a unique presentation
as an offset in one of its constituent runs.  Only existence is needed by
the edge-accounting proof below. -/
private theorem exists_run_offset_of_lt_flatten_length
    (runs : List (List Alternating.Direction)) {n : ℕ}
    (hn : n < runs.flatten.length) :
    ∃ (i : Fin runs.length) (k : ℕ),
      k < (runs.get i).length ∧
        n = Alternating.RunCompressor.runLower runs i + k := by
  induction runs generalizing n with
  | nil => simp at hn
  | cons r runs ih =>
      simp only [List.flatten_cons, List.length_append] at hn
      by_cases hnr : n < r.length
      · refine ⟨⟨0, by simp⟩, n, by simpa, ?_⟩
        simp [Alternating.RunCompressor.runLower]
      · have htail : n - r.length < runs.flatten.length := by omega
        obtain ⟨i, k, hk, hnk⟩ := ih htail
        refine ⟨⟨i.1 + 1, by simp⟩, k, by simpa, ?_⟩
        have hnSplit : n = r.length + (n - r.length) := by omega
        rw [hnSplit, hnk]
        simp [Alternating.RunCompressor.runLower, Nat.add_assoc]

/-- A suffix of a traversable signed walk beginning at any visited vertex.
The final clause retains the ordered suffix relation between vertex chains,
which transfers simplicity. -/
theorem RunsFromTo.exists_suffix_from_mem
    {x y z : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) (hz : z ∈ signedVertexChain x q) :
    ∃ r : List (SignedEdge V),
      r <:+ q ∧ RunsFromTo z y r ∧
        signedVertexChain z r <:+ signedVertexChain x q := by
  induction h generalizing z with
  | nil x₀ =>
      have hzx : z = x₀ := by simpa [signedVertexChain] using hz
      subst z
      exact ⟨[], List.suffix_rfl, .nil x₀, List.suffix_rfl⟩
  | @cons s y q tail ih =>
      by_cases hzx : z = s.entry
      · subst z
        exact ⟨s :: q, List.suffix_rfl, .cons s tail, List.suffix_rfl⟩
      · have hzTail : z ∈ signedVertexChain s.exit q := by
          simpa [signedVertexChain, hzx] using hz
        obtain ⟨r, hrq, hruns, hrchain⟩ := ih hzTail
        exact ⟨r, hrq.trans (by simpa using List.suffix_cons s q), hruns,
          hrchain.trans (by
            simpa [signedVertexChain] using
              List.suffix_cons s.entry (signedVertexChain s.exit q))⟩

/-- A loop-erased signed subroute.  It has the same ordered endpoints as the
raw trace, its signed steps form a sublist of the raw steps, and its projected
vertex chain has no repetition. -/
structure ErasedSignedRoute (x y : V) (raw : List (SignedEdge V)) where
  steps : List (SignedEdge V)
  runs : RunsFromTo x y steps
  steps_sublist : List.Sublist steps raw
  vertexChain_nodup : (signedVertexChain x steps).Nodup

/-- Every finite traversable signed walk admits endpoint-preserving
chronological loop erasure. -/
theorem RunsFromTo.exists_erasedSignedRoute
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) : Nonempty (ErasedSignedRoute x y q) := by
  induction h with
  | nil =>
      exact ⟨⟨[], .nil _, List.Sublist.refl [], by simp [signedVertexChain]⟩⟩
  | @cons s y q tail ih =>
      obtain ⟨E⟩ := ih
      by_cases hrepeat : s.entry ∈ signedVertexChain s.exit E.steps
      · obtain ⟨r, hrE, hruns, hrchain⟩ :=
          E.runs.exists_suffix_from_mem hrepeat
        exact ⟨⟨r, hruns,
          hrE.sublist.trans E.steps_sublist |>.cons s,
          hrchain.nodup E.vertexChain_nodup⟩⟩
      · exact ⟨⟨s :: E.steps, .cons s E.runs,
          E.steps_sublist.cons_cons s,
          List.nodup_cons.mpr ⟨hrepeat, E.vertexChain_nodup⟩⟩⟩

/-- The canonical loop-erased signed route. -/
noncomputable def RunsFromTo.erasedSignedRoute
    {x y : V} {q : List (SignedEdge V)}
    (h : RunsFromTo x y q) : ErasedSignedRoute x y q :=
  Classical.choice h.exists_erasedSignedRoute

namespace ErasedSignedRoute

variable {x y : V} {raw : List (SignedEdge V)}
    (E : ErasedSignedRoute x y raw)

def vertexChain : List V := signedVertexChain x E.steps

@[simp] theorem vertexChain_length :
    E.vertexChain.length = E.steps.length + 1 := by
  simp [vertexChain, signedVertexChain]

def routeVertex (n : ℕ) : V := E.vertexChain.getD n y

theorem routeVertex_eq_entry (n : Fin E.steps.length) :
    E.routeVertex n = (E.steps.get n).entry := by
  unfold routeVertex vertexChain signedVertexChain
  change (x :: E.steps.map SignedEdge.exit).getD n.1 y = _
  calc
    (x :: E.steps.map SignedEdge.exit).getD n.1 y =
        (x :: E.steps.map SignedEdge.exit).get ⟨n.1, by simp⟩ :=
      List.getD_eq_get _ _ ⟨n.1, by simp⟩
    _ = (E.steps.get n).entry :=
      (E.runs.signedVertexChain_get_entry_exit n.1 n.2).1

theorem routeVertex_succ_eq_exit (n : Fin E.steps.length) :
    E.routeVertex (n.1 + 1) = (E.steps.get n).exit := by
  unfold routeVertex vertexChain signedVertexChain
  calc
    (x :: E.steps.map SignedEdge.exit).getD (n.1 + 1) y =
        (x :: E.steps.map SignedEdge.exit).get ⟨n.1 + 1, by simp⟩ :=
      List.getD_eq_get _ _ ⟨n.1 + 1, by simp⟩
    _ = (E.steps.get n).exit := by simp

theorem routeVertex_zero : E.routeVertex 0 = x := by
  unfold routeVertex vertexChain signedVertexChain
  simp

theorem routeVertex_last : E.routeVertex E.steps.length = y := by
  unfold routeVertex
  have hlen : E.steps.length < E.vertexChain.length := by simp
  rw [List.getD_eq_get E.vertexChain y ⟨E.steps.length, hlen⟩]
  have hindex : E.steps.length = E.vertexChain.length - 1 := by
    simp
  have hne : E.vertexChain ≠ [] := by
    apply List.ne_nil_iff_length_pos.mpr
    rw [E.vertexChain_length]
    omega
  calc
    E.vertexChain.get ⟨E.steps.length, hlen⟩ =
        E.vertexChain.get ⟨E.vertexChain.length - 1, by
          have : 0 < E.vertexChain.length := by simp
          omega⟩ := by congr
    _ = E.vertexChain.getLast hne :=
      List.get_length_sub_one (l := E.vertexChain) (by omega)
    _ = y := E.runs.signedVertexChain_getLast

/-- The erased route inherits validity of every retained signed edge. -/
theorem valid_of_sublist
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (E : ErasedSignedRoute T.initial T.terminal T.steps)
    {s : SignedEdge V} (hs : s ∈ E.steps) :
    SignedEdge.Valid (Gamma := Gamma) s :=
  T.valid s (E.steps_sublist.subset hs)

/-- The erased route inherits the ladder provenance of every retained
backward edge. -/
theorem backward_on_ladder_of_sublist
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (E : ErasedSignedRoute T.initial T.terminal T.steps)
    {s : SignedEdge V} (hs : s ∈ E.steps)
    (hback : s.direction = .backward) :
    s.edge ∈ L.familyEdges :=
  T.backward_on_ladder s (E.steps_sublist.subset hs) hback

/-- A nonempty erased signed route is an input to the finite maximal-run
compressor. -/
noncomputable def toFiniteInputOfValid
    (E : ErasedSignedRoute x y raw)
    (hne : E.steps ≠ [])
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    Alternating.RunCompressor.FiniteInput Gamma.graph where
  lastEdge := E.steps.length
  lastEdge_pos := List.length_pos_iff_ne_nil.mpr hne
  vertex := E.routeVertex
  vertex_injective_on := by
    intro i j hi hj hij
    have hi' : i < E.vertexChain.length := by
      rw [E.vertexChain_length]
      omega
    have hj' : j < E.vertexChain.length := by
      rw [E.vertexChain_length]
      omega
    have hget : E.vertexChain.get ⟨i, hi'⟩ =
        E.vertexChain.get ⟨j, hj'⟩ := by
      change E.vertexChain.getD i y = E.vertexChain.getD j y at hij
      rw [List.getD_eq_get E.vertexChain y ⟨i, hi'⟩,
        List.getD_eq_get E.vertexChain y ⟨j, hj'⟩] at hij
      exact hij
    exact congrArg Fin.val (E.vertexChain_nodup.injective_get hget)
  colour n := (E.steps.get n).direction
  forward_adj := by
    intro n hn
    have hv := hvalid (List.get_mem E.steps n)
    rw [E.routeVertex_eq_entry n, E.routeVertex_succ_eq_exit n]
    rw [SignedEdge.entry_eq_fst_of_direction_forward _ hn,
      SignedEdge.exit_eq_snd_of_direction_forward _ hn]
    exact hv
  backward_adj := by
    intro n hn
    have hv := hvalid (List.get_mem E.steps n)
    rw [E.routeVertex_eq_entry n, E.routeVertex_succ_eq_exit n]
    rw [SignedEdge.exit_eq_fst_of_direction_backward _ hn,
      SignedEdge.entry_eq_snd_of_direction_backward _ hn]
    exact hv

/-- The specialization to an erased Lambda micro-trace. -/
noncomputable def toFiniteInput
    {p : FinitePath L.lambda.graph} {T : L.MicroTrace p}
    (E : ErasedSignedRoute T.initial T.terminal T.steps)
    (hne : E.steps ≠ []) :
    Alternating.RunCompressor.FiniteInput Gamma.graph :=
  E.toFiniteInputOfValid hne (fun {_s} hs ↦ E.valid_of_sublist L hs)

theorem step_edge_eq_routeVertices_forward
    (n : Fin E.steps.length)
    (hdir : (E.steps.get n).direction = .forward) :
    (E.steps.get n).edge =
      (E.routeVertex n, E.routeVertex (n.1 + 1)) := by
  apply Prod.ext
  · rw [E.routeVertex_eq_entry n,
      SignedEdge.entry_eq_fst_of_direction_forward _ hdir]
  · rw [E.routeVertex_succ_eq_exit n,
      SignedEdge.exit_eq_snd_of_direction_forward _ hdir]

theorem step_edge_eq_routeVertices_backward
    (n : Fin E.steps.length)
    (hdir : (E.steps.get n).direction = .backward) :
    (E.steps.get n).edge =
      (E.routeVertex (n.1 + 1), E.routeVertex n) := by
  apply Prod.ext
  · rw [E.routeVertex_succ_eq_exit n,
      SignedEdge.exit_eq_fst_of_direction_backward _ hdir]
  · rw [E.routeVertex_eq_entry n,
      SignedEdge.entry_eq_snd_of_direction_backward _ hdir]

/-- Maximal-run compression of a nonempty erased route preserves exactly
the retained (rather than the raw pre-erasure) signed edge set. -/
theorem toFiniteInputOfValid_orientedEdgeSet_eq_signedEdgeSet
    (E : ErasedSignedRoute x y raw)
    (hne : E.steps ≠ [])
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    (E.toFiniteInputOfValid hne hvalid).orientedEdgeSet =
      signedEdgeSet E.steps := by
  let S := E.toFiniteInputOfValid hne hvalid
  change S.orientedEdgeSet = signedEdgeSet E.steps
  ext e
  constructor
  · intro he
    simp only [Alternating.RunCompressor.FiniteInput.orientedEdgeSet,
      Set.mem_iUnion] at he
    obtain ⟨i, he⟩ := he
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd] at he
      rcases he with ⟨k, hk, rfl⟩
      let n : Fin E.steps.length :=
        ⟨Alternating.RunCompressor.runLower S.runs i + k, by
          change Alternating.RunCompressor.runLower S.runs i + k <
            S.lastEdge
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge i)⟩
      have hcolour := S.colour_run_offset i hk
      have hdir : (E.steps.get n).direction = .forward := by
        exact hcolour.trans hd
      refine ⟨E.steps.get n, List.get_mem E.steps n, ?_⟩
      exact (E.step_edge_eq_routeVertices_forward n hdir).trans rfl
    · have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      rw [if_neg hd] at he
      rcases he with ⟨k, hk, rfl⟩
      let n : Fin E.steps.length :=
        ⟨Alternating.RunCompressor.runLower S.runs i + k, by
          change Alternating.RunCompressor.runLower S.runs i + k <
            S.lastEdge
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge i)⟩
      have hcolour := S.colour_run_offset i hk
      have hdir : (E.steps.get n).direction = .backward := by
        exact hcolour.trans hb
      refine ⟨E.steps.get n, List.get_mem E.steps n, ?_⟩
      exact (E.step_edge_eq_routeVertices_backward n hdir).trans rfl
  · rintro ⟨s, hs, rfl⟩
    obtain ⟨n, hns⟩ := List.get_of_mem hs
    have hnflat : n.1 < S.runs.flatten.length := by
      rw [S.runs_flatten, S.colours_length]
      exact n.2
    obtain ⟨i, k, hk, hnk⟩ :=
      exists_run_offset_of_lt_flatten_length S.runs hnflat
    have hbound : Alternating.RunCompressor.runLower S.runs i + k <
        E.steps.length := by
      change Alternating.RunCompressor.runLower S.runs i + k < S.lastEdge
      exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
        (S.runUpper_le_lastEdge i)
    let m : Fin E.steps.length :=
      ⟨Alternating.RunCompressor.runLower S.runs i + k, hbound⟩
    have hnm : n = m := Fin.ext hnk
    subst n
    have hms : E.steps.get m = s := hns
    simp only [Alternating.RunCompressor.FiniteInput.orientedEdgeSet,
      Set.mem_iUnion]
    refine ⟨i, ?_⟩
    by_cases hd : S.runDirection i = .forward
    · rw [if_pos hd]
      refine ⟨k, hk, ?_⟩
      have hcolour := S.colour_run_offset i hk
      have hdir : (E.steps.get m).direction = .forward := hcolour.trans hd
      exact hms ▸ E.step_edge_eq_routeVertices_forward m hdir
    · have hb : S.runDirection i = .backward := by
        cases h : S.runDirection i
        · exact (hd h).elim
        · rfl
      rw [if_neg hd]
      refine ⟨k, hk, ?_⟩
      have hcolour := S.colour_run_offset i hk
      have hdir : (E.steps.get m).direction = .backward := hcolour.trans hb
      exact hms ▸ E.step_edge_eq_routeVertices_backward m hdir

/-- The honest alternating path obtained by maximal-run compression of a
loop-erased signed route.  Its edge set is the retained erased set, never
the generally larger raw micro-trace set. -/
structure ErasedCompression (E : ErasedSignedRoute x y raw) where
  path : Alternating.AltPath Gamma.graph
  edgeSet_eq : path.edgeSet = signedEdgeSet E.steps
  initial_eq : path.initial = x
  terminal_eq : path.terminal? = some y

/-- Every valid erased route, including a zero-edge route, compresses to an
honest alternating path with the same ordered endpoints. -/
noncomputable def compressionOfValid
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s) :
    ErasedCompression (Gamma := Gamma) E := by
  classical
  by_cases hnil : E.steps = []
  · have hxy : x = y := RunsFromTo.start_eq_of_nil (hnil ▸ E.runs)
    exact {
      path := .trivial x
      edgeSet_eq := by simp [Alternating.AltPath.edgeSet_trivial, hnil,
        signedEdgeSet_nil]
      initial_eq := Alternating.AltPath.initial_trivial x
      terminal_eq := by simp [Alternating.AltPath.terminal?_trivial, hxy] }
  · let S := E.toFiniteInputOfValid hnil hvalid
    exact {
      path := .finite S.toFiniteRunWalk.toFiniteTrace
      edgeSet_eq := S.toFiniteTrace_edgeSet.trans
        (E.toFiniteInputOfValid_orientedEdgeSet_eq_signedEdgeSet hnil hvalid)
      initial_eq := by
        rw [Alternating.AltPath.initial,
          Alternating.FiniteRunWalk.toFiniteTrace_initial]
        exact E.routeVertex_zero
      terminal_eq := by
        rw [Alternating.AltPath.terminal?,
          Alternating.FiniteRunWalk.toFiniteTrace_terminal,
          S.toFiniteRunWalk_final_last]
        exact congrArg some E.routeVertex_last }

/-- Maximal-run compression preserves the direction of every retained
edge.  The unoriented `edgeSet_eq` theorem is insufficient for simultaneous
switching: at a contact vertex we must know whether the retained edge came
from an auxiliary connector or from a backward ladder gadget. -/
theorem compressionOfValid_directionEdges_subset_directedSignedEdgeSet
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    (d : Direction) :
    (E.compressionOfValid hvalid).path.directionEdges d ⊆
      directedSignedEdgeSet d E.steps := by
  classical
  by_cases hnil : E.steps = []
  · simp [compressionOfValid, hnil, Alternating.AltPath.directionEdges,
      Alternating.AltPath.links, directedSignedEdgeSet]
  · let S := E.toFiniteInputOfValid hnil hvalid
    simp only [compressionOfValid, hnil]
    change
      (Alternating.AltPath.finite
        S.toFiniteRunWalk.toFiniteTrace).directionEdges d ⊆ _
    intro e he
    simp only [Alternating.AltPath.directionEdges,
      Alternating.AltPath.links, Alternating.FiniteTrace.links,
      Set.mem_iUnion, Set.mem_range] at he
    obtain ⟨l, ⟨i, rfl⟩, hd, he⟩ := he
    have hrun : S.runDirection (S.runIndex i) = d :=
      (S.toFiniteRunWalk_run_direction i).symm.trans hd
    change e ∈ (S.projectedRun (S.runIndex i)).link.path.edgeSet at he
    cases d with
    | forward =>
        rw [S.projectedRun_edgeSet_eq_forward (S.runIndex i) hrun] at he
        rcases he with ⟨k, hk, rfl⟩
        let n : Fin E.steps.length :=
          ⟨Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k, by
            change
              Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k <
                S.lastEdge
            exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
              (S.runUpper_le_lastEdge (S.runIndex i))⟩
        have hcolour := S.colour_run_offset (S.runIndex i) hk
        have hdir : (E.steps.get n).direction = .forward :=
          hcolour.trans hrun
        exact ⟨E.steps.get n, List.get_mem E.steps n, hdir,
          (E.step_edge_eq_routeVertices_forward n hdir).trans rfl⟩
    | backward =>
        rw [S.projectedRun_edgeSet_eq_backward (S.runIndex i) hrun] at he
        rcases he with ⟨k, hk, rfl⟩
        let n : Fin E.steps.length :=
          ⟨Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k, by
            change
              Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k <
                S.lastEdge
            exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
              (S.runUpper_le_lastEdge (S.runIndex i))⟩
        have hcolour := S.colour_run_offset (S.runIndex i) hk
        have hdir : (E.steps.get n).direction = .backward :=
          hcolour.trans hrun
        exact ⟨E.steps.get n, List.get_mem E.steps n, hdir,
          (E.step_edge_eq_routeVertices_backward n hdir).trans rfl⟩

/-- Maximal-run compression remembers the provenance of every retained
backward run.  This is the switching-level fact needed by the simultaneous
decoder; unlike a raw edge-set equality, it identifies a whole compressed
backward link as a fragment of one member of the reference warp. -/
theorem compressionOfValid_backwardLinksOn
    (E : ErasedSignedRoute x y raw)
    (hvalid : ∀ {s : SignedEdge V}, s ∈ E.steps →
      SignedEdge.Valid (Gamma := Gamma) s)
    {Y : Set Gamma.DPath} (hY : Gamma.IsWarp Y)
    (hback : ∀ {s : SignedEdge V}, s ∈ E.steps →
      s.direction = .backward → s.edge ∈ Alternating.familyEdges Y) :
    Alternating.BackwardLinksOn Y (E.compressionOfValid hvalid).path := by
  classical
  by_cases hnil : E.steps = []
  · simp [compressionOfValid, hnil, Alternating.BackwardLinksOn]
  · let S := E.toFiniteInputOfValid hnil hvalid
    suffices h : Alternating.BackwardLinksOn Y
        (.finite S.toFiniteRunWalk.toFiniteTrace) by
      simpa [compressionOfValid, hnil, S] using h
    intro l hl hdir
    change l ∈ S.toFiniteRunWalk.toFiniteTrace.links at hl
    rw [S.toFiniteRunWalk.toFiniteTrace_links] at hl
    rcases hl with ⟨i, rfl⟩
    have hrun : S.runDirection (S.runIndex i) = .backward := by
      exact (S.toFiniteRunWalk_run_direction i).symm.trans hdir
    apply Alternating.SwitchingCore.finitePath_isFragmentOf_of_edgeSet_subset_familyEdges
      hY (S.toFiniteRunWalk.run i).link.path
        (S.toFiniteRunWalk.run i).link.nontrivial
    intro e he
    change e ∈ (S.projectedRun (S.runIndex i)).link.path.edgeSet at he
    rw [S.projectedRun_edgeSet_eq_backward (S.runIndex i) hrun] at he
    rcases he with ⟨k, hk, rfl⟩
    let n : Fin E.steps.length :=
      ⟨Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k,
        by
          change Alternating.RunCompressor.runLower S.runs (S.runIndex i) + k <
            S.lastEdge
          exact lt_of_lt_of_le (Nat.add_lt_add_left hk _)
            (S.runUpper_le_lastEdge (S.runIndex i))⟩
    have hcolour := S.colour_run_offset (S.runIndex i) hk
    have hstep : (E.steps.get n).direction = .backward :=
      hcolour.trans hrun
    have hedge := hback (List.get_mem E.steps n) hstep
    rw [E.step_edge_eq_routeVertices_backward n hstep] at hedge
    exact hedge

end ErasedSignedRoute

/-! ## Canonical erasure of ordinary and endpoint-relaxed decodings -/

/-- Canonical chronological erasure and compression of a decoded Lambda
micro-trace. -/
noncomputable def MicroTrace.erasedCompression
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma)
      T.runs.erasedSignedRoute :=
  let E := T.runs.erasedSignedRoute
  E.compressionOfValid (fun {_s} hs ↦ T.valid _ (E.steps_sublist.subset hs))

theorem MicroTrace.erasedCompression_edgeSet_subset
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p) :
    T.erasedCompression.path.edgeSet ⊆ L.decodedRouteEdges p := by
  intro e he
  rw [T.erasedCompression.edgeSet_eq] at he
  obtain ⟨s, hs, rfl⟩ := he
  rw [← T.edgeSet_eq]
  exact ⟨s, T.runs.erasedSignedRoute.steps_sublist.subset hs, rfl⟩

/-- Lossless decoding of an auxiliary path whose final gadget merely has a
specified original-web exit.  Unlike `MicroTrace`, this does not require the
final gadget to be a Lambda target marker, so it applies to Section 8 cut
requests. -/
structure EndpointTrace (p : FinitePath L.lambda.graph) (z : V) where
  steps : List (SignedEdge V)
  initial : V
  runs : RunsFromTo initial z steps
  valid : ∀ s, s ∈ steps → SignedEdge.Valid (Gamma := Gamma) s
  backward_on_ladder : ∀ s, s ∈ steps →
    s.direction = .backward → s.edge ∈ L.familyEdges
  source_endpoint :
    (∃ x ∈ L.finiteSource, initial = x) ∨
      ∃ i : I, initial ∈ (L.proxyPath i).support

/-- Endpoint-relaxed decoding from an ordinary finite source. -/
noncomputable def decodeFinitePathToExitFromFinite
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (x : {x : V // x ∈ L.finiteSource ∧ p.start = .old x})
    (z : V) (hexit : L.gadgetExit p.finish = some z) :
    L.EndpointTrace p z where
  steps := L.decodeWalkSteps p.walk
  initial := x.1
  runs := L.decodeWalkSteps_runs_from_entry p.walk
    (L.start_old_gadget p x.2.2).1 hexit
  valid := fun _ hs ↦ L.decodeWalkSteps_valid p hstart hs
  backward_on_ladder := fun _ hs hb ↦
    L.decodeWalkSteps_backward_on_ladder p hstart hs hb
  source_endpoint := Or.inl ⟨x.1, x.2.1, rfl⟩

/-- Endpoint-relaxed decoding from an infinite proxy source. -/
noncomputable def decodeFinitePathToExitFromProxy
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source)
    (i : {i : I // p.start = .proxy i})
    (z : V) (hexit : L.gadgetExit p.finish = some z) :
    L.EndpointTrace p z := by
  let witness : {x : V // x ∈ (L.proxyPath i.1).support ∧
      RunsFromTo x z (L.decodeWalkSteps p.walk)} :=
    Classical.choice (by
      obtain ⟨x, hx, hruns⟩ :=
        L.decodeWalkSteps_runs_from_eq_proxy p.walk i.2 hexit
      exact ⟨⟨x, hx, hruns⟩⟩)
  exact {
    steps := L.decodeWalkSteps p.walk
    initial := witness.1
    runs := witness.2.2
    valid := fun _ hs ↦ L.decodeWalkSteps_valid p hstart hs
    backward_on_ladder := fun _ hs hb ↦
      L.decodeWalkSteps_backward_on_ladder p hstart hs hb
    source_endpoint := Or.inr ⟨i.1, witness.2.1⟩ }

/-- Decode to an arbitrary non-proxy final gadget, retaining the exact
chosen signed walk and its original-web source description. -/
noncomputable def decodeFinitePathToExit
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (z : V)
    (hexit : L.gadgetExit p.finish = some z) : L.EndpointTrace p z :=
  match L.chooseSourceEndpoint p hstart with
  | .inl x => L.decodeFinitePathToExitFromFinite p hstart x z hexit
  | .inr i => L.decodeFinitePathToExitFromProxy p hstart i z hexit

@[simp] theorem decodeFinitePathToExit_steps
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (z : V)
    (hexit : L.gadgetExit p.finish = some z) :
    (L.decodeFinitePathToExit p hstart z hexit).steps =
      L.decodeWalkSteps p.walk := by
  classical
  unfold decodeFinitePathToExit
  cases L.chooseSourceEndpoint p hstart <;> rfl

/-! ## Stopping before a final edge gadget

An edge request is applied at the head of the represented ladder edge.  Its
decoded route must therefore stop at the *entry* of the final edge gadget,
before traversing that gadget's backward edge.  The following small list
lemmas make that source convention explicit. -/

/-- Removing a final signed step from a traversable signed walk leaves a
traversable walk ending at the entry of that step. -/
theorem RunsFromTo.init_of_append_singleton
    {x z : V} {q : List (SignedEdge V)} {s : SignedEdge V}
    (h : RunsFromTo x z (q ++ [s])) :
    RunsFromTo x s.entry q := by
  induction q generalizing x with
  | nil =>
      simp only [List.nil_append] at h
      cases h with
      | cons _ tail => exact .nil _
  | cons t q ih =>
      simp only [List.cons_append] at h
      cases h with
      | cons _ tail => exact .cons t (ih tail)

/-- The deterministic decoder of a walk ending at an edge gadget ends with
exactly the backward traversal of the represented edge. -/
theorem exists_decodeWalkSteps_init_of_finish_edge
    {a b : L.LV} (q : Walk L.lambda.graph a b) {u v : V}
    (hfinish : b = .edge u v) :
    ∃ init, L.decodeWalkSteps q =
      init ++ [SignedEdge.backward (u, v)] := by
  induction q with
  | nil =>
      rw [hfinish]
      exact ⟨[], rfl⟩
  | @cons a b _ hab q ih =>
      obtain ⟨init, hinit⟩ := ih hfinish
      refine ⟨L.gadgetSteps a ++ L.connectorSteps a b ++ init, ?_⟩
      simp only [decodeWalkSteps_cons, hinit, List.append_assoc]

/-- The canonical prefix of the decoded signed list before its final edge
gadget. -/
noncomputable def decodeWalkStepsEdgeEntry
    (p : FinitePath L.lambda.graph) (u v : V)
    (hfinish : p.finish = .edge u v) : List (SignedEdge V) :=
  Classical.choose
    (L.exists_decodeWalkSteps_init_of_finish_edge p.walk hfinish)

theorem decodeWalkSteps_eq_edgeEntry_append
    (p : FinitePath L.lambda.graph) (u v : V)
    (hfinish : p.finish = .edge u v) :
    L.decodeWalkSteps p.walk =
      L.decodeWalkStepsEdgeEntry p u v hfinish ++
        [SignedEdge.backward (u, v)] :=
  Classical.choose_spec
    (L.exists_decodeWalkSteps_init_of_finish_edge p.walk hfinish)

/-- Decode a finite auxiliary path ending at an edge gadget only as far as
the gadget entry.  In particular, the represented cut edge itself is not a
step of the resulting route. -/
noncomputable def decodeFinitePathToEdgeEntry
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (u v : V)
    (hfinish : p.finish = .edge u v) : L.EndpointTrace p v := by
  have hexit : L.gadgetExit p.finish = some u := by
    rw [hfinish]
    rfl
  let T := L.decodeFinitePathToExit p hstart u hexit
  let init := L.decodeWalkStepsEdgeEntry p u v hfinish
  have hinit : L.decodeWalkSteps p.walk =
      init ++ [SignedEdge.backward (u, v)] :=
    L.decodeWalkSteps_eq_edgeEntry_append p u v hfinish
  have hsteps : T.steps = init ++ [SignedEdge.backward (u, v)] := by
    rw [L.decodeFinitePathToExit_steps]
    exact hinit
  have hruns : RunsFromTo T.initial v init := by
    have h := RunsFromTo.init_of_append_singleton
      (s := SignedEdge.backward (u, v)) (by
        rw [← hsteps]
        exact T.runs)
    simpa using h
  exact {
    steps := init
    initial := T.initial
    runs := hruns
    valid := fun s hs ↦ T.valid s (by
      rw [hsteps]
      exact List.mem_append_left _ hs)
    backward_on_ladder := fun s hs hb ↦ T.backward_on_ladder s (by
      rw [hsteps]
      exact List.mem_append_left _ hs) hb
    source_endpoint := T.source_endpoint }

@[simp] theorem decodeFinitePathToEdgeEntry_steps
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (u v : V)
    (hfinish : p.finish = .edge u v) :
    (L.decodeFinitePathToEdgeEntry p hstart u v hfinish).steps =
      L.decodeWalkStepsEdgeEntry p u v hfinish := by
  unfold decodeFinitePathToEdgeEntry
  rfl

theorem decodeFinitePathToEdgeEntry_steps_sublist
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (u v : V)
    (hfinish : p.finish = .edge u v) :
    (L.decodeFinitePathToEdgeEntry p hstart u v hfinish).steps.Sublist
      (L.decodeWalkSteps p.walk) := by
  rw [L.decodeFinitePathToEdgeEntry_steps,
    L.decodeWalkSteps_eq_edgeEntry_append p u v hfinish]
  exact List.sublist_append_left _ _

theorem decodeFinitePathToEdgeEntry_steps_append
    (p : FinitePath L.lambda.graph)
    (hstart : p.start ∈ L.lambda.source) (u v : V)
    (hfinish : p.finish = .edge u v) :
    (L.decodeFinitePathToEdgeEntry p hstart u v hfinish).steps ++
        [SignedEdge.backward (u, v)] = L.decodeWalkSteps p.walk := by
  rw [L.decodeFinitePathToEdgeEntry_steps]
  exact (L.decodeWalkSteps_eq_edgeEntry_append p u v hfinish).symm

namespace EndpointTrace

variable {p : FinitePath L.lambda.graph} {z : V}

noncomputable def erasedRoute (T : L.EndpointTrace p z) :
    ErasedSignedRoute T.initial z T.steps :=
  T.runs.erasedSignedRoute

noncomputable def erasedCompression (T : L.EndpointTrace p z) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma) T.erasedRoute :=
  T.erasedRoute.compressionOfValid
    (fun {_s} hs ↦ T.valid _ (T.erasedRoute.steps_sublist.subset hs))

theorem erasedCompression_edgeSet_subset_raw (T : L.EndpointTrace p z) :
    T.erasedCompression.path.edgeSet ⊆ signedEdgeSet T.steps := by
  intro e he
  rw [T.erasedCompression.edgeSet_eq] at he
  obtain ⟨s, hs, rfl⟩ := he
  exact ⟨s, T.erasedRoute.steps_sublist.subset hs, rfl⟩

/-- Direction-sensitive endpoint-trace provenance.  In particular a
compressed forward edge is witnessed by a forward signed step of the
head-stopping decoder, not merely by an equal unoriented micro-edge. -/
theorem erasedCompression_directionEdges_subset_steps
    (T : L.EndpointTrace p z) (d : Direction) :
    T.erasedCompression.path.directionEdges d ⊆
      directedSignedEdgeSet d T.steps := by
  intro e he
  obtain ⟨s, hs, hsd, hse⟩ :=
    T.erasedRoute.compressionOfValid_directionEdges_subset_directedSignedEdgeSet
      (fun {_s} hs ↦ T.valid _ (T.erasedRoute.steps_sublist.subset hs)) d he
  exact ⟨s, T.erasedRoute.steps_sublist.subset hs, hsd, hse⟩

/-- Every compressed backward link of an endpoint-relaxed decoding lies on
one member of the limiting ladder warp. -/
theorem erasedCompression_backwardLinksOn (T : L.EndpointTrace p z) :
    Alternating.BackwardLinksOn L.ladder.paths
      T.erasedCompression.path := by
  apply T.erasedRoute.compressionOfValid_backwardLinksOn
    (fun {_s} hs ↦ T.valid _ (T.erasedRoute.steps_sublist.subset hs))
    L.ladder.disjoint
  intro s hs hdir
  simpa [PopularAuxiliary.Input.familyEdges, Alternating.familyEdges] using
    T.backward_on_ladder s (T.erasedRoute.steps_sublist.subset hs) hdir

end EndpointTrace

end PopularAuxiliary.Input

namespace GroundingErasedDecode

open DirectedPath PopularGroundingBridge GroundingSimultaneousDecode
open PopularAuxiliary.Input
open PopularAuxiliary.Input.EndpointTrace

variable {V I : Type u} {Gamma : DWeb V}

/-- The original-web endpoint of a request route.  This is the request
vertex itself: for an old request it is the old vertex, while for a ladder
edge request `u → v` it is the head `v`.  In the latter case decoding
stops at the entry of the final edge gadget and never traverses the deleted
edge backwards. -/
def requestExit {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV} :
    Request L C → V
  | .inl x => x.1
  | .inr e => e.1.2

@[simp] theorem requestExit_eq_requestVertex
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : Request L C) : requestExit r = requestVertex r := by
  cases r <;> rfl


@[simp] theorem gadgetEntry_requestAuxVertex
    {L : PopularAuxiliary.Input Gamma I} {C : Set L.LV}
    (r : Request L C) :
    L.gadgetEntry (requestAuxVertex r) = some (requestExit r) := by
  cases r <;> rfl

/-- The endpoint-relaxed signed decoder for the strengthened selected path
at one Section 8 request. -/
noncomputable def selectedRequestTrace
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    L.EndpointTrace (strongSelectedPath U S K r) (requestExit r) := by
  let p := strongSelectedPath U S K r
  have hp : p ∈ (strongSelectedWarp U S K).paths := ⟨r, rfl⟩
  have hstart : p.start ∈ L.lambda.source :=
    (strongSelectedWarp U S K).starts_in_source hp
  have hfinish : p.finish = requestAuxVertex r :=
    strongSelectedPath_finish U S K r
  cases r with
  | inl x =>
      have hexit : L.gadgetExit p.finish = some x.1 := by
        rw [hfinish]
        rfl
      exact L.decodeFinitePathToExit p hstart x.1 hexit
  | inr e =>
      exact L.decodeFinitePathToEdgeEntry p hstart e.1.1 e.1.2 hfinish

/-- The head-stopping request decoder retains a sublist of the raw Lambda
decoder.  It is equal to the raw list for an old request and omits exactly
the final backward cut edge before possible loop erasure for an edge
request. -/
theorem selectedRequestTrace_steps_sublist
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    (selectedRequestTrace U S K r).steps.Sublist
      (L.decodeWalkSteps (strongSelectedPath U S K r).walk) := by
  classical
  cases r with
  | inl x =>
      simp [selectedRequestTrace]
  | inr e =>
      unfold selectedRequestTrace
      apply L.decodeFinitePathToEdgeEntry_steps_sublist

/-- The canonical loop-erased alternating Gamma-route attached to a
request. -/
noncomputable def selectedErasedCompression
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    ErasedSignedRoute.ErasedCompression (Gamma := Gamma)
      (selectedRequestTrace U S K r).erasedRoute :=
  (selectedRequestTrace U S K r).erasedCompression

/-- The request exit survives chronological erasure as the terminal vertex
of the compressed alternating route. -/
theorem requestExit_mem_selectedErasedCompression_vertexSet
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    requestExit r ∈ (selectedErasedCompression U S K r).path.vertexSet := by
  have hterminal := (selectedErasedCompression U S K r).terminal_eq
  cases hp : (selectedErasedCompression U S K r).path with
  | trivial x =>
      have hx : x = requestExit r := Option.some.inj (by
        simpa [hp] using hterminal)
      simpa using hx.symm
  | finite Q =>
      have hx : Q.terminal = requestExit r := Option.some.inj (by
        simpa [hp] using hterminal)
      change requestExit r ∈ Q.vertexSet
      rw [← hx]
      exact Q.terminal_mem_vertexSet
  | infinite Q =>
      have hfalse : (none : Option V) = some (requestExit r) := by
        simpa [hp] using hterminal
      cases hfalse

/-- Every compressed backward link of a selected route is a fragment of a
member of the limiting ladder warp. -/
theorem selectedErasedCompression_backwardLinksOn
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) :
    Alternating.BackwardLinksOn L.ladder.paths
      (selectedErasedCompression U S K r).path :=
  (selectedRequestTrace U S K r).erasedCompression_backwardLinksOn

/-- Direction-sensitive provenance for every edge of the selected erased
compression, stated in the raw deterministic Lambda decoding. -/
theorem selectedErasedCompression_directionEdge_provenance
    {kappa : Cardinal.{u}}
    {L : PopularAuxiliary.Input Gamma I}
    (U : Popular.KappaIndexed L.lambda kappa)
    (S : Popular.PopularSeparator U)
    (K : GroundingSelection.Controls S)
    (r : Request L S.cut) (d : Alternating.Direction)
    {e : V × V}
    (he : e ∈ (selectedErasedCompression U S K r).path.directionEdges d) :
    ∃ s : SignedEdge V,
      s ∈ L.decodeWalkSteps (strongSelectedPath U S K r).walk ∧
        s.direction = d ∧ s.edge = e := by
  obtain ⟨s, hs, hsd, hse⟩ :=
    EndpointTrace.erasedCompression_directionEdges_subset_steps
      (L := L) (selectedRequestTrace U S K r) d he
  exact ⟨s,
    (selectedRequestTrace_steps_sublist U S K r).subset hs,
    hsd, hse⟩

end GroundingErasedDecode
end Erdos599
