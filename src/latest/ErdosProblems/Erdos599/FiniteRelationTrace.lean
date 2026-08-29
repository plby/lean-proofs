/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.AlternatingEdgeWalk
import Mathlib.Data.List.SplitBy

/-!
# Finite two-colour relation walks and alternating traces

This file is the finite extraction interface used by the reverse-reachability
part of the alternating-path dichotomy.  A search first erases loops in its
projected vertex walk and compresses consecutive steps of the same colour.
The resulting nonempty runs are recorded by `FiniteRunWalk`; the theorem
`FiniteReverseReachabilityCertificate.exists_trace` then forgets the search
indices and returns the literal finite bracket-alternating trace, with both
endpoints exposed.

`FiniteCertifiedRunWalk` is a second, deliberately more general interface.
It is useful for state-space searches whose state walk is injective but whose
vertex projection can revisit a vertex.  Such a search supplies the precise
`CompatibleInOrder` certificate directly instead of pretending that the
vertex projection is injective.
-/

namespace Erdos599.Alternating

open Set DirectedPath

universe u

variable {V : Type u} {D : Digraph V} {Gamma : DWeb V}

/-! ## Maximal colour blocks -/

/-- Maximal consecutive constant-colour blocks.  `List.splitBy` retains the
order of the original edge colours and starts a new block precisely when two
successive colours differ. -/
def colourRuns (colours : List Direction) : List (List Direction) :=
  colours.splitBy (fun a b => a == b)

@[simp]
theorem flatten_colourRuns (colours : List Direction) :
    (colourRuns colours).flatten = colours :=
  List.flatten_splitBy _ _

theorem colourRun_ne_nil {colours run : List Direction}
    (hrun : run ∈ colourRuns colours) : run ≠ [] :=
  List.ne_nil_of_mem_splitBy hrun

theorem colourRuns_ne_nil {colours : List Direction} (h : colours ≠ []) :
    colourRuns colours ≠ [] :=
  List.splitBy_ne_nil.2 h

/-- Adjacent maximal colour blocks have different boundary colours. -/
theorem colourRuns_boundary_ne {colours : List Direction} :
    (colourRuns colours).IsChain (fun a b ↦
      ∃ ha : a ≠ [], ∃ hb : b ≠ [],
        a.getLast ha ≠ b.head hb) := by
  have h := List.isChain_getLast_head_splitBy
    (fun a b : Direction => a == b) colours
  refine h.imp ?_
  intro a b hab
  rcases hab with ⟨ha, hb, heq⟩
  exact ⟨ha, hb, by
    intro hab'
    have htrue : (a.getLast ha == b.head hb) = true := by
      simpa only [beq_iff_eq] using hab'
    exact Bool.noConfusion (heq.symm.trans htrue)⟩

/-! ## A compatibility-certified finite run sequence -/

/-- A finite sequence of already-compressed links for which compatibility is
proved directly.  Unlike `FiniteRunWalk`, no injectivity hypothesis is made
about a projected vertex sequence. -/
structure FiniteCertifiedRunWalk (D : Digraph V) where
  lastIndex : ℕ
  link : Fin (lastIndex + 1) → Link D
  joins : ∀ i : Fin lastIndex,
    (link i.castSucc).exit = (link i.succ).entry
  alternates : ∀ i : Fin lastIndex,
    (link i.castSucc).direction ≠ (link i.succ).direction
  compatible : ∀ i j : Fin (lastIndex + 1), i < j →
    CompatibleInOrder (j.1 = i.1 + 1) (link i) (link j)

namespace FiniteCertifiedRunWalk

variable (W : FiniteCertifiedRunWalk D)

/-- Forget the search certificate and retain the literal alternating trace. -/
def toFiniteTrace : FiniteTrace D where
  lastIndex := W.lastIndex
  link := W.link
  joins := W.joins
  alternates := W.alternates
  compatible := W.compatible

@[simp] theorem toFiniteTrace_link (i : Fin (W.lastIndex + 1)) :
    W.toFiniteTrace.link i = W.link i := rfl

@[simp] theorem toFiniteTrace_initial :
    W.toFiniteTrace.initial = (W.link ⟨0, Nat.zero_lt_succ _⟩).entry :=
  rfl

@[simp] theorem toFiniteTrace_terminal :
    W.toFiniteTrace.terminal =
      (W.link ⟨W.lastIndex, Nat.lt_succ_self _⟩).exit :=
  rfl

theorem toFiniteTrace_links :
    W.toFiniteTrace.links = Set.range W.link :=
  rfl

end FiniteCertifiedRunWalk

/-! ## The reverse-reachability extraction payload -/

/-- The two-colour relation traversed by a reducing search: forward along a
member of `U`, or backward along a member of the reference warp `Z`. -/
def ForwardBackwardRel (U Z : Set Gamma.DPath) (x y : V) : Prop :=
  (x, y) ∈ familyEdges U ∨ (y, x) ∈ familyEdges Z

/-- A completed finite reverse-reachability extraction.  The construction
upstream supplies the loop-erased projected runs; the fields below are exactly
the local warp labels and endpoint facts needed to obtain a literal
`[U,Z]`-alternating path. -/
structure FiniteReverseReachabilityCertificate
    (Gamma : DWeb V) (U Z : Set Gamma.DPath) (s t : V) where
  walk : FiniteRunWalk Gamma.graph
  labels : walk.BracketLabels U Z
  initial_eq : walk.vertex 0 = s
  terminal_eq : walk.vertex (walk.run walk.lastRunIndex).last = t

namespace FiniteReverseReachabilityCertificate

variable {U Z : Set Gamma.DPath} {s t : V}
    (C : FiniteReverseReachabilityCertificate Gamma U Z s t)

/-- The concrete finite alternating path extracted from the run certificate. -/
def trace : FiniteTrace Gamma.graph := C.walk.toFiniteTrace

@[simp] theorem trace_initial : C.trace.initial = s := by
  rw [trace, C.walk.toFiniteTrace_initial, C.initial_eq]

@[simp] theorem trace_terminal : C.trace.terminal = t := by
  rw [trace, C.walk.toFiniteTrace_terminal, C.terminal_eq]

theorem isBracketAlternating :
    IsBracketAlternating U Z (.finite C.trace) :=
  C.walk.isBracketAlternating C.labels

/-- Endpoint-exposed finite alternative used by reverse reachability. -/
theorem exists_trace
    (C : FiniteReverseReachabilityCertificate Gamma U Z s t) :
    ∃ Q : FiniteTrace Gamma.graph,
      IsBracketAlternating U Z (.finite Q) ∧
      Q.initial = s ∧ Q.terminal = t :=
  ⟨trace C, isBracketAlternating C, trace_initial C, trace_terminal C⟩

/-- The same conclusion in the optional-terminal language of `AltPath`. -/
theorem exists_altPath
    (C : FiniteReverseReachabilityCertificate Gamma U Z s t) :
    ∃ Q : AltPath Gamma.graph,
      IsBracketAlternating U Z Q ∧ Q.initial = s ∧ Q.terminal? = some t := by
  refine ⟨.finite (trace C), isBracketAlternating C, trace_initial C, ?_⟩
  simp [trace_terminal C]

end FiniteReverseReachabilityCertificate

end Erdos599.Alternating
