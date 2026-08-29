/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingCutDecoder

/-!
# Escaping suffixes from terminal grounding fragments

This file isolates the terminal splice used in Assertion 8.18.  A terminal
vertex of a surviving fragment is followed backwards to the fragment's
first escaping vertex, and the resulting auxiliary path is appended to the
escape witnessing membership in `escapeRegion`.

The displayed terminal old vertex must avoid the auxiliary cut.  This
hypothesis is necessary: it belongs to the support of every auxiliary path
starting there.  In the Section 8 application it follows from avoidance of
`BB`, since `CV ⊆ BB`.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingEscapeSuffix

open DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

abbrev Input (Gamma : DWeb V) (I : Type v) : Type (max u v) :=
  PopularAuxiliary.Input Gamma I

abbrev LV (_L : Input Gamma I) : Type (max u v) :=
  PopularAuxiliary.Input.LambdaVertex V I

/-! ## Loop-erased concatenation -/

/-- Two cut-avoiding finite paths with a common endpoint can be appended
and loop-erased without introducing a vertex of the cut. -/
theorem exists_avoiding_append
    (web : DWeb V) (C : Set V)
    (p q : FinitePath web.graph) (hpq : p.finish = q.start)
    (hp : web.Avoids p C) (hq : web.Avoids q C) :
    ∃ r : FinitePath web.graph,
      r.start = p.start ∧ r.finish = q.finish ∧ web.Avoids r C :=
  PopularSwitching.exists_avoiding_path_of_avoiding_paths p q hpq hp hq

/-! ## The terminal escape splice -/

/-- A finite terminal fragment meeting the escape region supplies an
avoiding auxiliary suffix from its terminal old vertex to the auxiliary
target.  When the blocking point is the terminal, the escape witness itself
is used.  Otherwise the surviving fragment segment is decoded backwards and
then appended to that witness.

The `old t ∉ C` premise cannot be omitted: every path in the conclusion
contains its starting vertex `old t`. -/
theorem exists_avoiding_terminal_escape
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment)
    (hP : P ∈ GroundingCut.fragments L C ∩ GroundingCut.G0 L C)
    {t : V} (ht : P.path.terminal? = some t)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (htNotC :
      (PopularAuxiliary.Input.LambdaVertex.old t : LV L) ∉ C)
    (hblockNe : GroundingCut.blockingPoint L C P ≠ t) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = PopularAuxiliary.Input.LambdaVertex.old t ∧
        q.finish ∈ L.lambda.target ∧ L.lambda.Avoids q C := by
  let b := GroundingCut.blockingPoint L C P
  have hbEscape : b ∈ L.escapeRegion C := by
    exact GroundingCut.blockingPoint_mem_escapeRegion_of_meetsEscape
      L C P hescape
  obtain ⟨E⟩ := hbEscape
  have hbSupport : b ∈ P.path.support :=
    GroundingCut.blockingPoint_mem_support L C P hP.2.2
  have hbt : GroundingCut.BeforeEq P.path b t :=
    GroundingCut.beforeEq_terminal ht hbSupport
  exact GroundingCutDecoder.exists_avoiding_reverse_to_relaxedEscape
    L C P hP.1 ⟨hbt, hblockNe⟩ htNotC E

/-- Section 8 usually knows the terminal lies outside `BB`.  Since the old
part `CV` of the auxiliary cut is contained in `BB`, this discharges the
necessary endpoint-avoidance premise of `exists_avoiding_terminal_escape`. -/
theorem exists_avoiding_terminal_escape_of_not_mem_BB
    (L : Input Gamma I) (C : Set (LV L))
    (P : L.Fragment)
    (hP : P ∈ GroundingCut.fragments L C ∩ GroundingCut.G0 L C)
    {t : V} (ht : P.path.terminal? = some t)
    (hescape : PopularAuxiliary.Input.Fragment.MeetsEscape L C P)
    (htNotBB : t ∉ GroundingCut.BB L C) :
    ∃ q : FinitePath L.lambda.graph,
      q.start = PopularAuxiliary.Input.LambdaVertex.old t ∧
        q.finish ∈ L.lambda.target ∧ L.lambda.Avoids q C := by
  apply exists_avoiding_terminal_escape L C P hP ht hescape
  intro htC
  apply htNotBB
  exact GroundingCut.CV_subset_BB L C (by simpa using htC)
  intro hblock
  apply htNotBB
  apply GroundingCut.BL_subset_BB L C
  exact ⟨P, hP.2, hblock⟩

end GroundingEscapeSuffix
end Erdos599
