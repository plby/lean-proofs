/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingWeakChronology
import ErdosProblems.Erdos599.LambdaDecoder

/-!
# Initial points for successor-corrected grounding transport

The bookkeeping at stage `a` chooses from the inessential part of
`Y_(a+1)`.  This file records the corresponding unconditional half of the
successor-corrected form of Lemma 7.17.  A chosen finite terminal, and every
point of a chosen grounded ray, lies in the strict roof of `T_(a+1)`.

The last section gives the list-theoretic propagation lemma for decoded
signed micro-traces.  It deliberately exposes the remaining geometric
obligation: each traversed signed edge must preserve the selected roof.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599

namespace PopularAuxiliary

open Alternating DirectedPath

universe u v

variable {V : Type u} {I : Type v} {Gamma : DWeb V}

namespace Input

variable {L : Input Gamma I}

/-- Membership in a set propagates along a continuous signed trace once it
propagates across each signed step.  This separates the purely ordered part
of micro-trace confinement from its graph-theoretic roof argument. -/
theorem RunsFromTo.terminal_mem_of_step_closed
    {x y : V} {q : List (SignedEdge V)}
    (h_run : RunsFromTo x y q) (S : Set V) (hx : x ∈ S)
    (hstep : ∀ s ∈ q, s.entry ∈ S → s.exit ∈ S) :
    y ∈ S := by
  induction h_run with
  | nil x => exact hx
  | cons s tail ih =>
      apply ih
      · exact hstep s (List.mem_cons_self) hx
      · intro t ht
        exact hstep t (List.mem_cons_of_mem s ht)

/-- Boundary-aware propagation along a continuous signed trace.  A local
step may fail to preserve `S` only when its entry lies in the distinguished
boundary `E`; the global conclusion retains the first such boundary contact
as an explicit witness. -/
theorem RunsFromTo.terminal_mem_or_exists_entry
    {x y : V} {q : List (SignedEdge V)}
    (h_run : RunsFromTo x y q) (S E : Set V) (hx : x ∈ S)
    (hstep : ∀ s ∈ q, s.entry ∈ S →
      s.exit ∈ S ∨ s.entry ∈ E) :
    y ∈ S ∨ ∃ s ∈ q, s.entry ∈ E := by
  induction h_run with
  | nil => exact Or.inl hx
  | cons s tail ih =>
      rcases hstep s List.mem_cons_self hx with hsexit | hsentry
      · rcases ih hsexit (fun t ht ↦
            hstep t (List.mem_cons_of_mem s ht)) with hy | ⟨t, ht, hte⟩
        · exact Or.inl hy
        · exact Or.inr ⟨t, List.mem_cons_of_mem s ht, hte⟩
      · exact Or.inr ⟨s, List.mem_cons_self, hsentry⟩

/-- Micro-trace form of boundary-aware propagation. -/
theorem MicroTrace.terminal_mem_or_exists_entry
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p)
    (S E : Set V) (hinit : T.initial ∈ S)
    (hstep : ∀ s ∈ T.steps, s.entry ∈ S →
      s.exit ∈ S ∨ s.entry ∈ E) :
    T.terminal ∈ S ∨ ∃ s ∈ T.steps, s.entry ∈ E :=
  T.runs.terminal_mem_or_exists_entry S E hinit hstep

/-- Micro-trace form of `RunsFromTo.terminal_mem_of_step_closed`. -/
theorem MicroTrace.terminal_mem_of_step_closed
    {p : FinitePath L.lambda.graph} (T : L.MicroTrace p)
    (S : Set V) (hinit : T.initial ∈ S)
    (hstep : ∀ s ∈ T.steps, s.entry ∈ S → s.exit ∈ S) :
    T.terminal ∈ S :=
  T.runs.terminal_mem_of_step_closed S hinit hstep

end Input
end PopularAuxiliary

namespace DWeb

open DirectedPath Ladder

universe u

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- A genuine forward edge cannot leave the full roof of an essential
separator when it starts in the strict roof.  The use of `strictRoof` is
sharp: at an essential boundary vertex a forward edge may point out of the
roof. -/
theorem adj_mem_roof_of_mem_strictRoof_of_essential
    {S : Set V} (hessential : Gamma.essential S = S)
    {x y : V} (hxy : Gamma.graph.Adj x y)
    (hx : x ∈ Gamma.strictRoof S) :
    y ∈ Gamma.roof S := by
  intro p hp
  let qwalk : Walk Gamma.graph y p.finish :=
    RelationalRoof.castStart Gamma.graph.Adj hp.1 p.walk
  let w : Walk Gamma.graph x p.finish := .cons hxy qwalk
  have hmeet : w.Meets S :=
    RelationalRoof.roof_meets_walk Gamma.graph.Adj Gamma.target
      hx.1 w hp.2
  obtain ⟨z, hz, hzS⟩ := hmeet
  change z ∈ (Walk.cons hxy qwalk).support at hz
  simp only [Walk.support_cons, List.mem_cons] at hz
  rcases hz with rfl | hz
  · exact False.elim (hx.2 (hessential.symm ▸ hzS))
  · have hzp : z ∈ p.walk.support := by
      simpa only [qwalk, RelationalRoof.support_castStart] using hz
    exact ⟨z, hzp, hzS⟩

end DWeb

namespace PopularAuxiliary
namespace Input

variable {V : Type u} {Gamma : DWeb V}

/-- Signed-edge wrapper for the forward-link half of Lemma 7.17. -/
theorem SignedEdge.exit_mem_roof_of_forward
    {S : Set V} (hessential : Gamma.essential S = S)
    (s : SignedEdge V)
    (hvalid : SignedEdge.Valid (Gamma := Gamma) s)
    (hforward : s.direction = .forward)
    (hentry : s.entry ∈ Gamma.strictRoof S) :
    s.exit ∈ Gamma.roof S := by
  rcases s with ⟨⟨x, y⟩, direction⟩
  cases direction with
  | forward =>
      exact Gamma.adj_mem_roof_of_mem_strictRoof_of_essential
        hessential hvalid hentry
  | backward => cases hforward

end Input
end PopularAuxiliary

namespace DWeb

open DirectedPath Ladder

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

namespace KappaLadder

/-- The ordinary successor stage represents exactly the extended successor
used by the accumulated-warp recursion. -/
@[simp]
theorem warpAt_successorStage
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (a : Stage kappa) :
    L.warpAt (L.successorStage hlegal a) = L.successorWarp a := by
  rfl

/-- A selected finite terminal is strictly roofed by the corrected
successor frontier. -/
theorem finiteTerminal_mem_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (x : L.finiteTerminalSet) :
    x.1 ∈ Gamma.strictRoof
      (L.frontier (L.successorStage hlegal (L.finiteTerminalStage x))) := by
  obtain ⟨_, p, hp, hpx⟩ := L.finiteTerminalStage_spec x
  have hp_available : p ∈ L.bookkeeping.available (L.finiteTerminalStage x) :=
    L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hp
  have hx_raw : x.1 ∈ Gamma.strictRoof
      (Gamma.terminalFrontier
        (L.successorWarp (L.finiteTerminalStage x))) :=
    Gamma.terminal_mem_strictRoof_of_mem_inessentialPaths
      hp_available.1 hpx
  rw [L.frontier_eq_essential_terminalFrontier
      hlegal.roofsSourceAtStages,
    Gamma.strictRoof_essential,
    L.warpAt_successorStage hlegal]
  exact hx_raw

/-- Every point of a grounded ray selected at `a` is strictly roofed by
`T_(a+1)`.  The ray misses the finite terminal frontier of the successor
warp by warp disjointness; prefix splicing then roofs its entire support. -/
theorem chosen_grounded_ray_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    {a : Stage kappa} {r : Ray Gamma.graph}
    (hchosen : L.chosen a = some (.inr r : Gamma.DPath))
    (hground : r.initial ∈ Gamma.source) :
    r.support ⊆ Gamma.strictRoof
      (L.frontier (L.successorStage hlegal a)) := by
  have hp_available : (.inr r : Gamma.DPath) ∈ L.bookkeeping.available a :=
    L.bookkeeping.chosen_mem_available hlegal.validBookkeeping hchosen
  let T := Gamma.terminalFrontier (L.successorWarp a)
  have hsupport_disjoint : Disjoint r.support T := by
    apply Set.disjoint_left.2
    intro z hzr hzT
    obtain ⟨q, hq_warp, hq_terminal⟩ := hzT
    have hrq : (.inr r : Gamma.DPath) ≠ q := by
      intro hrq
      have hterminal := congrArg Gamma.terminal? hrq
      rw [Gamma.terminal?_ray, hq_terminal] at hterminal
      cases hterminal
    exact Set.disjoint_left.1
      (hlegal.warpStages (Stage.succExtended a)
        hp_available.1.1 hq_warp hrq)
      hzr (Gamma.terminal_mem_support hq_terminal)
  have hsupport_roof : r.support ⊆ Gamma.roof T := by
    apply Gamma.pathSupportRoof (.inr r : Gamma.DPath) T
    · exact hlegal.roofsSourceAtStages (Stage.succExtended a) hground
    · intro t ht
      rw [Gamma.terminal?_ray] at ht
      cases ht
    · intro z hz
      exact False.elim
        (Set.disjoint_left.1 hsupport_disjoint hz.1 hz.2)
  intro z hzr
  have hz_roof : z ∈ Gamma.roof
      (L.frontier (L.successorStage hlegal a)) := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      Gamma.roof_essential,
      L.warpAt_successorStage hlegal]
    exact hsupport_roof hzr
  refine ⟨hz_roof, ?_⟩
  intro hz_essential
  have hz_frontier : z ∈ L.frontier (L.successorStage hlegal a) := by
    rw [← hlegal.frontiersEssential (L.successorStage hlegal a)]
    exact hz_essential
  have hzT : z ∈ T := by
    rw [L.frontier_eq_essential_terminalFrontier
        hlegal.roofsSourceAtStages,
      L.warpAt_successorStage hlegal] at hz_frontier
    exact hz_frontier.1
  exact Set.disjoint_left.1 hsupport_disjoint hzr hzT

/-- The represented path of every grounded infinite proxy is strictly
roofed by the successor of its record stage. -/
theorem groundedInfinitePath_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (i : L.groundedInfiniteRecords) :
    (L.groundedInfinitePath hlegal i).support ⊆ Gamma.strictRoof
      (L.frontier
        (L.successorStage hlegal (L.groundedInfiniteStage i))) := by
  obtain ⟨r, hr⟩ := L.groundedInfinitePath_isRay hlegal i
  have hchosen : L.chosen (L.groundedInfiniteStage i) =
      some (.inr r : Gamma.DPath) := by
    rw [← hr]
    exact L.groundedInfiniteStage_spec i |>.2
  obtain ⟨p, hp, hp_ground⟩ :=
    (L.groundedInfiniteStage_spec i).1.1
  have hpr : p = (.inr r : Gamma.DPath) := by
    apply Option.some.inj
    exact hp.symm.trans hchosen
  have hr_ground : r.initial ∈ Gamma.source := by
    rw [hpr] at hp_ground
    exact hp_ground
  rw [hr]
  exact L.chosen_grounded_ray_support_subset_strictRoof_successorFrontier
    hlegal hchosen hr_ground

/-- Input-level form of the proxy start-point result. -/
theorem popularAuxiliary_proxyPath_support_subset_strictRoof_successorFrontier
    (L : Gamma.KappaLadder kappa) (hlegal : L.IsLegal)
    (i : L.groundedInfiniteRecords) :
    ((L.popularAuxiliaryInput hlegal).proxyPath i).support ⊆
      Gamma.strictRoof
        (L.frontier
          (L.successorStage hlegal (L.groundedInfiniteStage i))) := by
  exact L.groundedInfinitePath_support_subset_strictRoof_successorFrontier
    hlegal i

end KappaLadder
end DWeb
end Erdos599
