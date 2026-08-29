/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeAugmentedRealReach
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Full-edge and terminal accounting in an arbitrary augmented web

The original and augmented webs are explicit parameters; the proof uses
only their real-edge relation and warp incidence. The completion set is explicit.
In particular accounting to one ladder
frontier is not silently upgraded to accounting to the web target.
-/

namespace Erdos599.ColouredSafeAugmentedRealReach

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma D : DWeb V}
variable {W U R : Set D.DPath} {B B' : Set V}

def FullAccount (Gamma D : DWeb V) (W U : Set D.DPath) (B : Set V) : Prop :=
  ∀ x ∈ D.vertexSet W,
    (x ∈ D.terminalFrontier W ∧
      x ∈ D.terminalFrontier U) ∨
    (∃ y, (x, y) ∈ familyEdges W ∧ (x, y) ∈ familyEdges U) ∨ RealReaches Gamma D U x B

theorem FullAccount.refl (hW : D.IsWarp W) (B : Set V) :
    FullAccount Gamma D W W B := by
  classical
  intro x hx
  by_cases hterm : x ∈ D.terminalFrontier W
  · exact Or.inl ⟨hterm, hterm⟩
  · right; left
    have hout : HasOutgoing (familyEdges W) x := by
      by_contra hno
      apply hterm
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hW]
      exact ⟨hx, hno⟩
    obtain ⟨y, hy⟩ := hout
    exact ⟨y, hy, hy⟩

theorem FullAccount.target_mono (h : FullAccount Gamma D W U B) (hBB' : B ⊆ B') :
    FullAccount Gamma D W U B' := by
  intro x hx
  rcases h x hx with hterm | hedge | hdone
  · exact Or.inl hterm
  · exact Or.inr (Or.inl hedge)
  · exact Or.inr (Or.inr (hdone.target_mono hBB'))

/-- Full accounting already contains the real-terminal ledger. A common
outgoing edge at an old real terminal is nonreal, and uniqueness prevents
a different real outgoing edge in the new warp. -/
theorem FullAccount.realTerminal_pending_or_completed
    (h : FullAccount Gamma D W U B) (hU : D.IsWarp U)
    {x : V} (hx : IsRealTerminal (Gamma := D)
      Gamma.graph.Adj W x) :
    IsRealTerminal (Gamma := D) Gamma.graph.Adj U x ∨
      RealReaches Gamma D U x B := by
  rcases h x hx.1 with hterm | ⟨y, hyW, hyU⟩ | hdone
  · left
    have hxU := hterm.2
    rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU]
      at hxU
    exact ⟨hxU.1, fun ⟨z, hz, _⟩ ↦ hxU.2 ⟨z, hz⟩⟩
  · left
    refine ⟨(familyEdges_subset_vertexSet_prod U hyU).1, ?_⟩
    rintro ⟨z, hz, hreal⟩
    have hzy : z = y := (IsWarp.familyEdges_biUnique hU).2 hz hyU
    exact hx.2 ⟨y, hyW, hzy ▸ hreal⟩
  · exact Or.inr hdone

/-- Removing a pending real terminal in an accounted extension means
actual completion to the specified set, not just loss from a work list. -/
theorem FullAccount.completed_of_not_pending
    (h : FullAccount Gamma D W U B) (hU : D.IsWarp U)
    {x : V} (hx : IsRealTerminal (Gamma := D)
      Gamma.graph.Adj W x)
    (hnot : ¬IsRealTerminal (Gamma := D)
      Gamma.graph.Adj U x) : RealReaches Gamma D U x B :=
  (h.realTerminal_pending_or_completed hU hx).resolve_left hnot

/-- The completion-transfer premise permits both ordinary monotone
composition and an explicitly justified change of completion set. -/
theorem FullAccount.trans_of_completion_transfer
    (hU : D.IsWarp U)
    (hWU : FullAccount Gamma D W U B) (hUR : FullAccount Gamma D U R B')
    (hV : D.vertexSet W ⊆
      D.vertexSet U)
    (hcompleted : ∀ x, RealReaches Gamma D U x B → RealReaches Gamma D R x B') :
    FullAccount Gamma D W R B' := by
  intro x hx
  rcases hWU x hx with hterm | ⟨y, hyW, hyU⟩ | hdone
  · rcases hUR x (hV hx) with hterm' | ⟨y, hyU, _⟩ | hdone
    · exact Or.inl ⟨hterm.1, hterm'.2⟩
    · have hno := hterm.2
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU]
        at hno
      exact False.elim (hno.2 ⟨y, hyU⟩)
    · exact Or.inr (Or.inr hdone)
  · rcases hUR x (hV hx) with hterm' | ⟨z, hzU, hzR⟩ | hdone
    · have hno := hterm'.1
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hU]
        at hno
      exact False.elim (hno.2 ⟨y, hyU⟩)
    · have hyz := (IsWarp.familyEdges_biUnique hU).2 hyU hzU
      exact Or.inr (Or.inl ⟨y, hyW, hyz.symm ▸ hzR⟩)
    · exact Or.inr (Or.inr hdone)
  · exact Or.inr (Or.inr (hcompleted x hdone))

theorem FullAccount.trans
    (hU : D.IsWarp U)
    (hWU : FullAccount Gamma D W U B) (hUR : FullAccount Gamma D U R B)
    (hWV : D.vertexSet W ⊆
      D.vertexSet U)
    (hUV : D.vertexSet U ⊆
      D.vertexSet R)
    (hUE : RealEdges (Gamma := D) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := D) Gamma.graph.Adj R) :
    FullAccount Gamma D W R B :=
  hWU.trans_of_completion_transfer hU hUR hWV (fun _ h ↦ h.mono hUV hUE)

/-- Every loss in a one-cut replacement is accounted for by the actual
finite completion of the cut tail. -/
theorem fullAccount_of_cut_and_reach
    (hW : D.IsWarp W) {s t : V}
    (hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U)
    (hterms : D.terminalFrontier W \ {s} ⊆
      D.terminalFrontier U)
    (hreach : RealReaches Gamma D U s B) : FullAccount Gamma D W U B := by
  classical
  intro x hx
  by_cases hxs : x = s
  · exact Or.inr (Or.inr (hxs ▸ hreach))
  by_cases hterm : x ∈ D.terminalFrontier W
  · exact Or.inl ⟨hterm, hterms ⟨hterm, hxs⟩⟩
  · have hout : HasOutgoing (familyEdges W) x := by
      by_contra hno
      apply hterm
      rw [TerminalContactSwitch.terminalFrontier_eq_vertexSet_diff_hasOutgoing_anyWarp hW]
      exact ⟨hx, hno⟩
    obtain ⟨y, hy⟩ := hout
    refine Or.inr (Or.inl ⟨y, hy, hcut ⟨hy, ?_⟩⟩)
    intro heq
    exact hxs (congrArg Prod.fst (Set.mem_singleton_iff.mp heq))

/-- Promoting one common intermediate endpoint to the actual target.
Only terminals shared with the original warp must be retained; arbitrary
new auxiliary terminals of the intermediate warp are not constrained. -/
theorem FullAccount.promote_singleton
    {z : V} (h : FullAccount Gamma D W U {z})
    (hV : D.vertexSet U ⊆
      D.vertexSet R)
    (hE : familyEdges U ⊆ familyEdges R)
    (hT : (D.terminalFrontier W ∩
        D.terminalFrontier U) \ {z} ⊆
      D.terminalFrontier R)
    (hz : RealReaches Gamma D R z B) : FullAccount Gamma D W R B := by
  classical
  intro x hx
  rcases h x hx with hterm | ⟨y, hyW, hyU⟩ | ⟨t, htz, hxt⟩
  · by_cases hxz : x = z
    · exact Or.inr (Or.inr (hxz ▸ hz))
    · exact Or.inl ⟨hterm.1, hT ⟨hterm, hxz⟩⟩
  · exact Or.inr (Or.inl ⟨y, hyW, hE hyU⟩)
  · have htz' : t = z := Set.mem_singleton_iff.mp htz
    have hreal : RealReach Gamma D R x z :=
      htz' ▸ hxt.mono hV (fun _ he ↦ ⟨hE he.1, he.2⟩)
    exact Or.inr (Or.inr (hreal.then_reaches hz))

/-- A displayed finite source path specifies the singleton completion
set in the exact one-cut criterion. -/
theorem fullAccount_of_cut_and_path
    (hW : D.IsWarp W) {s t : V}
    (hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U)
    (hterms : D.terminalFrontier W \ {s} ⊆
      D.terminalFrontier U)
    (p : FinitePath Gamma.graph) (hps : p.start = s)
    (hpV : p.support ⊆ D.vertexSet U)
    (hpE : p.edgeSet ⊆ familyEdges U) : FullAccount Gamma D W U {p.finish} :=
  fullAccount_of_cut_and_reach hW hcut hterms
    ⟨p.finish, Set.mem_singleton _, hps ▸ RealReach.of_path p hpV hpE⟩

/-- All old completions through one connector endpoint follow the next
real connector to its single chosen endpoint. -/
theorem FullAccount.trans_singleton
    (hU : D.IsWarp U) {s t : V}
    (hWU : FullAccount Gamma D W U {s}) (hUR : FullAccount Gamma D U R {t})
    (hWV : D.vertexSet W ⊆
      D.vertexSet U)
    (hUV : D.vertexSet U ⊆
      D.vertexSet R)
    (hUE : RealEdges (Gamma := D) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := D) Gamma.graph.Adj R)
    (hst : RealReach Gamma D R s t) : FullAccount Gamma D W R {t} := by
  apply hWU.trans_of_completion_transfer hU hUR hWV
  rintro x ⟨z, hz, hxz⟩
  have hzs : z = s := Set.mem_singleton_iff.mp hz
  exact ⟨t, Set.mem_singleton _, (hzs ▸ hxz.mono hUV hUE).trans hst⟩

#print axioms FullAccount.trans
#print axioms FullAccount.realTerminal_pending_or_completed
#print axioms FullAccount.completed_of_not_pending
#print axioms fullAccount_of_cut_and_reach
#print axioms FullAccount.promote_singleton
#print axioms fullAccount_of_cut_and_path
#print axioms FullAccount.trans_singleton

end Erdos599.ColouredSafeAugmentedRealReach
