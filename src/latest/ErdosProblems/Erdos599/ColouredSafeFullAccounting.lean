/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeRealReach
import ErdosProblems.Erdos599.ColouredSafeAugmentedFullAccounting
import ErdosProblems.Erdos599.TerminalContactSwitchInfinite

/-!
# Exact native full-edge and terminal accounting

The completion set is explicit. In particular accounting to one ladder
frontier is not silently upgraded to accounting to the web target.
-/

namespace Erdos599.Blueprint.ColouredSafeShortcutGraph

open Set DirectedPath Alternating ColouredSafeLocalTransactionRealLedger

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {W U R : Set (imaginaryWeb Y kappa).DPath} {B B' : Set V}

abbrev FullAccount (W U : Set (imaginaryWeb Y kappa).DPath) (B : Set V) : Prop :=
  ColouredSafeAugmentedRealReach.FullAccount Gamma (imaginaryWeb Y kappa) W U B

theorem FullAccount.refl (hW : (imaginaryWeb Y kappa).IsWarp W) (B : Set V) :
    FullAccount W W B :=
  ColouredSafeAugmentedRealReach.FullAccount.refl
    (D := imaginaryWeb Y kappa) hW B

theorem FullAccount.target_mono (h : FullAccount W U B) (hBB' : B ⊆ B') :
    FullAccount W U B' :=
  ColouredSafeAugmentedRealReach.FullAccount.target_mono
    (D := imaginaryWeb Y kappa) h hBB'

/-- Full accounting already contains the real-terminal ledger. A common
outgoing edge at an old real terminal is nonreal, and uniqueness prevents
a different real outgoing edge in the new warp. -/
theorem FullAccount.realTerminal_pending_or_completed
    (h : FullAccount W U B) (hU : (imaginaryWeb Y kappa).IsWarp U)
    {x : V} (hx : IsRealTerminal (Gamma := imaginaryWeb Y kappa)
      Gamma.graph.Adj W x) :
    IsRealTerminal (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U x ∨
      RealReaches U x B :=
  ColouredSafeAugmentedRealReach.FullAccount.realTerminal_pending_or_completed
    (D := imaginaryWeb Y kappa) h hU hx

/-- Removing a pending real terminal in an accounted extension means
actual completion to the specified set, not just loss from a work list. -/
theorem FullAccount.completed_of_not_pending
    (h : FullAccount W U B) (hU : (imaginaryWeb Y kappa).IsWarp U)
    {x : V} (hx : IsRealTerminal (Gamma := imaginaryWeb Y kappa)
      Gamma.graph.Adj W x)
    (hnot : ¬IsRealTerminal (Gamma := imaginaryWeb Y kappa)
      Gamma.graph.Adj U x) : RealReaches U x B :=
  ColouredSafeAugmentedRealReach.FullAccount.completed_of_not_pending
    (D := imaginaryWeb Y kappa) h hU hx hnot

/-- The completion-transfer premise permits both ordinary monotone
composition and an explicitly justified change of completion set. -/
theorem FullAccount.trans_of_completion_transfer
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hWU : FullAccount W U B) (hUR : FullAccount U R B')
    (hV : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hcompleted : ∀ x, RealReaches U x B → RealReaches R x B') :
    FullAccount W R B' :=
  ColouredSafeAugmentedRealReach.FullAccount.trans_of_completion_transfer
    (D := imaginaryWeb Y kappa) hU hWU hUR hV hcompleted

theorem FullAccount.trans
    (hU : (imaginaryWeb Y kappa).IsWarp U)
    (hWU : FullAccount W U B) (hUR : FullAccount U R B)
    (hWV : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U ⊆
      (imaginaryWeb Y kappa).vertexSet R)
    (hUE : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj R) :
    FullAccount W R B :=
  ColouredSafeAugmentedRealReach.FullAccount.trans
    (D := imaginaryWeb Y kappa) hU hWU hUR hWV hUV hUE

/-- Every loss in a one-cut replacement is accounted for by the actual
finite completion of the cut tail. -/
theorem fullAccount_of_cut_and_reach
    (hW : (imaginaryWeb Y kappa).IsWarp W) {s t : V}
    (hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U)
    (hterms : (imaginaryWeb Y kappa).terminalFrontier W \ {s} ⊆
      (imaginaryWeb Y kappa).terminalFrontier U)
    (hreach : RealReaches U s B) : FullAccount W U B :=
  ColouredSafeAugmentedRealReach.fullAccount_of_cut_and_reach
    (D := imaginaryWeb Y kappa) hW hcut hterms hreach

/-- Promoting one common intermediate endpoint to the actual target.
Only terminals shared with the original warp must be retained; arbitrary
new auxiliary terminals of the intermediate warp are not constrained. -/
theorem FullAccount.promote_singleton
    {z : V} (h : FullAccount W U {z})
    (hV : (imaginaryWeb Y kappa).vertexSet U ⊆
      (imaginaryWeb Y kappa).vertexSet R)
    (hE : familyEdges U ⊆ familyEdges R)
    (hT : ((imaginaryWeb Y kappa).terminalFrontier W ∩
        (imaginaryWeb Y kappa).terminalFrontier U) \ {z} ⊆
      (imaginaryWeb Y kappa).terminalFrontier R)
    (hz : RealReaches R z B) : FullAccount W R B :=
  ColouredSafeAugmentedRealReach.FullAccount.promote_singleton
    (D := imaginaryWeb Y kappa) h hV hE hT hz

/-- A displayed finite source path specifies the singleton completion
set in the exact one-cut criterion. -/
theorem fullAccount_of_cut_and_path
    (hW : (imaginaryWeb Y kappa).IsWarp W) {s t : V}
    (hcut : familyEdges W \ {(s, t)} ⊆ familyEdges U)
    (hterms : (imaginaryWeb Y kappa).terminalFrontier W \ {s} ⊆
      (imaginaryWeb Y kappa).terminalFrontier U)
    (p : FinitePath Gamma.graph) (hps : p.start = s)
    (hpV : p.support ⊆ (imaginaryWeb Y kappa).vertexSet U)
    (hpE : p.edgeSet ⊆ familyEdges U) : FullAccount W U {p.finish} :=
  ColouredSafeAugmentedRealReach.fullAccount_of_cut_and_path
    (D := imaginaryWeb Y kappa) hW hcut hterms p hps hpV hpE

/-- All old completions through one connector endpoint follow the next
real connector to its single chosen endpoint. -/
theorem FullAccount.trans_singleton
    (hU : (imaginaryWeb Y kappa).IsWarp U) {s t : V}
    (hWU : FullAccount W U {s}) (hUR : FullAccount U R {t})
    (hWV : (imaginaryWeb Y kappa).vertexSet W ⊆
      (imaginaryWeb Y kappa).vertexSet U)
    (hUV : (imaginaryWeb Y kappa).vertexSet U ⊆
      (imaginaryWeb Y kappa).vertexSet R)
    (hUE : RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj U ⊆
      RealEdges (Gamma := imaginaryWeb Y kappa) Gamma.graph.Adj R)
    (hst : RealReach R s t) : FullAccount W R {t} :=
  ColouredSafeAugmentedRealReach.FullAccount.trans_singleton
    (D := imaginaryWeb Y kappa) hU hWU hUR hWV hUV hUE hst

#print axioms FullAccount.trans
#print axioms FullAccount.realTerminal_pending_or_completed
#print axioms FullAccount.completed_of_not_pending
#print axioms fullAccount_of_cut_and_reach
#print axioms FullAccount.promote_singleton
#print axioms fullAccount_of_cut_and_path
#print axioms FullAccount.trans_singleton

end Erdos599.Blueprint.ColouredSafeShortcutGraph
