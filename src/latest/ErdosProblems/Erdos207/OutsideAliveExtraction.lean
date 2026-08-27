/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.OutsidePairSurvival
import ErdosProblems.Erdos207.CoverDownPacking

/-!
# Extracting an outside packing from an exhausted alive state

If the constrained greedy state is exhausted while every eligible outside
leave pair is still alive, no such pair can remain: an alive pair has a
nonempty available star.  This is the shortest deterministic terminal
interface for any final vortex phase that preserves outside-pair survival.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Exhaustion and outside-pair survival force the residual graph outside the
absorber to be supported on the flexible set. -/
theorem graphSupportedOn_of_exhausted_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {H : SimpleGraph V} {X : Finset V} {S : GreedyStateOn V}
    (hexhausted : S.available = ∅)
    (houtside : OutsideLeavePairsAlive H X S) :
    GraphSupportedOn (graphDifference (leaveGraph S.chosen) H) (X : Set V) := by
  intro u v huv
  by_contra hsupport
  push Not at hsupport
  have halive : PairAlive ({u, v} : Finset V) S :=
    houtside u v huv.2.2 (by simpa using hsupport) huv.1
  have hempty : availableTrianglesContainingPair S {u, v} = ∅ := by
    simp [availableTrianglesContainingPair, hexhausted]
  rw [PairAlive, hempty] at halive
  simp at halive

/-- An exhausted absorber-greedy state with outside-pair survival is already
the exact packing required by the KSSS deterministic reduction. -/
theorem hasKSSSOutsidePacking_of_exhausted_outsideLeavePairsAlive
    {V : Type*} [Fintype V] [DecidableEq V]
    {q : ℕ} {H : SimpleGraph V} {X : Finset V}
    {B : TripleSystemOn V} {S : GreedyStateOn V}
    (hS : AbsorberGreedyInvariant
      (absorberErdosForbiddenConfigurationsOn q B)
      (outsideAvailableTriangles H B) S)
    (hexhausted : S.available = ∅)
    (houtside : OutsideLeavePairsAlive H X S) :
    HasKSSSOutsidePacking q H X B S.chosen := by
  apply hasKSSSOutsidePacking_of_maximal hS.1.1 hS.2.1.1 hS.1.2.1
  exact graphSupportedOn_of_exhausted_outsideLeavePairsAlive
    hexhausted houtside

end

end Erdos207
