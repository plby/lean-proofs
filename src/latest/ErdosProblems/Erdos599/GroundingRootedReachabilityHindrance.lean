/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.GroundingRootedReachabilityWarp
import ErdosProblems.Erdos599.HindranceGrounding

/-!
# Hindrances from a rooted separating relation

The equal-stage grounding construction and the Assertion 8.22 construction
have the same final finite-output step.  One has a locally bi-unique relation,
a separating antichain all of whose vertices are reachable from allowed
original sources, and an original source which is not allowed as a root.

This file packages that common step without mentioning the particular
Assertion 8.22 boundary `BB`.  In particular it can be applied directly to a
repaired equal-stage relation with the essential terminal cut as boundary.
No decomposition of irrelevant relation components and no global
well-foundedness assumption is needed: only the finite rooted paths ending at
the boundary are compiled.
-/

noncomputable section

open Set

namespace Erdos599
namespace GroundingRootedReachabilityHindrance

open DirectedPath
open GroundingRootedReachabilityWarp

universe u

variable {V : Type u} {Gamma : DWeb V}

/-- A bi-unique source-rooted relation reaching a separating antichain yields
an ordinary hindrance as soon as one original source is excluded from the
allowed root set.

The proof deliberately compiles only the finite last-source-normalized paths
ending at `B`.  Thus reverse rays or unrelated components of `E` are
irrelevant.  The excluded source cannot be the initial vertex of any compiled
path, hence it is also absent from the essential part of the resulting wave.
-/
theorem exists_hindrance_of_rootedSeparatingAntichain
    (E : Set (V × V)) (A B : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hAsource : A ⊆ Gamma.source)
    (hanti : IsReachabilityAntichain E B)
    (hroot : ∀ b ∈ B, ∃ a ∈ A,
      Relation.ReflTransGen (fun x y ↦ (x, y) ∈ E) a b)
    (hseparator : Popular.IsSeparator Gamma B)
    (unused : V) (hunusedSource : unused ∈ Gamma.source)
    (hunused : unused ∉ A) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  classical
  obtain ⟨P, hcover, hpaths⟩ :=
    exists_rootedReachabilityWarp hEadj hbi hAsource hanti hroot
  let W : Set Gamma.DPath := PopularSwitching.pathFamily P
  have hWwarp : Gamma.IsWarp W :=
    PopularSwitching.pathFamily_isWarp P
  have hWinitial : Gamma.initialSet W ⊆ Gamma.source :=
    PopularSwitching.pathFamily_initialSet_subset P
  have hWterminal : Gamma.terminalFrontier W = B :=
    PopularSwitching.pathFamily_terminalFrontier_eq P hcover
  have hWwave : Gamma.IsWave W :=
    DWeb.isWave_of_terminalFrontier_isSeparator hWwarp hWinitial (by
      rw [hWterminal]
      exact hseparator)
  refine ⟨Gamma.essentialWarpPart W, hWwave.essentialWarpPart, ?_⟩
  intro heq
  have huInitial : unused ∈
      Gamma.initialSet (Gamma.essentialWarpPart W) :=
    heq.symm ▸ hunusedSource
  obtain ⟨p, hpEssential, hpInitial⟩ := huInitial
  obtain ⟨q, hqP, hpq⟩ := hpEssential.1
  cases hpq
  apply hunused
  exact hpInitial ▸ (hpaths q hqP).2.1

end GroundingRootedReachabilityHindrance

namespace DWeb.KappaLadder

open GroundingRootedReachabilityWarp

variable {V : Type u} {Gamma : DWeb V} {kappa : Cardinal.{u}}

/-- Concrete terminal-cut specialization for a legal ladder.  This is the
ambient output constructor needed by an equal-stage repaired relation: local
adjacency and bi-uniqueness, terminal-cut antichain/root reachability, and one
unused allowed source are the only remaining inputs.  Separation of the
terminal cut is supplied by ladder legality. -/
theorem exists_hindrance_of_rootedTerminalCut
    (L : Gamma.KappaLadder kappa) (hL : L.IsKappaHindrance)
    (E : Set (V × V)) (A : Set V)
    (hEadj : E ⊆ {e | Gamma.graph.Adj e.1 e.2})
    (hbi : Relator.BiUnique fun x y ↦ (x, y) ∈ E)
    (hAsource : A ⊆ Gamma.source)
    (hanti : IsReachabilityAntichain E
      (L.popularAuxiliaryInput hL.legal).terminalCut)
    (hroot : ∀ b ∈ (L.popularAuxiliaryInput hL.legal).terminalCut,
      ∃ a ∈ A, Relation.ReflTransGen
        (fun x y ↦ (x, y) ∈ E) a b)
    (unused : V) (hunusedSource : unused ∈ Gamma.source)
    (hunused : unused ∉ A) :
    ∃ H : Set Gamma.DPath, Gamma.IsHindrance H := by
  exact
    GroundingRootedReachabilityHindrance.exists_hindrance_of_rootedSeparatingAntichain
      E A (L.popularAuxiliaryInput hL.legal).terminalCut hEadj hbi
      hAsource hanti hroot
      (L.popularAuxiliaryInput_terminalCut_isSeparator hL.legal)
      unused hunusedSource hunused

end DWeb.KappaLadder
end Erdos599
