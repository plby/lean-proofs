/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeEndpointAccountedClubLimit

/-!
# Stable endpoint states and exact small-chain upper bounds

The actual endpoint augmentation is fixed. Extension retains full target
accounting and source predecessor refinement, besides the monotone data.
The upper bound is constructed by the checked exact relation limit.
-/

namespace Erdos599.Blueprint.ColouredSafeEndpointBlueprint

open Set Cardinal Order DirectedPath Ladder LinkageBlueprint
open _root_.Erdos599.Alternating
open _root_.Erdos599.ColouredSafeLocalTransactionRealLedger
open _root_.Erdos599.ColouredSafeAugmentedRealReach

universe u v

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}

structure StableState (C : ClubStageGeometry Gamma Y kappa (succ kappa)) (Z : Set V) where
  index : Stage (succ kappa)
  index_mem : index ∈ C.club
  old_lt : C.oldStage < index
  family : Set (web C).DPath
  blueprint : IsBlueprint C index family
  stable : (web C).terminalFrontier family ∩ C.ladder.frontier index ⊆ C.persistent
  contained : (web C).vertexSet family ⊆ Z

namespace StableState

variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)} {Z : Set V}

def carrier (S : StableState C Z) : Set V := (web C).vertexSet S.family

def completed (S : StableState C Z) : Set V :=
  {x | RealReaches Gamma (web C) S.family x Gamma.target}

structure Extends (S T : StableState C Z) : Prop where
  index_le : S.index ≤ T.index
  vertices : S.carrier ⊆ T.carrier
  realEdges : RealEdges (Gamma := web C) Gamma.graph.Adj S.family ⊆
    RealEdges (Gamma := web C) Gamma.graph.Adj T.family
  initials : (web C).initialSet S.family ⊆ (web C).initialSet T.family
  account : FullAccount Gamma (web C) S.family T.family Gamma.target
  predecessor : SourcePredecessorRefines Gamma (web C) S.family T.family

theorem Extends.refl (S : StableState C Z) : S.Extends S :=
  ⟨le_rfl, Subset.rfl, Subset.rfl, Subset.rfl,
    FullAccount.refl S.blueprint.isWarp Gamma.target, SourcePredecessorRefines.refl S.family⟩

theorem Extends.trans {S T U : StableState C Z} (hST : S.Extends T) (hTU : T.Extends U) :
    S.Extends U :=
  ⟨hST.index_le.trans hTU.index_le, hST.vertices.trans hTU.vertices,
    hST.realEdges.trans hTU.realEdges, hST.initials.trans hTU.initials,
    hST.account.trans T.blueprint.isWarp hTU.account hST.vertices hTU.vertices hTU.realEdges,
    hST.predecessor.trans hTU.predecessor hST.vertices hTU.vertices hTU.realEdges⟩

theorem Extends.completed_mono {S T : StableState C Z} (hST : S.Extends T) :
    S.completed ⊆ T.completed := fun _ hx ↦ hx.mono hST.vertices hST.realEdges

def chain {I : Type v} [LinearOrder I] (S : I → StableState C Z)
    (hS : ∀ ⦃i j⦄, i ≤ j → (S i).Extends (S j)) :
    AugmentedAccountedChain Gamma (web C) I :=
  accountedChain_of_blueprints (fun i ↦ (S i).index) (fun i ↦ (S i).family)
    (fun i ↦ (S i).blueprint) (fun _ _ hij ↦ (hS hij).vertices)
    (fun _ _ hij ↦ (hS hij).realEdges) (fun _ _ hij ↦ (hS hij).initials)
    (fun hij ↦ (hS hij).account) (fun hij ↦ (hS hij).predecessor)

/-- The upper state has the exact union carrier. In particular it does not
introduce unprocessed vertices at the end of the fair construction. -/
theorem exists_exactUpper {I : Type v} [LinearOrder I] [Nonempty I]
    (S : I → StableState C Z) (hS : ∀ ⦃i j⦄, i ≤ j → (S i).Extends (S j))
    (hI : Cardinal.lift.{u} #I ≤ Cardinal.lift.{v} kappa) :
    ∃ U : StableState C Z, (∀ i, (S i).Extends U) ∧ U.carrier = ⋃ i, (S i).carrier := by
  let R := chain S hS
  obtain ⟨a, ha, haLUB, W, hW, hstable, hWV, _hWE, hWZ, _hpop, hprior⟩ :=
    exists_stableAccountedLimit_at_clubSup (fun i ↦ (S i).index)
      (fun _ _ hij ↦ (hS hij).index_le) (fun i ↦ (S i).index_mem) R hI
      (fun i ↦ (S i).blueprint) (fun i ↦ (S i).stable) (fun i ↦ (S i).contained)
  have hold : C.oldStage < a :=
    (S (Classical.arbitrary I)).old_lt.trans_le (haLUB.1 ⟨Classical.arbitrary I, rfl⟩)
  let U : StableState C Z := ⟨a, ha, hold, W, hW, hstable, hWZ⟩
  refine ⟨U, ?_, hWV⟩
  intro i
  obtain ⟨hV, hE, hInitial, hPred, hAccount⟩ := hprior i
  exact ⟨haLUB.1 ⟨i, rfl⟩, hV, hE, hInitial, hAccount, hPred⟩

/-- Small proper ordinal histories have an upper state in the same fixed
augmentation, with no additional compatibility-provider hypothesis. -/
theorem exists_ordinalUpper (o : Ordinal.{u}) (ho : IsSuccLimit o) (hcard : o.card ≤ kappa)
    (prior : Set.Iio o → StableState C Z)
    (hprior : ∀ ⦃i j⦄, i ≤ j → (prior i).Extends (prior j)) :
    ∃ U : StableState C Z, ∀ i, (prior i).Extends U := by
  let : Nonempty o.ToType :=
    ⟨Ordinal.ToType.mk ⟨0, Ordinal.natCast_lt_of_isSuccLimit ho 0⟩⟩
  let S : o.ToType → StableState C Z := fun i ↦ prior (Ordinal.ToType.toOrd i)
  have hS : ∀ ⦃i j⦄, i ≤ j → (S i).Extends (S j) := by
    intro i j hij
    exact hprior (Ordinal.ToType.mk.symm.monotone hij)
  have hI : Cardinal.lift.{u} #o.ToType ≤ Cardinal.lift.{u} kappa := by
    simpa only [Cardinal.mk_toType, Cardinal.lift_le] using hcard
  obtain ⟨U, hU, _hUV⟩ := exists_exactUpper S hS hI
  refine ⟨U, fun i ↦ ?_⟩
  simpa [S] using hU (Ordinal.ToType.mk i)

#print axioms Extends.trans
#print axioms exists_exactUpper
#print axioms exists_ordinalUpper

end StableState
end Erdos599.Blueprint.ColouredSafeEndpointBlueprint
