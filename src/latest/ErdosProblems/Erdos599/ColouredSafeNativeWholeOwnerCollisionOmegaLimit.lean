/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.ColouredSafeNativeWholeOwnerFiniteCollisionRepair
import ErdosProblems.Erdos599.SingularSafeDesignatedLimit
import ErdosProblems.Erdos599.SliceSpliceSource

/-!
# The exact protected omega limit of collision repairs

A finite collision-repair successor retains the old safely designated paths
literally.  Consequently an omega sequence of such successors has an honest
increasing union linkage.  This structural fact does not by itself imply that
deleting the union carrier leaves an unhindered web.

The exact extra limit invariant used here is
`MaximalWavesResurrectAcrossDelete`: every maximal wave in the final residual,
after the completed sources are restored, is already a wave in the original
stage web.  The checked resurrection theorem then proves final residual
unhinderedness.  This is strictly stronger than safety at every finite stage.

The completed-only matrix construction in the mathematical proof does not
need this invariant: it retains the union linkage but makes no residual-safety
claim at omega.  A construction that does need an omega-safe linkage can
supply resurrection through the checked collective retained-tree route in
`SingularSafeTreeResurrection` and `SingularCollectiveSafeBatch`.  The current
finite collision state intentionally does not pretend to retain those
common-final-deletion tree certificates.
-/

noncomputable section

open Cardinal Order Set

namespace Erdos599.Blueprint.LinkageBlueprint

open DirectedPath Ladder
open _root_.Erdos599.CardinalInduction
open _root_.Erdos599.CardinalInduction.SingularSafeDesignatedLinkage
open _root_.Erdos599.CardinalInduction.SingularSafeDesignatedLimit
open ColouredSafeMovingStages

universe u

variable {V : Type u} {Gamma : DWeb V} {Y : Set Gamma.DPath}
variable {kappa : Cardinal.{u}}
variable {C : ClubStageGeometry Gamma Y kappa (succ kappa)}
variable {seed : Set V} {z : V} {R : LimitClosure C seed}

namespace NativePostClosureIntervalTransaction

open FiniteCollisionRepairState

variable {T : NativePostClosureIntervalTransaction C seed z R}
variable {seed' : Set V} {R' : LimitClosure C seed'}

/-- An actual omega sequence of genuine finite collision-repair successors. -/
structure OmegaCollisionRepairSequence
    (T : NativePostClosureIntervalTransaction C seed z R)
    {seed' : Set V} (R' : LimitClosure C seed')
    (hlater : R.later.stage < R'.later.stage) where
  state : Nat -> FiniteCollisionRepairState T R'
  successor : forall n, IsSuccessor hlater (state n) (state (n + 1))

namespace OmegaCollisionRepairSequence

variable {hlater : R.later.stage < R'.later.stage}

/-- The sources safely designated at some finite repair stage. -/
def limitDesignated
    (Q : OmegaCollisionRepairSequence T R' hlater) : Set V :=
  ⋃ n, (Q.state n).designated

/-- The literal union of the safely designated path families. -/
def limitPaths
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    Set (C.ladder.stageWeb R.later.stage).DPath :=
  ⋃₀ Set.range (fun n => (Q.state n).safe.paths)

theorem designated_subset_succ
    (Q : OmegaCollisionRepairSequence T R' hlater) (n : Nat) :
    (Q.state n).designated ⊆ (Q.state (n + 1)).designated := by
  obtain ⟨t, _ht, hdesignated, _hpaths⟩ := Q.successor n
  rw [hdesignated]
  exact Set.subset_insert t _

theorem safePaths_subset_succ
    (Q : OmegaCollisionRepairSequence T R' hlater) (n : Nat) :
    (Q.state n).safe.paths ⊆ (Q.state (n + 1)).safe.paths := by
  obtain ⟨_t, _ht, _hdesignated, hpaths⟩ := Q.successor n
  exact hpaths

theorem designated_mono
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    Monotone (fun n => (Q.state n).designated) :=
  monotone_nat_of_le_succ Q.designated_subset_succ

theorem safePaths_mono
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    Monotone (fun n => (Q.state n).safe.paths) :=
  monotone_nat_of_le_succ Q.safePaths_subset_succ

theorem state_designated_subset_limitDesignated
    (Q : OmegaCollisionRepairSequence T R' hlater) (n : Nat) :
    (Q.state n).designated ⊆ Q.limitDesignated :=
  Set.subset_iUnion (fun m => (Q.state m).designated) n

theorem state_safePaths_subset_limitPaths
    (Q : OmegaCollisionRepairSequence T R' hlater) (n : Nat) :
    (Q.state n).safe.paths ⊆ Q.limitPaths := by
  exact Set.subset_sUnion_of_mem ⟨n, rfl⟩

/-- Every limit-designated source is still a source of the fixed old stage
web. -/
theorem limitDesignated_subset_source
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    Q.limitDesignated ⊆ (C.ladder.stageWeb R.later.stage).source := by
  intro x hx
  obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
  change x ∈ C.ladder.frontier R.later.stage
  exact T.nativeWholeOwnerInterval_isLinkageBetween.terminalFrontier_subset
    ((Q.state n).designated_subset_surviving hxn).1

/-- The families occurring in an omega repair sequence form an inclusion
chain. -/
theorem safePathRange_isChain
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    IsChain (.⊆.)
      (Set.range (fun n => (Q.state n).safe.paths)) := by
  rintro _ ⟨m, rfl⟩ _ ⟨n, rfl⟩ _hne
  rcases le_total m n with hmn | hnm
  · exact Or.inl (Q.safePaths_mono hmn)
  · exact Or.inr (Q.safePaths_mono hnm)

/-- The literal omega union has exactly the union of the finite-stage
designated sets as its initial set. -/
theorem initialSet_limitPaths
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    (C.ladder.stageWeb R.later.stage).initialSet Q.limitPaths =
      Q.limitDesignated := by
  let G := C.ladder.stageWeb R.later.stage
  apply Set.Subset.antisymm
  · rintro x ⟨p, hp, hpx⟩
    obtain ⟨P, ⟨n, rfl⟩, hpP⟩ := Set.mem_sUnion.mp hp
    apply Set.mem_iUnion.mpr
    refine ⟨n, ?_⟩
    rw [← (Q.state n).safe.linkage.initialSet_eq]
    exact ⟨p, hpP, hpx⟩
  · intro x hx
    obtain ⟨n, hxn⟩ := Set.mem_iUnion.mp hx
    have hxInitial : x ∈ G.initialSet (Q.state n).safe.paths := by
      rw [(Q.state n).safe.linkage.initialSet_eq]
      exact hxn
    obtain ⟨p, hp, hpx⟩ := hxInitial
    exact ⟨p, Q.state_safePaths_subset_limitPaths n hp, hpx⟩

/-- Pairwise disjointness passes to the literal omega union because the
finite-stage families form an inclusion chain. -/
theorem limitPaths_isWarp
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    (C.ladder.stageWeb R.later.stage).IsWarp Q.limitPaths := by
  intro p hp q hq hpq
  obtain ⟨P, ⟨m, rfl⟩, hpP⟩ := Set.mem_sUnion.mp hp
  obtain ⟨P, ⟨n, rfl⟩, hqP⟩ := Set.mem_sUnion.mp hq
  rcases le_total m n with hmn | hnm
  · exact (Q.state n).safe.isWarp
      (Q.safePaths_mono hmn hpP) hqP hpq
  · exact (Q.state m).safe.isWarp
      hpP (Q.safePaths_mono hnm hqP) hpq

/-- Finite character passes pointwise to the literal omega union. -/
theorem limitPaths_finiteCharacter
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    (C.ladder.stageWeb R.later.stage).HasFiniteCharacter Q.limitPaths := by
  intro p hp
  obtain ⟨P, ⟨n, rfl⟩, hpP⟩ := Set.mem_sUnion.mp hp
  exact (Q.state n).safe.finiteCharacter hpP

/-- Every terminal of the literal omega union remains in the fixed stage
target. -/
theorem terminalFrontier_limitPaths_subset_target
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    (C.ladder.stageWeb R.later.stage).terminalFrontier Q.limitPaths ⊆
      (C.ladder.stageWeb R.later.stage).target := by
  rintro x ⟨p, hp, hpx⟩
  obtain ⟨P, ⟨n, rfl⟩, hpP⟩ := Set.mem_sUnion.mp hp
  exact (Q.state n).safe.linkage.terminalFrontier_subset
    ⟨p, hpP, hpx⟩

/-- All structural linkage fields, including exact initials, pass to the
literal omega union without any limit residual-safety premise. -/
theorem limitPaths_isLinkageBetween
    (Q : OmegaCollisionRepairSequence T R' hlater) :
    IsLinkageBetween (C.ladder.stageWeb R.later.stage)
      Q.limitDesignated (C.ladder.stageWeb R.later.stage).target
      Q.limitPaths := by
  let G := C.ladder.stageWeb R.later.stage
  have hNorm : G.IsNormalized :=
    RegularCandidateProvider.stageWeb_isNormalized
      C.normalized C.ladder R.later.stage
  have hboundary : SliceSpliceSource.MeetsOnlyAtTerminal
      G Q.limitPaths G.target := by
    intro p hp x hxp hxTarget
    exact hNorm.terminal?_eq_of_mem_path p hxp hxTarget
  exact (SliceSpliceSource.tightLinkageBetween_of_structural
    hNorm Q.limitDesignated_subset_source Q.limitPaths_isWarp
    Q.limitPaths_finiteCharacter Q.initialSet_limitPaths
    Q.terminalFrontier_limitPaths_subset_target hboundary).1

/-- Under the genuine maximal-wave resurrection invariant, the literal
omega union is a safely deletable linkage.  The conclusion retains every
finite-stage safe path literally and has exactly the union of the designated
sets as its initial set. -/
theorem exists_safeLimit_of_resurrection
    (Q : OmegaCollisionRepairSequence T R' hlater)
    (hresurrect : MaximalWavesResurrectAcrossDelete
      (C.ladder.stageWeb R.later.stage)
      ((C.ladder.stageWeb R.later.stage).vertexSet Q.limitPaths)) :
    ∃ L : SafeDesignatedLinkage
        (C.ladder.stageWeb R.later.stage) Q.limitDesignated,
      L.paths = Q.limitPaths ∧
        ∀ n, (Q.state n).safe.paths ⊆ L.paths := by
  let G := C.ladder.stageWeb R.later.stage
  have hG : G.IsUnhindered :=
    (nativeCapturedGeometry R).newStage_isUnhindered
  have hlimit : (G.delete (G.vertexSet Q.limitPaths)).IsUnhindered :=
    isUnhindered_delete_of_resurrection hG hresurrect
  let L : SafeDesignatedLinkage G Q.limitDesignated := {
    paths := Q.limitPaths
    linkage := Q.limitPaths_isLinkageBetween
    residual_unhindered := hlimit }
  refine ⟨L, rfl, ?_⟩
  intro n
  exact Q.state_safePaths_subset_limitPaths n

#print axioms OmegaCollisionRepairSequence.initialSet_limitPaths
#print axioms OmegaCollisionRepairSequence.limitPaths_isLinkageBetween
#print axioms OmegaCollisionRepairSequence.exists_safeLimit_of_resurrection

end OmegaCollisionRepairSequence
end NativePostClosureIntervalTransaction
end Erdos599.Blueprint.LinkageBlueprint
