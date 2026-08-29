/-
Copyright (c) 2026 The lean-proofs contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The lean-proofs contributors
-/

import ErdosProblems.Erdos599.HalfwayIndexedRelationScheduler

/-!
# Public strong half-way projection for the indexed fair scheduler

This module existentially hides the ladder index, moving slice family, and
fair relation chain only after the indexed construction has finished.  Its
output projects directly to the separating globally-resolved certificate
used by the strong half-way clause.
-/

noncomputable section

open Cardinal

namespace Erdos599
namespace CardinalInduction

universe u w

variable {V : Type u}

private abbrev IndexedState
    {Gamma : DWeb V} {Y : Set Gamma.DPath} {kappa : Cardinal.{u}}
    {persistent : Set V} {Stage : Type w}
    (slice closure : Stage → Set V) :=
  Blueprint.LinkageBlueprint.IndexedTerminalResolutionState
    (Gamma := Gamma) (Y := Y) (kappa := kappa)
    (persistent := persistent) (B := Gamma.target) slice closure

/-- Existentially packaged output of the moving-slice fair recursion at one
designated source set. -/
structure IndexedFairResolutionCertificateOutput
    (Gamma : DWeb V) (A0 : Set V) (kappa : Cardinal.{u}) where
  reference : Set Gamma.DPath
  Stage : Type w
  [stageOrder : LinearOrder Stage]
  slice : Stage → Set V
  closure : Stage → Set V
  persistent : Set V
  index : Type (u + 1)
  [indexOrder : LinearOrder index]
  [indexNonempty : Nonempty index]
  chain :
    Blueprint.LinkageBlueprint.IndexedTerminalResolutionState.ReachableResolutionRecursor.ResolutionChain
      (Gamma := Gamma) (Y := reference) (kappa := kappa)
      (persistent := persistent) (B := Gamma.target)
      (slice := slice) (closure := closure) index
  seed : IndexedState (Gamma := Gamma) (Y := reference) (kappa := kappa)
    (persistent := persistent) slice closure
  certificate :
    Blueprint.LinkageBlueprint.IndexedTerminalResolutionState.ReachableResolutionRecursor.ResolutionChain.FairResolutionCertificate
      (Gamma := Gamma) (Y := reference) (kappa := kappa)
      (persistent := persistent) (slice := slice) (closure := closure)
      chain seed A0

namespace IndexedFairResolutionCertificateOutput

/-- Erase the indexed construction while retaining its separator witness. -/
def toSeparatingGloballyResolved
    {Gamma : DWeb V} {A0 : Set V} {kappa : Cardinal.{u}}
    (O : IndexedFairResolutionCertificateOutput Gamma A0 kappa) :
    SeparatingGloballyResolvedBlueprintCertificate Gamma A0 kappa := by
  letI : LinearOrder O.Stage := O.stageOrder
  letI : LinearOrder O.index := O.indexOrder
  letI : Nonempty O.index := O.indexNonempty
  exact O.certificate.toSeparatingGloballyResolved

end IndexedFairResolutionCertificateOutput

/-- Per-web constructor for the complete indexed fair resolution output. -/
def IndexedFairResolutionCertificateCompiler
    (Gamma : DWeb V) (kappa : Cardinal.{u}) : Prop :=
  ∀ A0 : Set V, A0 ⊆ Gamma.source → #A0 = kappa →
    Nonempty (IndexedFairResolutionCertificateOutput.{u, w}
      Gamma A0 kappa)

theorem separatingGloballyResolvedBlueprintCompiler_of_indexedFairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : IndexedFairResolutionCertificateCompiler Gamma kappa) :
    SeparatingGloballyResolvedBlueprintCompiler Gamma kappa := by
  intro A0 hA0 hcard
  exact (hcompile A0 hA0 hcard).map
    IndexedFairResolutionCertificateOutput.toSeparatingGloballyResolved

/-- The indexed separator certificate is the exact producer required by
the strong half-way clause at one web and cardinal. -/
theorem separatingHalfwayClauseAt_of_indexedFairResolution
    {Gamma : DWeb V} {kappa : Cardinal.{u}}
    (hcompile : IndexedFairResolutionCertificateCompiler Gamma kappa) :
    SeparatingHalfwayClauseAt Gamma kappa := by
  intro A0 hA0 hcard
  let S := (hcompile A0 hA0 hcard).some.toSeparatingGloballyResolved
  obtain ⟨W, hstop, hlinks, hheight⟩ :=
    S.exists_separatingHalfwayLinkage
  exact ⟨W, S.certificate.stopover, hstop, hlinks, hheight⟩

/-- Uniform moving-slice scheduler constructor with exactly the hypotheses
of the simultaneous cardinal-induction half-way step. -/
def UniversalIndexedFairResolutionCertificateCompiler
    (V : Type u) : Prop :=
  ∀ kappa : Cardinal.{u},
    UniversalCardinalInductionBelow V kappa →
    UniversalExtensionClauseAt V kappa →
    ℵ₀ ≤ kappa →
    ∀ Gamma : DWeb V, Gamma.IsUnhindered →
      IndexedFairResolutionCertificateCompiler.{u, w} Gamma kappa

/-- Public strong half-way reduction from the genuinely indexed scheduler. -/
theorem halfwayClauseStep_of_indexedFairResolutionCertificateCompiler
    (hcompile : UniversalIndexedFairResolutionCertificateCompiler V) :
    ∀ kappa : Cardinal.{u},
      UniversalCardinalInductionBelow V kappa →
      UniversalExtensionClauseAt V kappa →
      ℵ₀ ≤ kappa →
      ∀ Gamma : DWeb V, Gamma.IsUnhindered →
        SeparatingHalfwayClauseAt Gamma kappa := by
  intro kappa hlower hext hkappa Gamma hGamma
  exact separatingHalfwayClauseAt_of_indexedFairResolution
    (hcompile kappa hlower hext hkappa Gamma hGamma)

end CardinalInduction
end Erdos599
