/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryAugmentedReserveNumeric
import ErdosProblems.Erdos207.SharpInternalEdgeSupportedKernel

/-!
# Composing the preliminary and internal cover laws

This file packages the first two random families in one master step.  The
preliminary kernel adds every missed crossing edge to the reserve; the sharp
scheduled internal kernel then covers all outer--outer edges while leaving
that augmented reserve unchanged.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Bind the preliminary mixed selected/uncovered law and then the sharp
internal-edge law.  The result retains both the reserve-aware product bound
and the complete internal-cover support certificate. -/
theorem IsReserveStronglyWellDistributed.jointBind_preliminary_then_internal
    {Omega Xi V : Type*} [Fintype Omega] [Fintype Xi] [Fintype V]
    [DecidableEq Omega] [DecidableEq Xi] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {Kpre : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {k mid final : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b pMid reserveDensityMid CMid bMid
      pFinal CFinal bFinal alpha eta epsilon : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W k initial later sampled
      p reserveDensity C b)
    (addedPre : Omega → Xi → TripleSystemOn V)
    (hpreliminary : ∀ omega Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
        E ⊆ preliminaryResidualCrossingEdges (G omega) U
          (addedPre omega xi)) ≤ alpha ^ Q.card * eta ^ E.card + epsilon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkMid : k ≤ mid) (hCCMid : C ≤ CMid) (hCMid : 1 ≤ CMid)
    (hpMid : p ≤ pMid) (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensityMid)
    (hreserveOne : reserveDensity ≤ 1)
    (halpha : alpha ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensityMid)
    (hbOne : b ≤ 1) (herror : b + 2 * epsilon ≤ bMid)
    (hnewPre : ∀ Q : TripleOn V,
      alpha ≤ pMid /
        ((W.U (W.truncatedLevel mid Q)).card : ℝ≥0))
    (F : ForbiddenFamilyOn V)
    (Gint : Omega × Xi → SimpleGraph V)
    (A P0 : Omega × Xi → TripleSystemOn V)
    (bits : Omega × Xi → Sym2 V → Bool)
    (i : Fin ell) (a D horizon : ℕ) (hD : 0 < D)
    (hready : (L.jointBind Kpre).SupportedOn fun z ↦
      InternalOuterKernelReady W i F (Gint z) (A z) (P0 z)
        (bits z) a D)
    (horizonBound : ∀ z,
      (internalOuterEdges (Gint z) (W.U i.succ)).card ≤ horizon)
    (hMidFinal : mid ≤ final) (hCFinal : 2 * CMid ≤ CFinal)
    (hCFinalOne : 1 ≤ CFinal) (hpFinal : pMid ≤ pFinal)
    (hfactor : (D : ℝ≥0)⁻¹ ≤ 1) (hbFinal : bMid ≤ bFinal)
    (hnewInternal : ∀ Q : TripleOn V,
      (D : ℝ≥0)⁻¹ ≤ pFinal /
        ((W.U (W.truncatedLevel final Q)).card : ℝ≥0)) :
    let LP := L.jointBind Kpre
    let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (addedPre z.1 z.2)
    let Kint : Omega × Xi → FiniteLaw (InternalEdgeGreedyStateOn V) :=
      supportedInternalOuterEdgeKernel W i F Gint A P0 bits a D
    let addedInt : Omega × Xi → InternalEdgeGreedyStateOn V →
        TripleSystemOn V := supportedInternalOuterEdgeAdded P0
    IsReserveStronglyWellDistributed (LP.jointBind Kint) W final
        (jointInitial (jointInitial initial))
        (jointLater (jointLater later addedPre) addedInt)
        (fun z ↦ reservePre z.1) pFinal reserveDensityMid
          (2 * CFinal) bFinal ∧
      (LP.jointBind Kint).SupportedOn (fun z ↦
        GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
        (z.2.chosen \ P0 z.1).card ≤
          (internalOuterEdges (Gint z.1) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (Gint z.1) (W.U i.succ),
          (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) := by
  dsimp only
  let LP := L.jointBind Kpre
  let reservePre : Omega × Xi → Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) U (sampled z.1)
      (addedPre z.1 z.2)
  have hpre : IsReserveStronglyWellDistributed LP W mid
      (jointInitial initial) (jointLater later addedPre) reservePre
      pMid reserveDensityMid (2 * CMid) bMid := by
    exact hstrong.jointBind_preliminaryAugmentedReserve_of_numeric addedPre
      hpreliminary hnonempty hkMid hCCMid hCMid hpMid hpOne hreserveMono
      hreserveOne halpha hetaOne hetaReserve hbOne herror hnewPre
  let Kint : Omega × Xi → FiniteLaw (InternalEdgeGreedyStateOn V) :=
    supportedInternalOuterEdgeKernel W i F Gint A P0 bits a D
  let addedInt : Omega × Xi → InternalEdgeGreedyStateOn V →
      TripleSystemOn V := supportedInternalOuterEdgeAdded P0
  simpa only [LP, reservePre, Kint, addedInt] using
    hpre.jointBind_supportedInternalOuterEdgeKernel_sharp i a D horizon hD
      hready horizonBound hnonempty hMidFinal hCFinal hCFinalOne hpFinal
      hfactor hbFinal hnewInternal

end

end Erdos207
