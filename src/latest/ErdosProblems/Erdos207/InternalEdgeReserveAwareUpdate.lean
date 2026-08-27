/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeConditionedKernel
import ErdosProblems.Erdos207.ReservePreservingScaleUpdate

/-!
# Reserve-aware law update by the internal-edge kernel

This packages the pointwise good-reserve kernel into the law-level update
used before the simultaneous link cover.  The internal cover has a uniform
exponential C4 factor and does not impose any additional reserve-edge
prescription, so the full reserve density factor passes unchanged.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Bind the scheduled internal-edge random-greedy kernel to every state of
a reserve-aware master law. -/
theorem IsReserveStronglyWellDistributed.jointBind_internalOuterEdgeKernel
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : ℕ} {law : FiniteLaw Omega} {W : Vortex V ell}
    {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A P0 initial later : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b p' C' b' : ℝ≥0}
    (hreserve : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (i : Fin ell) (a D horizon : ℕ) (hD : 0 < D)
    (htri : ∀ omega, ConsistsOfTriangles (G omega) (A omega))
    (hpacking0 : ∀ omega, IsPackingOn (P0 omega))
    (havoid0 : ∀ omega, AvoidsForbidden (P0 omega) F)
    (hgood : ∀ omega,
      InternalOuterReserveGood W i (G omega) (A omega) (a + D) (bits omega))
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (hblocked : ∀ omega (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F (P0 omega) Q,
      Q ⊆ P0 omega ∪ A omega →
      (Q \ P0 omega).card ≤
        (internalOuterEdges (G omega) (W.U i.succ)).card →
      ∀ he : e ∈ internalOuterEdges (G omega) (W.U i.succ),
      ∀ hleave : (leaveGraph Q).Adj e.out.1 e.out.2,
      (edgeBlockedThirdVertices (A omega) Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges
              (G omega) (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F (A omega) Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges
              (G omega) (W.U i.succ) he))).card ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p')
    (hfactor : internalEdgeC4Factor D horizon ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      internalEdgeC4Factor D horizon ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let E : Omega → Finset (Sym2 V) := fun omega ↦
      internalOuterEdges (G omega) (W.U i.succ)
    let S : Omega → Sym2 V → Finset V := fun omega e ↦
      iterationExtensionVertices (A omega)
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
    let hne : ∀ omega e, e ∈ (E omega).toList → e.out.1 ≠ e.out.2 :=
      fun omega e he ↦ out_fst_ne_snd_of_mem_graphEdges
        (internalOuterEdges_subset_graphEdges (G omega) (W.U i.succ)
          (by simpa only [Finset.mem_toList] using he))
    let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) := fun omega ↦
      internalEdgeGreedyProcessLaw F (G omega) (W.U i.succ) (bits omega)
        (S omega) (E omega).toList (hne omega) D (P0 omega)
    let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
      fun omega z ↦ z.chosen \ P0 omega
    IsReserveStronglyWellDistributed (law.jointBind K) W next
        (jointInitial initial) (jointLater later added)
        (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
      (law.jointBind K).SupportedOn (fun z ↦
        GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
        (z.2.chosen \ P0 z.1).card ≤ (E z.1).card ∧
        ∀ e ∈ E z.1,
          (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) := by
  dsimp only
  let E : Omega → Finset (Sym2 V) := fun omega ↦
    internalOuterEdges (G omega) (W.U i.succ)
  let S : Omega → Sym2 V → Finset V := fun omega e ↦
    iterationExtensionVertices (A omega)
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hne : ∀ omega e, e ∈ (E omega).toList → e.out.1 ≠ e.out.2 := by
    intro omega e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (internalOuterEdges_subset_graphEdges (G omega) (W.U i.succ)
        (by simpa only [E, Finset.mem_toList] using he))
  let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) := fun omega ↦
    internalEdgeGreedyProcessLaw F (G omega) (W.U i.succ) (bits omega)
      (S omega) (E omega).toList (hne omega) D (P0 omega)
  let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    fun omega z ↦ z.chosen \ P0 omega
  have hkernel : ∀ omega,
      (K omega).SupportedOn (fun z ↦
          GreedyReachable F (P0 omega) z.chosen ∧
          z.chosen ⊆ P0 omega ∪ A omega ∧
          (z.chosen \ P0 omega).card ≤ (E omega).card ∧
          ∀ e ∈ E omega,
            (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
        ∀ Q : TripleSystemOn V,
          (K omega).probability (fun z ↦ Q ⊆ added omega z) ≤
            internalEdgeC4Factor D horizon ^ Q.card := by
    intro omega
    simpa only [K, E, S, added] using
      (internalOuterEdge_randomGreedyKernel_of_goodReserve
        (htri omega) i (hpacking0 omega) (havoid0 omega) (bits omega)
        a D horizon hD (horizonBound omega) (hgood omega)
        (hblocked omega))
  constructor
  · apply hreserve.jointBind_adjoin_preserve_of_numeric added
      (fun omega Q ↦ (hkernel omega).2 Q) hnonempty hkn hCC' hC'
      hpp' hfactor hbb' hnew
  · have hbase : law.SupportedOn (fun _omega ↦ True) :=
      fun _omega _hmass ↦ trivial
    have hjoint := hbase.jointBind (fun omega _htrue ↦ (hkernel omega).1)
    simpa only [true_and, E, K] using hjoint

end

end Erdos207
