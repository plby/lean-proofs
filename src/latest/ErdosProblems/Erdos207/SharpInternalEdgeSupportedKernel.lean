/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeSupportedKernel
import ErdosProblems.Erdos207.SharpInternalEdgeC4Law

/-!
# The supported internal kernel with sharp C4

The real fibers use the sharp scheduled-process estimate `D⁻|Q|`; fallback
fibers add nothing.  Thus the supported kernel has point factor exactly
`D⁻¹`.  The schedule horizon remains only in the deterministic success
certificate and no longer contaminates the probability estimate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Uniform sharp C4 for every fiber of the totalized internal kernel. -/
theorem supportedInternalOuterEdgeKernel_C4_sharp
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega -> SimpleGraph V)
    (A P0 : Omega -> TripleSystemOn V)
    (bits : Omega -> Sym2 V -> Bool) (a D : Nat)
    (hD : 0 < D) (omega : Omega) (Q : TripleSystemOn V) :
    (supportedInternalOuterEdgeKernel W i F G A P0 bits a D omega).probability
        (fun z => Q ⊆ supportedInternalOuterEdgeAdded P0 omega z) <=
      (D : NNReal)⁻¹ ^ Q.card := by
  classical
  by_cases hready : InternalOuterKernelReady W i F (G omega) (A omega)
      (P0 omega) (bits omega) a D
  · rw [supportedInternalOuterEdgeKernel, if_pos hready]
    let E := internalOuterEdges (G omega) (W.U i.succ)
    let S : Sym2 V -> Finset V := fun e =>
      iterationExtensionVertices (A omega)
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
    let hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := fun e he =>
      out_fst_ne_snd_of_mem_graphEdges
        (internalOuterEdges_subset_graphEdges (G omega) (W.U i.succ)
          (by simpa only [Finset.mem_toList] using he))
    apply internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
      F (G omega) (W.U i.succ) (bits omega) S E.toList hne
    · exact E.nodup_toList
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (by simpa only [E, Finset.mem_toList] using he)).2.1
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (by simpa only [E, Finset.mem_toList] using he)).2.2
    · intro e he
      exact iterationExtensionVertices_subset (A omega)
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
    · exact hD
  · rw [supportedInternalOuterEdgeKernel, if_neg hready]
    rw [FiniteLaw.probability_pure]
    by_cases hQ : Q = ∅
    · subst Q
      simp
    · have hnot : ¬ Q ⊆ supportedInternalOuterEdgeAdded P0 omega
          ({ chosen := P0 omega, failed := false } :
            InternalEdgeGreedyStateOn V) := by
        simpa only [supportedInternalOuterEdgeAdded, sdiff_self,
          bot_eq_empty, subset_empty] using hQ
      simp only [hnot, if_false]
      exact zero_le

/-- Reserve-aware adjoin update using the sharp reciprocal threshold. -/
theorem IsReserveStronglyWellDistributed.jointBind_supportedInternalOuterEdgeKernel_sharp
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V]
    {ell : Nat} {law : FiniteLaw Omega} {W : Vortex V ell}
    {k next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega -> SimpleGraph V}
    {A P0 initial later : Omega -> TripleSystemOn V}
    {bits : Omega -> Sym2 V -> Bool}
    {reserve : Omega -> Finset (Sym2 V)}
    {p reserveDensity C b p' C' b' : NNReal}
    (hreserve : IsReserveStronglyWellDistributed law W k initial later reserve
      p reserveDensity C b)
    (i : Fin ell) (a D horizon : Nat) (hD : 0 < D)
    (hready : law.SupportedOn fun omega =>
      InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
        (bits omega) a D)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card <= horizon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkn : k <= next) (hCC' : C <= C') (hC' : 1 <= C')
    (hpp' : p <= p')
    (hfactor : (D : NNReal)⁻¹ <= 1)
    (hbb' : b <= b')
    (hnew : ∀ T : TripleOn V,
      (D : NNReal)⁻¹ <=
        p' / ((W.U (W.truncatedLevel next T)).card : NNReal)) :
    let K : Omega -> FiniteLaw (InternalEdgeGreedyStateOn V) :=
      supportedInternalOuterEdgeKernel W i F G A P0 bits a D
    let added : Omega -> InternalEdgeGreedyStateOn V -> TripleSystemOn V :=
      supportedInternalOuterEdgeAdded P0
    IsReserveStronglyWellDistributed (law.jointBind K) W next
        (jointInitial initial) (jointLater later added)
        (fun z => reserve z.1) p' reserveDensity (2 * C') b' ∧
      (law.jointBind K).SupportedOn (fun z =>
        GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
        (z.2.chosen \ P0 z.1).card <=
          (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
          (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) := by
  dsimp only
  let K : Omega -> FiniteLaw (InternalEdgeGreedyStateOn V) :=
    supportedInternalOuterEdgeKernel W i F G A P0 bits a D
  let added : Omega -> InternalEdgeGreedyStateOn V -> TripleSystemOn V :=
    supportedInternalOuterEdgeAdded P0
  constructor
  · apply hreserve.jointBind_adjoin_preserve_of_numeric added
      (fun omega Q => supportedInternalOuterEdgeKernel_C4_sharp
        i F G A P0 bits a D hD omega Q)
      hnonempty hkn hCC' hC' hpp' hfactor hbb' hnew
  · have hjoint := hready.jointBind
      (K := K)
      (Q := fun omega z =>
        GreedyReachable F (P0 omega) z.chosen ∧
        z.chosen ⊆ P0 omega ∪ A omega ∧
        (z.chosen \ P0 omega).card <=
          (internalOuterEdges (G omega) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (G omega) (W.U i.succ),
          (coveredGraph z.chosen).Adj e.out.1 e.out.2)
      (fun omega homega =>
        (supportedInternalOuterEdgeKernel_ready i F G A P0 bits a D horizon
          hD horizonBound omega homega).1)
    simpa only [FiniteLaw.SupportedOn, K] using
      (fun z hz => (hjoint z hz).2)

end

end Erdos207
