/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeConditionedKernel
import ErdosProblems.Erdos207.ReservePreservingScaleUpdate

/-!
# Internal-edge kernels whose good hypotheses hold on support

Conditioning a finite law makes the conditioning event true at every
positive-mass outcome, but it does not replace the ambient sample type by a
subtype.  Thus a state-dependent kernel used after conditioning must still be
defined at irrelevant, zero-mass states.  This file uses the real scheduled
internal-edge kernel at ready states and a deterministic empty-extension
kernel elsewhere.  The latter has the same C4 bound trivially.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- All pointwise hypotheses needed to make the internal-edge scheduled
kernel cover every required edge. -/
def InternalOuterKernelReady
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V)
    (A P0 : TripleSystemOn V) (bits : Sym2 V → Bool)
    (a D : ℕ) : Prop :=
  ConsistsOfTriangles G A ∧
    IsPackingOn P0 ∧
    AvoidsForbidden P0 F ∧
    InternalOuterReserveGood W i G A (a + D) bits ∧
    ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ (_hreach : GreedyReachable F P0 Q),
      ∀ (_hsub : Q ⊆ P0 ∪ A),
      ∀ (_hcard : (Q \ P0).card ≤
        (internalOuterEdges G (W.U i.succ)).card),
      ∀ (he : e ∈ internalOuterEdges G (W.U i.succ)),
      ∀ (_hleave : (leaveGraph Q).Adj e.out.1 e.out.2),
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he))).card ≤ a

/-- Use the genuine scheduled internal-edge kernel at ready states and a
deterministic no-op kernel at all irrelevant states. -/
noncomputable def supportedInternalOuterEdgeKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V)
    (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (a D : ℕ)
    (omega : Omega) : FiniteLaw (InternalEdgeGreedyStateOn V) := by
  classical
  let E := internalOuterEdges (G omega) (W.U i.succ)
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices (A omega)
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
    out_fst_ne_snd_of_mem_graphEdges
      (internalOuterEdges_subset_graphEdges (G omega) (W.U i.succ)
        (by simpa only [Finset.mem_toList] using he))
  exact if InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
        (bits omega) a D then
      internalEdgeGreedyProcessLaw F (G omega) (W.U i.succ) (bits omega)
        S E.toList hne D (P0 omega)
    else
      FiniteLaw.pure { chosen := P0 omega, failed := false }

/-- The extension family exposed by the supported internal-edge kernel. -/
def supportedInternalOuterEdgeAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (P0 : Omega → TripleSystemOn V)
    (omega : Omega) (z : InternalEdgeGreedyStateOn V) : TripleSystemOn V :=
  z.chosen \ P0 omega

/-- At every ready state the supported kernel is the genuine internal-edge
kernel, hence it covers all scheduled internal edges and satisfies C4. -/
theorem supportedInternalOuterEdgeKernel_ready
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V)
    (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (a D horizon : ℕ)
    (hD : 0 < D)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (omega : Omega)
    (hready : InternalOuterKernelReady W i F (G omega) (A omega)
      (P0 omega) (bits omega) a D) :
    let E := internalOuterEdges (G omega) (W.U i.succ)
    (supportedInternalOuterEdgeKernel W i F G A P0 bits a D omega).SupportedOn
        (fun z ↦
          GreedyReachable F (P0 omega) z.chosen ∧
          z.chosen ⊆ P0 omega ∪ A omega ∧
          (z.chosen \ P0 omega).card ≤ E.card ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        (supportedInternalOuterEdgeKernel W i F G A P0 bits a D omega).probability
            (fun z ↦ Q ⊆ supportedInternalOuterEdgeAdded P0 omega z) ≤
          internalEdgeC4Factor D horizon ^ Q.card := by
  dsimp only
  rw [supportedInternalOuterEdgeKernel, if_pos hready]
  exact internalOuterEdge_randomGreedyKernel_of_goodReserve
    hready.1 i hready.2.1 hready.2.2.1 (bits omega) a D horizon hD
      (horizonBound omega) hready.2.2.2.1
      (fun Q e hreach hsub hcard he hleave ↦
        hready.2.2.2.2 Q e hreach hsub hcard he hleave)

/-- Even at an unsupported state the fallback kernel obeys the same C4
bound, because it adds no triangle. -/
theorem supportedInternalOuterEdgeKernel_C4
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V)
    (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (a D horizon : ℕ)
    (hD : 0 < D)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (omega : Omega) (Q : TripleSystemOn V) :
    (supportedInternalOuterEdgeKernel W i F G A P0 bits a D omega).probability
        (fun z ↦ Q ⊆ supportedInternalOuterEdgeAdded P0 omega z) ≤
      internalEdgeC4Factor D horizon ^ Q.card := by
  classical
  by_cases hready : InternalOuterKernelReady W i F (G omega) (A omega)
      (P0 omega) (bits omega) a D
  · exact (supportedInternalOuterEdgeKernel_ready i F G A P0 bits a D horizon
      hD horizonBound omega hready).2 Q
  · rw [supportedInternalOuterEdgeKernel, if_neg hready]
    rw [FiniteLaw.probability_pure]
    by_cases hQ : Q = ∅
    · subst Q
      simp
    · have hnot : ¬ Q ⊆ supportedInternalOuterEdgeAdded P0 omega
          ({ chosen := P0 omega, failed := false } :
            InternalEdgeGreedyStateOn V) := by
        simpa only [supportedInternalOuterEdgeAdded, sdiff_self,
          bot_eq_empty, Finset.subset_empty] using hQ
      simp only [hnot, if_false]
      exact zero_le

/-- A reserve-aware law only needs readiness on its support.  The fallback
fibers make the conditional C4 estimate total, and support of the joint law
then supplies the successful-cover certificate. -/
theorem IsReserveStronglyWellDistributed.jointBind_supportedInternalOuterEdgeKernel
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
    (hready : law.SupportedOn fun omega ↦
      InternalOuterKernelReady W i F (G omega) (A omega) (P0 omega)
        (bits omega) a D)
    (horizonBound : ∀ omega,
      (internalOuterEdges (G omega) (W.U i.succ)).card ≤ horizon)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hkn : k ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p')
    (hfactor : internalEdgeC4Factor D horizon ≤ 1)
    (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      internalEdgeC4Factor D horizon ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) :=
      supportedInternalOuterEdgeKernel W i F G A P0 bits a D
    let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
      supportedInternalOuterEdgeAdded P0
    IsReserveStronglyWellDistributed (law.jointBind K) W next
        (jointInitial initial) (jointLater later added)
        (fun z ↦ reserve z.1) p' reserveDensity (2 * C') b' ∧
      (law.jointBind K).SupportedOn (fun z ↦
        GreedyReachable F (P0 z.1) z.2.chosen ∧
        z.2.chosen ⊆ P0 z.1 ∪ A z.1 ∧
        (z.2.chosen \ P0 z.1).card ≤
          (internalOuterEdges (G z.1) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (G z.1) (W.U i.succ),
          (coveredGraph z.2.chosen).Adj e.out.1 e.out.2) := by
  dsimp only
  let K : Omega → FiniteLaw (InternalEdgeGreedyStateOn V) :=
    supportedInternalOuterEdgeKernel W i F G A P0 bits a D
  let added : Omega → InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    supportedInternalOuterEdgeAdded P0
  constructor
  · apply hreserve.jointBind_adjoin_preserve_of_numeric added
      (fun omega Q ↦ supportedInternalOuterEdgeKernel_C4 i F G A P0 bits
        a D horizon hD horizonBound omega Q)
      hnonempty hkn hCC' hC' hpp' hfactor hbb' hnew
  · have hjoint := hready.jointBind
      (K := K)
      (Q := fun omega z ↦
        GreedyReachable F (P0 omega) z.chosen ∧
        z.chosen ⊆ P0 omega ∪ A omega ∧
        (z.chosen \ P0 omega).card ≤
          (internalOuterEdges (G omega) (W.U i.succ)).card ∧
        ∀ e ∈ internalOuterEdges (G omega) (W.U i.succ),
          (coveredGraph z.chosen).Adj e.out.1 e.out.2)
      (fun omega homega ↦
        (supportedInternalOuterEdgeKernel_ready i F G A P0 bits a D horizon
          hD horizonBound omega homega).1)
    simpa only [FiniteLaw.SupportedOn, K] using
      (fun z hz ↦ (hjoint z hz).2)

end

end Erdos207
