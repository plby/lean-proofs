/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeFixedReserveSupply

/-!
# State-dependent residual-internal kernels from a fixed reserve

This is the fixed-bit analogue of
`exists_rawResidualInternalKernel_of_directSupply`.  The reserve bits have
already been sampled before the preliminary phase, so no measurable choice
or fresh reserve exposure is made here.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A pointwise active-wedge supply for already exposed reserve bits gives a
raw residual-internal kernel on every good preliminary fiber.  The sharp C4
estimate is unconditional because the same raw process is defined on bad
fibers as well. -/
theorem rawResidualInternalKernel_of_fixedReserveSupply
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V] {ell : ℕ} {W : Vortex V ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    (Good : Omega → Prop)
    (htri : ∀ omega, Good omega → ConsistsOfTriangles (G omega) (A omega))
    (i : Fin ell)
    (hpacking0 : ∀ omega, Good omega → IsPackingOn (P0 omega))
    (havoid0 : ∀ omega, Good omega → AvoidsForbidden (P0 omega) F)
    (hinitial : ∀ omega, Good omega →
      ∀ T ∈ A omega, TriangleAvoidsGraph (coveredGraph (P0 omega)) T)
    (bits : Omega → Sym2 V → Bool)
    (a D d R k : ℕ) (hD : 0 < D)
    (hsupply : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      ∀ e ∈ E,
        a + D ≤ (activeReserveWedgeVertices (G omega) (W.U i.succ)
          (residualInternalExtensionSet W i (A omega) e)
          e.out.1 e.out.2 (bits omega)).card)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ omega, Good omega → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges
          (G omega) (W.U i.succ) (P0 omega)) v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    (∀ omega, Good omega →
      RawResidualInternalFiberGood W i F G A P0 bits D R omega) ∧
    ∀ omega Q,
      (rawResidualInternalKernel W i F G A P0 bits D omega).probability
        (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  constructor
  · intro omega hgood
    let E := preliminaryResidualInternalEdges
      (G omega) (W.U i.succ) (P0 omega)
    have hE : E ⊆ internalOuterEdges (G omega) (W.U i.succ) :=
      preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G omega) (W.U i.succ) (P0 omega)
    have hlocal :=
      scheduledOuterEdge_rawLaw_terminalRootSuccess_of_fixedReserve
        (htri omega hgood) E hE (hpacking0 omega hgood)
        (havoid0 omega hgood) (hinitial omega hgood) (bits omega)
        a D d R k hD (hsupply omega hgood) hfamily
        (hincidence omega hgood) hscalar
    have hsupportSuccess := And.intro hlocal.1 hlocal.2.1
    simpa [RawResidualInternalFiberGood, rawResidualInternalKernel, E,
      residualInternalExtensionSet, residualInternalEdgeNe] using
      hsupportSuccess
  · intro omega Q
    let E := preliminaryResidualInternalEdges
      (G omega) (W.U i.succ) (P0 omega)
    let S := residualInternalExtensionSet W i (A omega)
    let hne := residualInternalEdgeNe
      (G omega) (W.U i.succ) (P0 omega)
    apply internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
      F (G omega) (W.U i.succ) (bits omega) S E.toList hne E.nodup_toList
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (preliminaryResidualInternalEdges_subset_internalOuterEdges
          (G omega) (W.U i.succ) (P0 omega)
          (by simpa only [E, Finset.mem_toList] using he))).2.1
    · intro e he
      exact (mem_internalOuterEdges_iff.mp
        (preliminaryResidualInternalEdges_subset_internalOuterEdges
          (G omega) (W.U i.succ) (P0 omega)
          (by simpa only [E, Finset.mem_toList] using he))).2.2
    · intro e _he
      exact iterationExtensionVertices_subset (A omega)
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
    · exact hD

end

end Erdos207
