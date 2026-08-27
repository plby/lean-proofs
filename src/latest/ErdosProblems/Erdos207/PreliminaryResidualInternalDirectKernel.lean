/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalKernel
import ErdosProblems.Erdos207.InternalEdgeDirectSupply

/-!
# State-dependent residual-internal kernels from direct supplies

This is the state-dependent counterpart of `InternalEdgeDirectSupply`.  It
retains the globally sharp C4 bound by totalizing bad fibers with the same
raw process, while choosing a successful reserve realization separately on
each occurring good preliminary state.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_rawResidualInternalKernel_of_directSupply
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
    (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (a D d R k : ℕ) (hD : 0 < D)
    (hsupply : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      ∀ e ∈ E,
        let S := residualInternalExtensionSet W i (A omega) e
        ((a + D : ℕ) : ℝ) ≤
          ((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card / 4)
    (hsmall : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      ∑ e ∈ E,
        (let S := residualInternalExtensionSet W i (A omega) e;
          Real.exp
            (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card) / 4)) < 1)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ omega, Good omega → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges
          (G omega) (W.U i.succ) (P0 omega)) v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    ∃ bits : Omega → Sym2 V → Bool,
      (∀ omega, Good omega →
        RawResidualInternalFiberGood W i F G A P0 bits D R omega) ∧
      ∀ omega Q,
        (rawResidualInternalKernel W i F G A P0 bits D omega).probability
          (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
            ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  classical
  have hex : ∀ omega, Good omega → ∃ bits : Sym2 V → Bool,
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      let S := residualInternalExtensionSet W i (A omega)
      let hne := residualInternalEdgeNe
        (G omega) (W.U i.succ) (P0 omega)
      let K := internalEdgeGreedyProcessLaw F (G omega) (W.U i.succ)
        bits S E.toList hne D (P0 omega)
      K.SupportedOn (fun z ↦
          InternalEdgeProcessInvariant F (P0 omega) E.toList
              E.toList.length z ∧
          z.chosen ⊆ P0 omega ∪ A omega ∧
          NewTrianglesUseScheduledOuterEdges
            (W.U i.succ) E (P0 omega) z.chosen ∧
          InternalEdgeFailureCertificate F (G omega) (W.U i.succ)
            bits S E.toList hne D E.toList.length z) ∧
        (∀ z, 0 < K.mass z → RootedActiveCapsGood F z.chosen R →
          z.failed = false ∧
            ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) := by
    intro omega hgood
    let E := preliminaryResidualInternalEdges
      (G omega) (W.U i.succ) (P0 omega)
    have hE : E ⊆ internalOuterEdges (G omega) (W.U i.succ) :=
      preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G omega) (W.U i.succ) (P0 omega)
    obtain ⟨bits, hbits⟩ :=
      exists_scheduledOuterEdge_rawLaw_terminalRootSuccess_of_directSupply
        (htri omega hgood) i E hE (hpacking0 omega hgood)
        (havoid0 omega hgood) (hinitial omega hgood) reserveRate
        hreserveRate a D d R k hD (hsupply omega hgood)
        (hsmall omega hgood) hfamily (hincidence omega hgood) hscalar
    refine ⟨bits, ?_⟩
    have hsupportSuccess := And.intro hbits.1 hbits.2.1
    simpa [E, residualInternalExtensionSet, residualInternalEdgeNe] using
      hsupportSuccess
  let bits : Omega → Sym2 V → Bool := fun omega ↦
    if hgood : Good omega then Classical.choose (hex omega hgood)
    else fun _ ↦ false
  have hbits : ∀ omega, Good omega →
      RawResidualInternalFiberGood W i F G A P0 bits D R omega := by
    intro omega hgood
    have hspec := Classical.choose_spec (hex omega hgood)
    simpa only [RawResidualInternalFiberGood, rawResidualInternalKernel,
      bits, dif_pos hgood] using hspec
  refine ⟨bits, hbits, ?_⟩
  intro omega Q
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
