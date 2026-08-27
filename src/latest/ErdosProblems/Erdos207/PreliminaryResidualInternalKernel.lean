/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternal

/-!
# A state-dependent raw residual-internal kernel

After conditioning the preliminary outcome on bounded residual incidence, a
reserve realization may be chosen separately in every preliminary fiber.
The resulting raw kernels are defined on all fibers, so their sharp C4 bound
is unconditional.  On good fibers their support carries the retrospective
success certificate.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The extension set used for a scheduled residual internal edge. -/
abbrev residualInternalExtensionSet
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (A : TripleSystemOn V) (e : Sym2 V) : Finset V :=
  iterationExtensionVertices A
    (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)

/-- Canonical non-diagonality proof for every residual internal edge. -/
def residualInternalEdgeNe
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (P : TripleSystemOn V) :
    ∀ e, e ∈ (preliminaryResidualInternalEdges G U P).toList →
      e.out.1 ≠ e.out.2 := fun e he ↦
  out_fst_ne_snd_of_mem_graphEdges
    (internalOuterEdges_subset_graphEdges G U
      (preliminaryResidualInternalEdges_subset_internalOuterEdges G U P
        (by simpa only [Finset.mem_toList] using he)))

/-- The raw internal process scheduled only on residual internal edges. -/
def rawResidualInternalKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (D : ℕ)
    (omega : Omega) : FiniteLaw (InternalEdgeGreedyStateOn V) :=
  let E := preliminaryResidualInternalEdges
    (G omega) (W.U i.succ) (P0 omega)
  internalEdgeGreedyProcessLaw F (G omega) (W.U i.succ) (bits omega)
    (residualInternalExtensionSet W i (A omega)) E.toList
    (residualInternalEdgeNe (G omega) (W.U i.succ) (P0 omega)) D
    (P0 omega)

/-- The genuinely new part of a raw internal outcome. -/
def rawResidualInternalAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (P0 : Omega → TripleSystemOn V) (omega : Omega)
    (z : InternalEdgeGreedyStateOn V) : TripleSystemOn V :=
  z.chosen \ P0 omega

/-- Full support certificate on one good preliminary fiber. -/
def RawResidualInternalFiberGood
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (D R : ℕ) (omega : Omega) : Prop :=
  let E := preliminaryResidualInternalEdges
    (G omega) (W.U i.succ) (P0 omega)
  let S := residualInternalExtensionSet W i (A omega)
  let hne := residualInternalEdgeNe
    (G omega) (W.U i.succ) (P0 omega)
  let K := rawResidualInternalKernel W i F G A P0 bits D omega
  K.SupportedOn (fun z ↦
      InternalEdgeProcessInvariant F (P0 omega) E.toList E.toList.length z ∧
      z.chosen ⊆ P0 omega ∪ A omega ∧
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E (P0 omega) z.chosen ∧
      InternalEdgeFailureCertificate F (G omega) (W.U i.succ)
        (bits omega) S E.toList hne D E.toList.length z) ∧
    ∀ z, 0 < K.mass z → RootedActiveCapsGood F z.chosen R →
      z.failed = false ∧
        ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2

/-- The structural and retrospective certificate carried by one occurring
raw internal outcome. -/
def RawResidualInternalOutcomeGood
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A P0 : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (D R : ℕ)
    (omega : Omega) (z : InternalEdgeGreedyStateOn V) : Prop :=
  let E := preliminaryResidualInternalEdges
    (G omega) (W.U i.succ) (P0 omega)
  let S := residualInternalExtensionSet W i (A omega)
  let hne := residualInternalEdgeNe
    (G omega) (W.U i.succ) (P0 omega)
  InternalEdgeProcessInvariant F (P0 omega) E.toList E.toList.length z ∧
    z.chosen ⊆ P0 omega ∪ A omega ∧
    NewTrianglesUseScheduledOuterEdges
      (W.U i.succ) E (P0 omega) z.chosen ∧
    InternalEdgeFailureCertificate F (G omega) (W.U i.succ)
      (bits omega) S E.toList hne D E.toList.length z ∧
    (RootedActiveCapsGood F z.chosen R →
      z.failed = false ∧
        ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2)

theorem RawResidualInternalFiberGood.supportedOn_outcome
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ} {omega : Omega}
    (hgood : RawResidualInternalFiberGood W i F G A P0 bits D R omega) :
    (rawResidualInternalKernel W i F G A P0 bits D omega).SupportedOn
      (RawResidualInternalOutcomeGood W i F G A P0 bits D R omega) := by
  intro z hz
  have hstruct := hgood.1 z hz
  exact ⟨hstruct.1, hstruct.2.1, hstruct.2.2.1, hstruct.2.2.2,
    hgood.2 z hz⟩

/-- Pointwise reserve choice on every good preliminary outcome.  No choice is
needed on bad outcomes; they receive the all-false reserve realization. -/
theorem exists_rawResidualInternalKernel
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V] {ell : ℕ} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (Good : Omega → Prop)
    (htyp : ∀ omega, Good omega →
      IsIterationTypical W stage (G omega) (A omega) p eta xi h)
    (htri : ∀ omega, Good omega → ConsistsOfTriangles (G omega) (A omega))
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : ∀ omega, Good omega →
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hpacking0 : ∀ omega, Good omega → IsPackingOn (P0 omega))
    (havoid0 : ∀ omega, Good omega → AvoidsForbidden (P0 omega) F)
    (hinitial : ∀ omega, Good omega →
      ∀ T ∈ A omega, TriangleAvoidsGraph (coveredGraph (P0 omega)) T)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a D d R k : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P0 omega)
      (E.card : ℝ) * Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
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
      (htyp omega hgood).exists_scheduledOuterEdge_rawLaw_terminalRootSuccess
        (htri omega hgood) i hstage (hGsupp omega hgood) E hE
        (hpacking0 omega hgood) (havoid0 omega hgood)
        (hinitial omega hgood) hh r hr m a D d R k hD hm ha
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
