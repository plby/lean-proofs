/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedCorrelatedStage
import ErdosProblems.Erdos207.LocalizedNewPreliminaryResidualInternalFixedReserveKernel

/-!
# Relative correlated stage with a newly activated terminal certificate
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The existing correlated facts, strengthened by the corrected raw
terminal certificate relative to the packing present before the whole
preliminary/internal stage. -/
structure RelativeReserveProtectedNewCorrelatedFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (level next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell) (U : Finset V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (initial later : Omega → TripleSystemOn V)
    (n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ)
    (alphaPre etaPre : ℝ≥0)
    (p reserveDensity C b p' reserveDensity' C' b' : ℝ≥0)
    extends RelativeReserveProtectedCorrelatedFacts L W level next F i U
      G A I D bits initial later n Kpair Kglobal Kinc Delta delta Icut Dcut
      d Dint R p reserveDensity C b p' reserveDensity' C' b' where
  newOutcome : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ LocalizedNewRawResidualInternalOutcomeGood W i F
      (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
      (relativeReserveProtectedAint A I D)
      (fun z ↦ I z.1 ∪ D z.1)
      (relativeReserveProtectedP0 I D)
      (fun z ↦ bits z.1) Dint R (z.1, z.2.1) z.2.2)
  combinedC4 : ∀ omega, 0 < L.mass omega → ∀ Q : TripleSystemOn V,
    (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
      Kpair Kglobal Kinc Delta delta Icut Dcut d Dint omega).probability
        (fun z ↦ Q ⊆ relativeReserveProtectedTotal I D omega z) ≤
      (alphaPre + etaPre * (Dint : ℝ≥0)⁻¹) ^ Q.card

theorem IsReserveStronglyWellDistributed.bind_relativeReserveProtectedNewCorrelatedStage
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell}
    {level next : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {initial later : Omega → TripleSystemOn V}
    {p reserveDensity C b p' reserveDensity' C' b' : ℝ≥0}
    (i : Fin ell)
    (hstrong : IsReserveStronglyWellDistributed L W level initial later
      (fun omega ↦ reserveEdges (G omega) (W.U i.succ) (bits omega))
      p reserveDensity C b)
    {etaMaster xi : ℝ≥0} {h : ℕ}
    (hpoint : L.SupportedOn fun omega ↦
      IsMasterStagePointwiseGood W level F (G omega) (A omega)
        (I omega) (D omega) p etaMaster xi h)
    (heven : L.SupportedOn fun omega ↦
      ∀ v : V, Even ((neighborsIn (G omega) univ v).card))
    (n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff R : ℕ)
    (alphaPre etaPre : ℝ≥0)
    (P : RelativeReserveProtectedPreliminaryFacts L F (W.U i.succ)
      G A I D bits n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint
      cutoff alphaPre etaPre)
    (hDint : 0 < Dint)
    (q : ℕ) (hfamily : ∀ S ∈ F, S.card ≤ q)
    (hscalar : 4 * d + R * q ≤ a)
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hlevelNext : level ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (hcombinedOne : alphaPre + etaPre * (Dint : ℝ≥0)⁻¹ ≤ 1)
    (hetaOne : etaPre ≤ 1) (hetaReserve : etaPre ≤ reserveDensity')
    (hbOne : b ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alphaPre + etaPre * (Dint : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    RelativeReserveProtectedNewCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits initial later n Kpair Kglobal Kinc Delta
      delta Icut Dcut d Dint R alphaPre etaPre
      p reserveDensity C b p' reserveDensity'
      C' b' := by
  let U := W.U i.succ
  let Kpre := relativeReserveProtectedPreliminaryKernel n F U G A I D bits
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let LP := L.jointBind Kpre
  let Plegal : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := fun z ↦ I z.1 ∪ D z.1
  let P0 : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := relativeReserveProtectedP0 I D
  let Aint : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := relativeReserveProtectedAint A I D
  let Gpre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      SimpleGraph V := fun z ↦ G z.1
  let bitsPre : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      Sym2 V → Bool := fun z ↦ bits z.1
  let Kint : Omega × FiniteLaw.TimedState (GreedyStateOn V) n →
      FiniteLaw (InternalEdgeGreedyStateOn V) :=
    relativeReserveProtectedInternalKernel W i F G A I D bits Dint
  let K : Omega → FiniteLaw
      (FiniteLaw.TimedState (GreedyStateOn V) n ×
        InternalEdgeGreedyStateOn V) :=
    relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
      Kpair Kglobal Kinc Delta delta Icut Dcut d Dint
  let Good : Omega × FiniteLaw.TimedState (GreedyStateOn V) n → Prop :=
    fun z ↦ 0 < LP.mass z
  have hmassL : ∀ z, Good z → 0 < L.mass z.1 := by
    intro z hz
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2).mp hz |>.1
  have htriInt : ∀ z, Good z → ConsistsOfTriangles (Gpre z) (Aint z) := by
    intro z hz
    exact ((hpoint z.1 (hmassL z hz)).2.2.2.2.2.1).pairSafeAvailable
  have hinitial : ∀ z, Good z → ∀ T ∈ Aint z,
      TriangleAvoidsGraph (coveredGraph (P0 z)) T := by
    intro z _ T hT
    exact pairSafeAvailable_triangleAvoids (A z.1) (P0 z) T hT
  have havailable : ∀ z, Good z → ∀ T ∈ Aint z,
      ¬ CompletesForbidden F (Plegal z) T := by
    intro z hz T hT
    exact (hpoint z.1 (hmassL z hz)).2.2.2.2.2.2 T
      (pairSafeAvailable_subset_left (A z.1) (P0 z) hT)
  have hsupply : ∀ z, Good z →
      let E := preliminaryResidualInternalEdges (Gpre z) U (P0 z)
      ∀ e ∈ E,
        a + Dint ≤ (activeReserveWedgeVertices (Gpre z) U
          (residualInternalExtensionSet W i (Aint z) e)
          e.out.1 e.out.2 (bitsPre z)).card := by
    intro z hz
    dsimp only
    intro e he
    have hbase := P.supply z hz e
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) U (P0 z) he)
    have he' : e ∈ preliminaryResidualInternalEdges (G z.1) U
        ((I z.1 ∪ D z.1) ∪
          relativeReserveProtectedPreliminaryAdded I D z.1 z.2) := by
      simpa only [P0, relativeReserveProtectedP0, union_assoc] using he
    have hmono := card_activeReserveWedgeVertices_pairSafe_ge
      (A := A z.1) (P := I z.1 ∪ D z.1)
      (M := relativeReserveProtectedPreliminaryAdded I D z.1 z.2)
      (bits := bits z.1) he'
      (hpoint z.1 (hmassL z hz)).2.2.2.2.1 (P.protectedAvailable z hz)
    exact hbase.trans (by
      simpa only [Gpre, Aint, P0, bitsPre, U,
        relativeReserveProtectedAint, relativeReserveProtectedP0,
        residualInternalExtensionSet, union_assoc] using hmono)
  have hkernel := localizedNewRawResidualInternalKernel_of_fixedReserveSupply
    Good htriInt i
      (fun z hz ↦ by
        simpa only [P0, relativeReserveProtectedP0] using P.packing z hz)
      (fun z hz ↦ by
        simpa only [P0, relativeReserveProtectedP0] using P.avoids z hz)
      hinitial havailable bitsPre a Dint d R q hDint hsupply hfamily
      (fun z hz v ↦ by
        simpa only [Gpre, P0, U, relativeReserveProtectedP0,
          union_assoc] using P.incidence z hz v)
      hscalar
  have holdFacts := hstrong.bind_relativeReserveProtectedCorrelatedStage
    i hpoint heven n Kpair Kglobal Kinc Delta delta Icut Dcut d a
      Dint cutoff R alphaPre etaPre P hDint q hfamily hscalar hnonempty
      hlevelNext hCC' hC' hpp' hpOne hreserveMono hreserveOne hcombinedOne
      hetaOne hetaReserve hbOne hbb' hnew
  refine ⟨holdFacts, ?_, ?_⟩
  · intro z hz
    have hm := (FiniteLaw.jointBind_mass_pos_iff L K z.1 z.2).mp hz
    have hmInner := (FiniteLaw.jointBind_mass_pos_iff (Kpre z.1)
      (fun xi ↦ Kint (z.1, xi)) z.2.1 z.2.2).mp (by
        simpa only [K, relativeReserveProtectedCorrelatedKernel] using hm.2)
    have hgood : Good (z.1, z.2.1) :=
      (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2.1).2
        ⟨hm.1, hmInner.1⟩
    simpa only [Gpre, Aint, Plegal, P0, bitsPre, U] using
      (hkernel.1 (z.1, z.2.1) hgood).supportedOn_outcome z.2.2 hmInner.2
  · intro omega hmass Q
    have hpreSupport : (Kpre omega).SupportedOn fun xi ↦
        RelativeGreedyTrajectory F
            (relativePreliminaryInitialState (I omega ∪ D omega)
              (reserveProtectedOuterAvailable (G omega) U
                (reserveEdges (G omega) U (bits omega)) (A omega)))
            xi.2 ∧
          Disjoint (I omega ∪ D omega)
            (relativeReserveProtectedPreliminaryAdded I D omega xi) := by
      intro xi hxi
      have hjoint := (FiniteLaw.jointBind_mass_pos_iff L Kpre omega xi).2
        ⟨hmass, hxi⟩
      exact ⟨P.trajectory (omega, xi) hjoint,
        P.oldDisjoint (omega, xi) hjoint⟩
    have hpre : ∀ Q E,
        (Kpre omega).probability (fun xi ↦
          Q ⊆ relativeReserveProtectedPreliminaryAdded I D omega xi ∧
            E ⊆ preliminaryResidualOuterEdges
              (reserveProtectedOuterGraph (G omega) U
                (reserveEdges (G omega) U (bits omega))) U
              (relativeReserveProtectedPreliminaryAdded I D omega xi)) ≤
          alphaPre ^ Q.card * etaPre ^ E.card := by
      intro Q' E
      have hmono : (Kpre omega).probability (fun xi ↦
            Q' ⊆ relativeReserveProtectedPreliminaryAdded I D omega xi ∧
              E ⊆ preliminaryResidualOuterEdges
                (reserveProtectedOuterGraph (G omega) U
                  (reserveEdges (G omega) U (bits omega))) U
                (relativeReserveProtectedPreliminaryAdded I D omega xi)) ≤
          (Kpre omega).probability (fun xi ↦
            Q' ⊆ relativeReserveProtectedPreliminaryAdded I D omega xi ∧
              E ⊆ preliminaryResidualOuterEdges
                (reserveProtectedOuterGraph (G omega) U
                  (reserveEdges (G omega) U (bits omega))) U xi.2.chosen) := by
        apply (Kpre omega).probability_mono_of_supported hpreSupport
        intro xi htraj hQE
        refine ⟨hQE.1, ?_⟩
        have hacc : (I omega ∪ D omega) ∪
              relativeReserveProtectedPreliminaryAdded I D omega xi =
            xi.2.chosen := by
          simpa only [relativeReserveProtectedPreliminaryAdded,
            relativePreliminaryInitialState_chosen] using
            htraj.1.initial_union_added
        have hleave : reserveProtectedOuterGraph (G omega) U
              (reserveEdges (G omega) U (bits omega)) ≤
            leaveGraph (I omega ∪ D omega) :=
          (reserveProtectedOuterGraph_le (G omega) U
            (reserveEdges (G omega) U (bits omega))).trans
              (hpoint omega hmass).2.2.2.2.1
        rw [← hacc,
          preliminaryResidualOuterEdges_union_eq_of_le_leaveGraph
            hleave htraj.2]
        exact hQE.2
      exact hmono.trans (P.outerProduct omega hmass Q' E)
    have hstruct : ((Kpre omega).jointBind
        (fun xi ↦ Kint (omega, xi))).SupportedOn fun z ↦
          IsPackingOn (relativeReserveProtectedTotal I D omega z) ∧
            Disjoint
              (relativeReserveProtectedPreliminaryAdded I D omega z.1)
              (relativeReserveProtectedInternalAdded I D omega z.1 z.2) ∧
            NewTrianglesUseScheduledOuterEdges U
              (preliminaryResidualInternalEdges (G omega) U
                (relativeReserveProtectedPreliminaryAdded I D omega z.1))
              (relativeReserveProtectedPreliminaryAdded I D omega z.1)
              (relativeReserveProtectedTotal I D omega z) := by
      intro z hz
      have hmInner := (FiniteLaw.jointBind_mass_pos_iff (Kpre omega)
        (fun xi ↦ Kint (omega, xi)) z.1 z.2).mp hz
      have hgood : Good (omega, z.1) :=
        (FiniteLaw.jointBind_mass_pos_iff L Kpre omega z.1).2
          ⟨hmass, hmInner.1⟩
      have hrawStruct := (hkernel.1 (omega, z.1) hgood).1 z.2 hmInner.2
      have hsubset : P0 (omega, z.1) ⊆ z.2.chosen :=
        hrawStruct.1.1.initial_subset
      have hunion : P0 (omega, z.1) ∪
          relativeReserveProtectedInternalAdded I D omega z.1 z.2 =
          z.2.chosen := by
        exact union_sdiff_of_subset hsubset
      have hpackFull : IsPackingOn
          (P0 (omega, z.1) ∪
            relativeReserveProtectedInternalAdded I D omega z.1 z.2) := by
        simpa only [hunion] using hrawStruct.1.1.isPacking
          (by simpa only [P0, relativeReserveProtectedP0] using
            P.packing (omega, z.1) hgood)
      have hdisjFull : Disjoint (P0 (omega, z.1))
          (relativeReserveProtectedInternalAdded I D omega z.1 z.2) := by
        rw [Finset.disjoint_left]
        intro T hTP hTnew
        exact (mem_sdiff.mp hTnew).2 hTP
      have hpreInt : Disjoint
          (relativeReserveProtectedPreliminaryAdded I D omega z.1)
          (relativeReserveProtectedInternalAdded I D omega z.1 z.2) :=
        hdisjFull.mono_left (by
          intro T hT
          simpa only [P0, relativeReserveProtectedP0] using
            (show T ∈ I omega ∪
                (D omega ∪ relativeReserveProtectedPreliminaryAdded I D
                  omega z.1) from
              mem_union_right _ (mem_union_right _ hT)))
      have hscheduleFull : NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges (G omega) U (P0 (omega, z.1)))
          (P0 (omega, z.1))
          (P0 (omega, z.1) ∪
            relativeReserveProtectedInternalAdded I D omega z.1 z.2) := by
        simpa only [hunion] using hrawStruct.2.2.1
      have hGleave : G omega ≤ leaveGraph (I omega ∪ D omega) :=
        (hpoint omega hmass).2.2.2.2.1
      have holdPre := P.oldDisjoint (omega, z.1) hgood
      have hschedule : preliminaryResidualInternalEdges (G omega) U
            (P0 (omega, z.1)) =
          preliminaryResidualInternalEdges (G omega) U
            (relativeReserveProtectedPreliminaryAdded I D omega z.1) := by
        simpa only [P0, relativeReserveProtectedP0, union_assoc] using
          preliminaryResidualInternalEdges_union_eq_of_le_leaveGraph
            hGleave holdPre
      refine ⟨?_, hpreInt, ?_⟩
      · exact hpackFull.mono (by
          intro T hT
          change T ∈
            relativeReserveProtectedPreliminaryAdded I D omega z.1 ∪
              relativeReserveProtectedInternalAdded I D omega z.1 z.2 at hT
          change T ∈ P0 (omega, z.1) ∪
            relativeReserveProtectedInternalAdded I D omega z.1 z.2
          rcases mem_union.mp hT with hTpre | hTint
          · apply mem_union_left
            simpa only [P0, relativeReserveProtectedP0] using
              (show T ∈ I omega ∪
                  (D omega ∪ relativeReserveProtectedPreliminaryAdded I D
                    omega z.1) from
                mem_union_right _ (mem_union_right _ hTpre))
          · exact mem_union_right _ hTint)
      · intro T hT
        have hTd := mem_sdiff.mp hT
        have hTint : T ∈
            relativeReserveProtectedInternalAdded I D omega z.1 z.2 := by
          have hTtotal := hTd.1
          change T ∈
              relativeReserveProtectedPreliminaryAdded I D omega z.1 ∪
                relativeReserveProtectedInternalAdded I D omega z.1 z.2 at hTtotal
          exact (mem_union.mp hTtotal).resolve_left hTd.2
        have hTfull : T ∈
            (P0 (omega, z.1) ∪
              relativeReserveProtectedInternalAdded I D omega z.1 z.2) \
              P0 (omega, z.1) := by
          exact mem_sdiff.mpr
            ⟨mem_union_right _ hTint, (mem_sdiff.mp hTint).2⟩
        obtain ⟨e, he, hne, w, hw, hTeq⟩ := hscheduleFull T hTfull
        exact ⟨e, by simpa only [hschedule] using he, hne, w, hw, hTeq⟩
    have hproduct :=
      (Kpre omega).jointBind_probability_protectedPreliminaryInternalCombined_le
        (fun xi ↦ Kint (omega, xi)) (G omega) U
        (reserveEdges (G omega) U (bits omega))
        (reserveEdges_subset_crossingEdges (G omega) U (bits omega))
        (relativeReserveProtectedPreliminaryAdded I D omega)
        (relativeReserveProtectedInternalAdded I D omega)
        alphaPre etaPre (Dint : ℝ≥0)⁻¹ hpre
        (fun xi Q' ↦ by
          simpa only [Kint, relativeReserveProtectedInternalKernel,
            relativeReserveProtectedInternalAdded, Gpre, Aint, P0, bitsPre]
            using hkernel.2 (omega, xi) Q')
        hstruct Q ∅
    simpa only [K, relativeReserveProtectedCorrelatedKernel,
      relativeReserveProtectedTotal, empty_subset, and_true, card_empty,
      pow_zero, mul_one] using hproduct

end

end Erdos207
