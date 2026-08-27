/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeCorrelatedComposition
import ErdosProblems.Erdos207.RelativeReserveProtectedPreliminaryStage
import ErdosProblems.Erdos207.LocalizedPreliminaryResidualInternalFixedReserveKernel

/-!
# The correlated reserve-protected stage relative to an old packing

This is the later-stage analogue of `ReserveProtectedCorrelatedStage`.
The old master `I/D` split is retained, and only the genuinely new
preliminary and internal differences are charged at the sharp combined base
`alphaPre + etaPre * D⁻¹`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

def relativeReserveProtectedP0
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (I D : Omega → TripleSystemOn V)
    (z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n) :
    TripleSystemOn V :=
  I z.1 ∪ (D z.1 ∪ relativeReserveProtectedPreliminaryAdded I D z.1 z.2)

def relativeReserveProtectedAint
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (A I D : Omega → TripleSystemOn V)
    (z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n) :
    TripleSystemOn V :=
  pairSafeAvailable (A z.1) (relativeReserveProtectedP0 I D z)

def relativeReserveProtectedInternalKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool) (Dint : ℕ)
    (z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n) :
    FiniteLaw (InternalEdgeGreedyStateOn V) :=
  rawResidualInternalKernel W i F (fun z ↦ G z.1)
    (relativeReserveProtectedAint A I D) (relativeReserveProtectedP0 I D)
    (fun z ↦ bits z.1) Dint z

def relativeReserveProtectedInternalAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (I D : Omega → TripleSystemOn V)
    (omega : Omega) (xi : FiniteLaw.TimedState (GreedyStateOn V) n)
    (z : InternalEdgeGreedyStateOn V) : TripleSystemOn V :=
  rawResidualInternalAdded (relativeReserveProtectedP0 I D) (omega, xi) z

def relativeReserveProtectedTotal
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    (I D : Omega → TripleSystemOn V) (omega : Omega)
    (z : FiniteLaw.TimedState (GreedyStateOn V) n ×
      InternalEdgeGreedyStateOn V) : TripleSystemOn V :=
  preliminaryInternalCombinedAdded
    (relativeReserveProtectedPreliminaryAdded I D omega)
    (relativeReserveProtectedInternalAdded I D omega) z

def relativeReserveProtectedCorrelatedKernel
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (U : Finset V) (G : Omega → SimpleGraph V)
    (A I D : Omega → TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint : ℕ)
    (omega : Omega) : FiniteLaw
      (FiniteLaw.TimedState (GreedyStateOn V) n ×
        InternalEdgeGreedyStateOn V) :=
  let Kpre := relativeReserveProtectedPreliminaryKernel n F U G A I D bits
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let Kint := relativeReserveProtectedInternalKernel (n := n)
    W i F G A I D bits Dint
  (Kpre omega).jointBind fun xi ↦ Kint (omega, xi)

/-- The internal-edge sample does not alter the preliminary marginal.  Thus
the preliminary C4 bound supplied by the protected preliminary stage remains
valid for the complete correlated sample. -/
theorem RelativeReserveProtectedPreliminaryFacts.probability_correlated_preliminary_subset_le
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} {F : ForbiddenFamilyOn V}
    {U : Finset V} {G : Omega → SimpleGraph V}
    {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {n Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff : ℕ}
    {alphaPre etaPre : ℝ≥0}
    (i : Fin ell)
    (P : RelativeReserveProtectedPreliminaryFacts L F U G A I D bits n
      Kpair Kglobal Kinc Delta delta Icut Dcut d a Dint cutoff
      alphaPre etaPre)
    (Q : TripleSystemOn V) :
    (L.jointBind (relativeReserveProtectedCorrelatedKernel W i F U G A I D
      bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).probability
        (fun z ↦ Q ⊆
          relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1) ≤
      alphaPre ^ Q.card := by
  let Kpre := relativeReserveProtectedPreliminaryKernel n F U G A I D bits
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let Kint := relativeReserveProtectedInternalKernel (n := n)
    W i F G A I D bits Dint
  have hbound :
      (L.jointBind (fun omega ↦
        (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi)))).probability
          (fun z ↦ Q ⊆
            relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1) ≤
        alphaPre ^ Q.card := by
    apply L.jointBind_jointBind_probability_snd_fst_le_on_support
      Kpre (fun omega xi ↦ Kint (omega, xi))
      (fun omega xi ↦ Q ⊆
        relativeReserveProtectedPreliminaryAdded I D omega xi)
      (alphaPre ^ Q.card)
    intro omega hmass
    have hraw := P.outerProduct omega hmass Q ∅
    simpa only [Kpre, empty_subset, and_true, card_empty, pow_zero,
      mul_one] using hraw
  change (L.jointBind (fun omega ↦
    (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi)))).probability
      (fun z ↦ Q ⊆
        relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1) ≤
    alphaPre ^ Q.card
  exact hbound

/-- The reusable output of one relative correlated stage. -/
structure RelativeReserveProtectedCorrelatedFacts
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    (L : FiniteLaw Omega) (W : Vortex V ell) (level next : Fin (ell + 1))
    (F : ForbiddenFamilyOn V) (i : Fin ell) (U : Finset V)
    (G : Omega → SimpleGraph V) (A I D : Omega → TripleSystemOn V)
    (bits : Omega → Sym2 V → Bool)
    (initial later : Omega → TripleSystemOn V)
    (n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint R : ℕ)
    (p reserveDensity C b p' reserveDensity' C' b' : ℝ≥0) where
  strong :
    IsReserveStronglyWellDistributed
      (L.jointBind (relativeReserveProtectedCorrelatedKernel W i F U G A I D
        bits n Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)) W next
      (jointInitial initial)
      (jointLater later (relativeReserveProtectedTotal I D))
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U
        (reserveEdges (G z.1) U (bits z.1))
        (relativeReserveProtectedTotal I D z.1 z.2))
      p' reserveDensity' (2 * C') b'
  outcome : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ LocalizedRawResidualInternalOutcomeGood W i F
      (fun z : Omega × FiniteLaw.TimedState (GreedyStateOn V) n ↦ G z.1)
      (relativeReserveProtectedAint A I D) (relativeReserveProtectedP0 I D)
      (fun z ↦ bits z.1) Dint R (z.1, z.2.1) z.2.2)
  preliminaryCard : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1).card ≤ n)
  preliminaryAtMostOne : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ TrianglesMeetAtMostOne U
      (relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1))
  incidence : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ ∀ v : V, (scheduledEdgesAt
      (preliminaryResidualInternalEdges (G z.1) U
        (relativeReserveProtectedP0 I D (z.1, z.2.1))) v).card ≤ d)
  accumulate : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ I z.1 ∪ (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2) =
      z.2.2.chosen)
  selected : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ relativeReserveProtectedTotal I D z.1 z.2 ⊆ A z.1)
  disjoint : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ Disjoint (I z.1) (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2))
  packing : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ IsPackingOn
      (I z.1 ∪ (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2)))
  avoids : (L.jointBind
      (relativeReserveProtectedCorrelatedKernel W i F U G A I D bits n
        Kpair Kglobal Kinc Delta delta Icut Dcut d Dint)).SupportedOn
    (fun z ↦ AvoidsForbidden
      (I z.1 ∪ (D z.1 ∪ relativeReserveProtectedTotal I D z.1 z.2)) F)

/-- Attach the fixed-reserve internal kernel to the relative preliminary
package and update the reserve-aware strong law at the sharp correlated
scale. -/
theorem IsReserveStronglyWellDistributed.bind_relativeReserveProtectedCorrelatedStage
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
    RelativeReserveProtectedCorrelatedFacts L W level next F i
      (W.U i.succ) G A I D bits initial later n Kpair Kglobal Kinc Delta
      delta Icut Dcut d Dint R p reserveDensity C b p' reserveDensity'
      C' b' := by
  let U := W.U i.succ
  let Kpre := relativeReserveProtectedPreliminaryKernel n F U G A I D bits
    Kpair Kglobal Kinc Delta delta Icut Dcut d
  let LP := L.jointBind Kpre
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
  let addedPre : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      TripleSystemOn V := relativeReserveProtectedPreliminaryAdded I D
  let addedInt : Omega → FiniteLaw.TimedState (GreedyStateOn V) n →
      InternalEdgeGreedyStateOn V → TripleSystemOn V :=
    relativeReserveProtectedInternalAdded I D
  let total : Omega →
      (FiniteLaw.TimedState (GreedyStateOn V) n ×
        InternalEdgeGreedyStateOn V) → TripleSystemOn V :=
    relativeReserveProtectedTotal I D
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
        ((I z.1 ∪ D z.1) ∪ addedPre z.1 z.2) := by
      simpa only [P0, relativeReserveProtectedP0, union_assoc] using he
    have hmono := card_activeReserveWedgeVertices_pairSafe_ge
      (A := A z.1) (P := I z.1 ∪ D z.1)
      (M := addedPre z.1 z.2) (bits := bits z.1) he'
      (hpoint z.1 (hmassL z hz)).2.2.2.2.1 (P.protectedAvailable z hz)
    exact hbase.trans (by
      simpa only [Gpre, Aint, P0, bitsPre, U,
        relativeReserveProtectedAint, relativeReserveProtectedP0,
        residualInternalExtensionSet, union_assoc] using hmono)
  have hkernel := localizedRawResidualInternalKernel_of_fixedReserveSupply
    Good htriInt i
      (fun z hz ↦ by
        simpa only [P0, relativeReserveProtectedP0] using P.packing z hz)
      (fun z hz ↦ by
        simpa only [P0, relativeReserveProtectedP0] using P.avoids z hz)
      hinitial bitsPre a Dint d R q hDint hsupply hfamily
      (fun z hz v ↦ by
        simpa only [Gpre, P0, U, relativeReserveProtectedP0,
          union_assoc] using P.incidence z hz v)
      hscalar
  have hstruct : ∀ omega, 0 < L.mass omega →
      ((Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))).SupportedOn
        (fun z ↦
          IsPackingOn ((I omega ∪ D omega) ∪ total omega z) ∧
          Disjoint (I omega ∪ D omega) (total omega z) ∧
          Disjoint (addedPre omega z.1) (addedInt omega z.1 z.2) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges (G omega) U
              ((I omega ∪ D omega) ∪ addedPre omega z.1))
            ((I omega ∪ D omega) ∪ addedPre omega z.1)
            ((I omega ∪ D omega) ∪ total omega z)) := by
    intro omega hmass z hz
    have hm := (FiniteLaw.jointBind_mass_pos_iff (Kpre omega)
      (fun xi ↦ Kint (omega, xi)) z.1 z.2).mp hz
    have hgood : Good (omega, z.1) :=
      (FiniteLaw.jointBind_mass_pos_iff L Kpre omega z.1).2 ⟨hmass, hm.1⟩
    have hrawStruct := (hkernel.1 (omega, z.1) hgood).1 z.2 hm.2
    have hsubset : P0 (omega, z.1) ⊆ z.2.chosen :=
      hrawStruct.1.1.initial_subset
    have hunion : P0 (omega, z.1) ∪ addedInt omega z.1 z.2 =
        z.2.chosen := by
      exact union_sdiff_of_subset hsubset
    have hraw :
        IsPackingOn (P0 (omega, z.1) ∪ addedInt omega z.1 z.2) ∧
        Disjoint (P0 (omega, z.1)) (addedInt omega z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges (Gpre (omega, z.1)) U
            (P0 (omega, z.1)))
          (P0 (omega, z.1))
          (P0 (omega, z.1) ∪ addedInt omega z.1 z.2) := by
      refine ⟨?_, ?_, ?_⟩
      · simpa only [hunion] using hrawStruct.1.1.isPacking
          (by simpa only [P0, relativeReserveProtectedP0] using
            P.packing (omega, z.1) hgood)
      · rw [Finset.disjoint_left]
        intro T hTP hTnew
        exact (mem_sdiff.mp hTnew).2 hTP
      · simpa only [U, hunion] using hrawStruct.2.2.1
    have holdPre := P.oldDisjoint (omega, z.1) hgood
    have holdRaw : Disjoint (I omega ∪ D omega) (addedInt omega z.1 z.2) :=
      hraw.2.1.mono_left (by
        intro T hT
        rcases mem_union.mp hT with hTI | hTD
        · simpa only [P0, relativeReserveProtectedP0] using
            (mem_union_left (D omega ∪ addedPre omega z.1) hTI)
        · simpa only [P0, relativeReserveProtectedP0] using
            (mem_union_right (I omega)
              (mem_union_left (addedPre omega z.1) hTD)))
    have hpreRaw : Disjoint (addedPre omega z.1) (addedInt omega z.1 z.2) :=
      hraw.2.1.mono_left (by
        intro T hT
        simpa only [P0, relativeReserveProtectedP0] using
          (show T ∈ I omega ∪ (D omega ∪ addedPre omega z.1) from
            mem_union_right _ (mem_union_right _ hT)))
    refine ⟨?_, ?_, hpreRaw, ?_⟩
    · simpa only [P0, relativeReserveProtectedP0, total,
        addedInt, relativeReserveProtectedInternalAdded,
        relativeReserveProtectedTotal, preliminaryInternalCombinedAdded,
        union_assoc] using hraw.1
    · change Disjoint (I omega ∪ D omega)
        (addedPre omega z.1 ∪ addedInt omega z.1 z.2)
      rw [disjoint_union_right]
      exact ⟨holdPre, holdRaw⟩
    · simpa only [Gpre, P0, relativeReserveProtectedP0, total, addedInt,
        relativeReserveProtectedTotal,
        relativeReserveProtectedInternalAdded,
        preliminaryInternalCombinedAdded, union_assoc] using hraw.2.2
  have hstrong' :=
    hstrong.jointBind_relativeProtectedPreliminaryInternal_of_numeric
      addedPre addedInt
      (fun omega hmass ↦ (hpoint omega hmass).2.2.2.2.1)
      (fun omega ↦ reserveEdges_subset_crossingEdges
        (G omega) U (bits omega))
      (by
        intro omega hmass Q E
        have hsupp : (Kpre omega).SupportedOn fun xi ↦
            RelativeGreedyTrajectory F
              (relativePreliminaryInitialState (I omega ∪ D omega)
                (reserveProtectedOuterAvailable (G omega) U
                  (reserveEdges (G omega) U (bits omega)) (A omega)))
              xi.2 := by
          intro xi hxi
          exact P.trajectory (omega, xi)
            ((FiniteLaw.jointBind_mass_pos_iff L Kpre omega xi).2
              ⟨hmass, hxi⟩)
        have hmono : (Kpre omega).probability (fun xi ↦
              Q ⊆ addedPre omega xi ∧
                E ⊆ preliminaryResidualOuterEdges
                  (reserveProtectedOuterGraph (G omega) U
                    (reserveEdges (G omega) U (bits omega))) U
                  ((I omega ∪ D omega) ∪ addedPre omega xi)) ≤
            (Kpre omega).probability (fun xi ↦
              Q ⊆ relativeReserveProtectedPreliminaryAdded I D omega xi ∧
                E ⊆ preliminaryResidualOuterEdges
                  (reserveProtectedOuterGraph (G omega) U
                    (reserveEdges (G omega) U (bits omega))) U
                  xi.2.chosen) := by
          apply (Kpre omega).probability_mono_of_supported hsupp
          intro xi htraj hQE
          refine ⟨?_, ?_⟩
          · simpa only [addedPre] using hQE.1
          · have hacc : (I omega ∪ D omega) ∪ addedPre omega xi =
                xi.2.chosen := by
              simpa only [addedPre,
                relativeReserveProtectedPreliminaryAdded,
                relativePreliminaryInitialState_chosen] using
                htraj.initial_union_added
            simpa only [hacc] using hQE.2
        exact hmono.trans (P.outerProduct omega hmass Q E))
      (fun omega xi Q ↦ by
        simpa only [Kint, addedInt,
          relativeReserveProtectedInternalKernel,
          relativeReserveProtectedInternalAdded, Gpre, Aint, P0, bitsPre]
          using hkernel.2 (omega, xi) Q)
      hstruct hnonempty hlevelNext hCC' hC'
      hpp' hpOne hreserveMono hreserveOne hcombinedOne hetaOne
      hetaReserve hbOne hbb' hnew
  have houtcome : (L.jointBind K).SupportedOn fun z ↦
      LocalizedRawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre Dint R
        (z.1, z.2.1) z.2.2 := by
    intro z hz
    have hm := (FiniteLaw.jointBind_mass_pos_iff L K z.1 z.2).mp hz
    have hmInner := (FiniteLaw.jointBind_mass_pos_iff (Kpre z.1)
      (fun xi ↦ Kint (z.1, xi)) z.2.1 z.2.2).mp (by
        simpa only [K, relativeReserveProtectedCorrelatedKernel] using hm.2)
    have hgood : Good (z.1, z.2.1) :=
      (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2.1).2
        ⟨hm.1, hmInner.1⟩
    exact (hkernel.1 (z.1, z.2.1) hgood).supportedOn_outcome
      z.2.2 hmInner.2
  have hgoodJoint : ∀ z, 0 < (L.jointBind K).mass z →
      Good (z.1, z.2.1) := by
    intro z hz
    have hm := (FiniteLaw.jointBind_mass_pos_iff L K z.1 z.2).mp hz
    have hmInner := (FiniteLaw.jointBind_mass_pos_iff (Kpre z.1)
      (fun xi ↦ Kint (z.1, xi)) z.2.1 z.2.2).mp (by
        simpa only [K, relativeReserveProtectedCorrelatedKernel] using hm.2)
    exact (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2.1).2
      ⟨hm.1, hmInner.1⟩
  have hpreliminaryCard : (L.jointBind K).SupportedOn fun z ↦
      (addedPre z.1 z.2.1).card ≤ n := by
    intro z hz
    exact P.addedCard (z.1, z.2.1) (hgoodJoint z hz)
  have hpreliminaryAtMostOne : (L.jointBind K).SupportedOn fun z ↦
      TrianglesMeetAtMostOne U (addedPre z.1 z.2.1) := by
    intro z hz
    exact P.atMostOne (z.1, z.2.1) (hgoodJoint z hz)
  have hincidence : (L.jointBind K).SupportedOn fun z ↦
      ∀ v : V, (scheduledEdgesAt
        (preliminaryResidualInternalEdges (G z.1) U
          (P0 (z.1, z.2.1))) v).card ≤ d := by
    intro z hz v
    simpa only [P0, relativeReserveProtectedP0, union_assoc] using
      P.incidence (z.1, z.2.1) (hgoodJoint z hz) v
  have haccumulate : (L.jointBind K).SupportedOn fun z ↦
      I z.1 ∪ (D z.1 ∪ total z.1 z.2) = z.2.2.chosen := by
    intro z hz
    have hgood := hgoodJoint z hz
    have hout := houtcome z hz
    have hsubset : P0 (z.1, z.2.1) ⊆ z.2.2.chosen :=
      hout.1.1.initial_subset
    have hunion : P0 (z.1, z.2.1) ∪
        addedInt z.1 z.2.1 z.2.2 = z.2.2.chosen :=
      union_sdiff_of_subset hsubset
    simpa only [P0, relativeReserveProtectedP0, total,
      relativeReserveProtectedTotal,
      preliminaryInternalCombinedAdded, union_assoc] using hunion
  have hselected : (L.jointBind K).SupportedOn fun z ↦
      total z.1 z.2 ⊆ A z.1 := by
    intro z hz T hT
    have hgood := hgoodJoint z hz
    rcases mem_union.mp hT with hTpre | hTint
    · exact P.selected (z.1, z.2.1) hgood hTpre
    · have hout := houtcome z hz
      have hchosen := hout.2.1 (mem_sdiff.mp hTint).1
      rcases mem_union.mp hchosen with hTP0 | hTAint
      · exact (mem_sdiff.mp hTint).2 hTP0 |>.elim
      · exact pairSafeAvailable_subset_left (A z.1)
          (P0 (z.1, z.2.1)) hTAint
  have hdisjoint : (L.jointBind K).SupportedOn fun z ↦
      Disjoint (I z.1) (D z.1 ∪ total z.1 z.2) := by
    intro z hz
    have hgood := hgoodJoint z hz
    have holdPre := P.oldDisjoint (z.1, z.2.1) hgood
    have hraw := houtcome z hz
    have hrawDisj : Disjoint (P0 (z.1, z.2.1))
        (addedInt z.1 z.2.1 z.2.2) := by
      rw [Finset.disjoint_left]
      intro T hTP0 hTnew
      exact (mem_sdiff.mp hTnew).2 hTP0
    change Disjoint (I z.1)
      (D z.1 ∪ (addedPre z.1 z.2.1 ∪ addedInt z.1 z.2.1 z.2.2))
    rw [disjoint_union_right, disjoint_union_right]
    refine ⟨(hpoint z.1 (hmassL (z.1, z.2.1) hgood)).1,
      holdPre.mono_left subset_union_left, ?_⟩
    exact hrawDisj.mono_left (by
      intro T hTI
      exact mem_union_left _ hTI)
  have hpacking : (L.jointBind K).SupportedOn fun z ↦
      IsPackingOn (I z.1 ∪ (D z.1 ∪ total z.1 z.2)) := by
    intro z hz
    rw [haccumulate z hz]
    exact (houtcome z hz).1.1.isPacking
      (by simpa only [P0, relativeReserveProtectedP0] using
        P.packing (z.1, z.2.1) (hgoodJoint z hz))
  have havoids : (L.jointBind K).SupportedOn fun z ↦
      AvoidsForbidden (I z.1 ∪ (D z.1 ∪ total z.1 z.2)) F := by
    intro z hz
    rw [haccumulate z hz]
    exact (houtcome z hz).1.1.avoidsForbidden
      (by simpa only [P0, relativeReserveProtectedP0] using
        P.avoids (z.1, z.2.1) (hgoodJoint z hz))
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · change IsReserveStronglyWellDistributed
      (L.jointBind (fun omega ↦
        (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi)))) W next
      (jointInitial initial)
      (jointLater later (fun omega z ↦
        preliminaryInternalCombinedAdded
          (addedPre omega) (addedInt omega) z))
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U
        (reserveEdges (G z.1) U (bits z.1))
        (preliminaryInternalCombinedAdded
          (addedPre z.1) (addedInt z.1) z.2))
      p' reserveDensity' (2 * C') b'
    exact hstrong'
  · simpa only [K, Gpre, Aint, P0, bitsPre,
      relativeReserveProtectedCorrelatedKernel] using houtcome
  · simpa only [K, addedPre,
      relativeReserveProtectedCorrelatedKernel] using hpreliminaryCard
  · simpa only [K, addedPre,
      relativeReserveProtectedCorrelatedKernel] using hpreliminaryAtMostOne
  · simpa only [K, P0,
      relativeReserveProtectedCorrelatedKernel] using hincidence
  · simpa only [K, total, relativeReserveProtectedCorrelatedKernel] using
      haccumulate
  · simpa only [K, total, relativeReserveProtectedCorrelatedKernel] using
      hselected
  · simpa only [K, total, relativeReserveProtectedCorrelatedKernel] using
      hdisjoint
  · simpa only [K, total, relativeReserveProtectedCorrelatedKernel] using
      hpacking
  · simpa only [K, total, relativeReserveProtectedCorrelatedKernel] using
      havoids

end

end Erdos207
