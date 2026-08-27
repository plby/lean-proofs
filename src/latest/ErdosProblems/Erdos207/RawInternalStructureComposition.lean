/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeRawInternalStructure
import ErdosProblems.Erdos207.RawInternalReserveDegreeSuccess
import ErdosProblems.Erdos207.ResidualCorrelatedInternalLaw

/-! # Actual correlated raw internal kernels preserve global structure before success -/

namespace Erdos207

open Finset
open scoped Classical NNReal

noncomputable section

theorem RawResidualInternalStructure.relative_added_structure
    {Omega V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {threshold : ℕ} {omega : Omega}
    {z : InternalEdgeGreedyStateOn V}
    (hz : RawResidualInternalStructure W i F G A P0 bits threshold omega z)
    (P pre : TripleSystemOn V) (hstart : P0 omega = P ∪ pre)
    (hpacking : IsPackingOn (P0 omega)) (havoid : AvoidsForbidden (P0 omega) F)
    (hdis : Disjoint P pre) (hG : G omega ≤ leaveGraph P) :
    let added := pre ∪ rawResidualInternalAdded P0 omega z
    rawResidualInternalAdded P0 omega z ⊆ A omega ∧ IsPackingOn (P ∪ added) ∧
      Disjoint P added ∧ Disjoint pre (rawResidualInternalAdded P0 omega z) ∧
      AvoidsForbidden (P ∪ added) F ∧
      NewTrianglesUseScheduledOuterEdges (W.U i.succ)
        (preliminaryResidualInternalEdges (G omega) (W.U i.succ) pre) pre added := by
  dsimp only
  have hsubset := hz.1.1.initial_subset
  have hunion : P ∪ (pre ∪ rawResidualInternalAdded P0 omega z) = z.chosen := by
    rw [← union_assoc, ← hstart]
    exact union_sdiff_of_subset hsubset
  have hnew : rawResidualInternalAdded P0 omega z ⊆ A omega := by
    intro T hT
    exact (mem_union.mp (hz.2.1 (mem_sdiff.mp hT).1)).resolve_left (mem_sdiff.mp hT).2
  have hdisnew : Disjoint (P0 omega) (rawResidualInternalAdded P0 omega z) :=
    disjoint_left.mpr (fun _ hT hnew ↦ (mem_sdiff.mp hnew).2 hT)
  have hPnew : Disjoint P (rawResidualInternalAdded P0 omega z) :=
    hdisnew.mono_left (hstart.symm ▸ subset_union_left)
  have hprenew : Disjoint pre (rawResidualInternalAdded P0 omega z) :=
    hdisnew.mono_left (hstart.symm ▸ subset_union_right)
  have hPadded : Disjoint P (pre ∪ rawResidualInternalAdded P0 omega z) :=
    disjoint_union_right.mpr ⟨hdis, hPnew⟩
  refine ⟨hnew, hunion.symm ▸ hz.1.1.isPacking hpacking, hPadded, hprenew,
    hunion.symm ▸ hz.1.1.avoidsForbidden havoid, ?_⟩
  apply NewTrianglesUseScheduledOuterEdges.remove_old hG hPadded subset_union_left
  simpa only [hunion, ← hstart] using hz.2.2.1

def correlatedRawInternalStart
    {Omega Xi V : Type*} [DecidableEq V]
    (old : Omega → TripleSystemOn V) (pre : Omega → Xi → TripleSystemOn V)
    (z : Omega × Xi) : TripleSystemOn V := old z.1 ∪ pre z.1 z.2

def correlatedRawInternalKernel
    {Omega Xi V : Type*} [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A old : Omega → TripleSystemOn V)
    (pre : Omega → Xi → TripleSystemOn V) (bits : Omega → Sym2 V → Bool) (threshold : ℕ)
    (omega : Omega) (xi : Xi) : FiniteLaw (InternalEdgeGreedyStateOn V) :=
  rawResidualInternalKernel W i F (fun z : Omega × Xi ↦ G z.1)
    (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
    (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) threshold (omega, xi)

def correlatedRawInternalAdded
    {Omega Xi V : Type*} [Fintype V] [DecidableEq V]
    (old : Omega → TripleSystemOn V) (pre : Omega → Xi → TripleSystemOn V)
    (omega : Omega) (xi : Xi) (z : InternalEdgeGreedyStateOn V) : TripleSystemOn V :=
  rawResidualInternalAdded (correlatedRawInternalStart old pre) (omega, xi) z

theorem correlatedRawInternalKernel_supported_structure
    {Omega Xi V : Type*} [Fintype Xi] [DecidableEq Xi] [Fintype V] [DecidableEq V] {ell : ℕ}
    (W : Vortex V ell) (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A old : Omega → TripleSystemOn V)
    (pre : Omega → Xi → TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (threshold : ℕ) (hthreshold : 0 < threshold) (Kpre : Omega → FiniteLaw Xi) (omega : Omega)
    (hG : G omega ≤ leaveGraph (old omega))
    (hpre : (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn (old omega ∪ pre omega xi) ∧ Disjoint (old omega) (pre omega xi) ∧
      AvoidsForbidden (old omega ∪ pre omega xi) F) :
    ((Kpre omega).jointBind (correlatedRawInternalKernel W i F G A old pre bits threshold omega)).SupportedOn
      fun z ↦
        let added := preliminaryInternalCombinedAdded (pre omega) (correlatedRawInternalAdded old pre omega) z
        added ⊆ A omega ∧ IsPackingOn (old omega ∪ added) ∧ Disjoint (old omega) added ∧
          Disjoint (pre omega z.1) (correlatedRawInternalAdded old pre omega z.1 z.2) ∧
          AvoidsForbidden (old omega ∪ added) F ∧
          NewTrianglesUseScheduledOuterEdges (W.U i.succ)
            (preliminaryResidualInternalEdges (G omega) (W.U i.succ) (pre omega z.1))
            (pre omega z.1) added := by
  intro z hz
  have hmasses := ((Kpre omega).jointBind_mass_pos_iff
    (correlatedRawInternalKernel W i F G A old pre bits threshold omega) z.1 z.2).mp hz
  have hpreData := hpre z.1 hmasses.1
  have hraw := rawResidualInternalKernel_supported_structure W i F
    (fun z : Omega × Xi ↦ G z.1)
    (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
    (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) threshold hthreshold
    (omega, z.1) z.2 hmasses.2
  have hstruct := hraw.relative_added_structure (old omega) (pre omega z.1) rfl
    hpreData.2.1 hpreData.2.2.2 hpreData.2.2.1 hG
  refine ⟨union_subset hpreData.1 (hstruct.1.trans (pairSafeAvailable_subset_left _ _)),
    hstruct.2⟩

theorem IsResidualReserveStronglyWellDistributed.jointBind_raw_correlatedInternal
    {Omega Xi V : Type*} [Fintype Omega] [DecidableEq Omega] [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {W : Vortex V ell} (i : Fin ell) (F : ForbiddenFamilyOn V)
    (G : Omega → SimpleGraph V) (A : Omega → TripleSystemOn V)
    (initial later : Omega → TripleSystemOn V) (bits : Omega → Sym2 V → Bool)
    (Gamma : SimpleGraph V) {p r C beta : ℝ≥0}
    (hstrong : IsResidualReserveStronglyWellDistributed L W i.castSucc Gamma initial later
      (fun omega ↦ reserveEdges (G omega) (W.U i.succ) (bits omega)) p r C beta)
    (Kpre : Omega → FiniteLaw Xi) (pre : Omega → Xi → TripleSystemOn V)
    (survival point constant mu alpha eta J factor error r' : ℝ≥0)
    (hmu : 512 ≤ mu) (hC : 1 ≤ C) (hJ : 1 ≤ J) (hfactor : 1 ≤ factor)
    (halpha : alpha ≤ 1) (heta : eta ≤ 1) (hr : r ≤ r') (hetar : eta ≤ r')
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hnew : alpha * p ^ 3 ≤ factor * (p / ((W.U i.castSucc).card : ℝ≥0)))
    (hmixed : ∀ omega, 0 < L.mass omega → IsGraphMixedProductBound (Kpre omega) (pre omega)
      (reserveProtectedOuterGraph (G omega) (W.U i.succ)
        (reserveEdges (G omega) (W.U i.succ) (bits omega))) survival point constant error)
    (halphaBound : constant * point + (constant * survival) * (64 / mu) ≤ alpha)
    (hetaBound : constant * survival ≤ eta) (hconstant : 2 * constant ≤ J)
    (hG : ∀ omega, 0 < L.mass omega → G omega ≤ leaveGraph (initial omega ∪ later omega))
    (hpre : ∀ omega, 0 < L.mass omega → (Kpre omega).SupportedOn fun xi ↦ pre omega xi ⊆ A omega ∧
      IsPackingOn ((initial omega ∪ later omega) ∪ pre omega xi) ∧
      Disjoint (initial omega ∪ later omega) (pre omega xi) ∧
      AvoidsForbidden ((initial omega ∪ later omega) ∪ pre omega xi) F)
    (htri : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega, tripleEdgeFinset T ⊆ graphEdges Gamma)
    (hsupport : ∀ omega, 0 < L.mass omega → ∀ T ∈ A omega, T.1 ⊆ W.U i.castSucc) :
    let old := fun omega ↦ initial omega ∪ later omega
    let Kint := correlatedRawInternalKernel W i F G A old pre bits ⌊mu / 32⌋₊
    let intAdded := correlatedRawInternalAdded old pre
    let kernel := fun omega ↦ (Kpre omega).jointBind (Kint omega)
    let added := fun omega z ↦ preliminaryInternalCombinedAdded (pre omega) (intAdded omega) z
    IsResidualReserveStronglyWellDistributed (L.jointBind kernel) W i.castSucc Gamma
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) (W.U i.succ)
        (reserveEdges (G z.1) (W.U i.succ) (bits z.1)) (added z.1 z.2))
      p r' (2 * max (C ^ 3 * factor) J) (beta + error) := by
  dsimp only
  let old := fun omega ↦ initial omega ∪ later omega
  let Kint := correlatedRawInternalKernel W i F G A old pre bits ⌊mu / 32⌋₊
  let intAdded := correlatedRawInternalAdded old pre
  have hthreshold := (internal_cover_rounded_budgets mu hmu).1
  have hstructure := fun omega hmass ↦ correlatedRawInternalKernel_supported_structure
    W i F G A old pre bits ⌊mu / 32⌋₊ hthreshold Kpre omega (hG omega hmass) (hpre omega hmass)
  apply hstrong.jointBind_correlatedInternal_graphMixed (Kint := Kint)
    G (W.U i.succ) pre intAdded (fun _ ↦ survival) (fun _ ↦ point) (fun _ ↦ constant)
    (fun _ ↦ 64 / mu) alpha eta J factor error r' hC hJ hfactor halpha heta hr hetar
    le_rfl hnonempty hnew
    (fun omega _ ↦ reserveEdges_subset_crossingEdges (G omega) (W.U i.succ) (bits omega))
    hmixed ?_ ?_ (fun _ _ ↦ halphaBound) (fun _ _ ↦ hetaBound) (fun _ _ ↦ hconstant) ?_ ?_ ?_
  · intro _ _
    exact (div_le_one (by positivity : (0 : ℝ≥0) < mu)).mpr
      ((by norm_num : (64 : ℝ≥0) ≤ 512).trans hmu)
  · intro omega _ xi Q
    exact rawResidualInternalKernel_rounded_point_bound W i F
      (fun z : Omega × Xi ↦ G z.1)
      (fun z ↦ pairSafeAvailable (A z.1) (correlatedRawInternalStart old pre z))
      (correlatedRawInternalStart old pre) (fun z ↦ bits z.1) mu hmu (omega, xi) Q
  · intro omega hmass z hz
    have hS := hstructure omega hmass z hz
    exact ⟨hS.2.1, hS.2.2.1, fun T hT ↦ htri omega hmass T (hS.1 hT)⟩
  · intro omega hmass z hz
    have hS := hstructure omega hmass z hz
    exact ⟨hS.2.2.2.1, hS.2.2.2.2.2⟩
  · intro omega hmass z hz T hT
    exact hsupport omega hmass T ((hstructure omega hmass z hz).1 hT)

end

end Erdos207
