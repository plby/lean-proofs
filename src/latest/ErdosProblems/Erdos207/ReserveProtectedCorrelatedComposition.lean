/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeResidualProduct
import ErdosProblems.Erdos207.PreliminaryResidualInternalFixedReserveKernel
import ErdosProblems.Erdos207.ReserveProtectedAugmentedReserveLaw

/-!
# Correlated preliminary/internal master update

The scheduled internal sampler is not an independent master update.  Every
selected internal triangle first requires its unique outside--outside edge to
survive the preliminary phase.  This file performs the two samplers inside a
single augmented-reserve update, at the sharp combined triangle scale
`alpha + eta * delta`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Bind a reserve-protected preliminary kernel and a conditionally sampled
scheduled-internal kernel in one master update. -/
theorem IsReserveStronglyWellDistributed.jointBind_protectedPreliminaryInternal_of_numeric
    {Omega Xi Zeta V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega}
    {Kpre : Omega → FiniteLaw Xi}
    {Kint : Omega → Xi → FiniteLaw Zeta}
    {W : Vortex V ell} {level next : Fin (ell + 1)}
    {initial later : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b'
      alpha eta delta : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W level initial later
      sampled p reserveDensity C b)
    (addedPre : Omega → Xi → TripleSystemOn V)
    (addedInt : Omega → Xi → Zeta → TripleSystemOn V)
    (hsampled : ∀ omega, sampled omega ⊆ crossingEdges (G omega) U)
    (hpre : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
            (addedPre omega xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ omega xi Q,
      (Kint omega xi).probability (fun z ↦
        Q ⊆ addedInt omega xi z) ≤ delta ^ Q.card)
    (hstruct : ∀ omega, 0 < L.mass omega →
      ((Kpre omega).jointBind (Kint omega)).SupportedOn fun z ↦
        IsPackingOn
            (preliminaryInternalCombinedAdded
              (addedPre omega) (addedInt omega) z) ∧
          Disjoint (addedPre omega z.1) (addedInt omega z.1 z.2) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges (G omega) U
              (addedPre omega z.1))
            (addedPre omega z.1)
            (preliminaryInternalCombinedAdded
              (addedPre omega) (addedInt omega) z))
    (hnonempty : ∀ i, (W.U i).Nonempty)
    (hlevelNext : level ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (hcombinedOne : alpha + eta * delta ≤ 1) (hetaOne : eta ≤ 1)
    (hetaReserve : eta ≤ reserveDensity')
    (hbOne : b ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha + eta * delta ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let K : Omega → FiniteLaw (Xi × Zeta) := fun omega ↦
      (Kpre omega).jointBind (Kint omega)
    let added : Omega → Xi × Zeta → TripleSystemOn V := fun omega z ↦
      preliminaryInternalCombinedAdded (addedPre omega) (addedInt omega) z
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  dsimp only
  let K : Omega → FiniteLaw (Xi × Zeta) := fun omega ↦
    (Kpre omega).jointBind (Kint omega)
  let added : Omega → Xi × Zeta → TripleSystemOn V := fun omega z ↦
    preliminaryInternalCombinedAdded (addedPre omega) (addedInt omega) z
  apply hstrong.jointBind_preliminaryAugmentedReserve_sdiff_of_numeric_supported
    added (alpha := alpha + eta * delta) (eta := eta) (epsilon := 0)
  · intro omega hmass Q E
    have hproduct :=
      (Kpre omega).jointBind_probability_protectedPreliminaryInternalCombined_le
        (Kint omega) (G omega) U (sampled omega) (hsampled omega)
        (addedPre omega) (addedInt omega) alpha eta delta
        (hpre omega hmass) (hC4 omega) (hstruct omega hmass) Q E
    simpa only [K, added, add_zero] using hproduct
  · exact hnonempty
  · exact hlevelNext
  · exact hCC'
  · exact hC'
  · exact hpp'
  · exact hpOne
  · exact hreserveMono
  · exact hreserveOne
  · exact hcombinedOne
  · exact hetaOne
  · exact hetaReserve
  · exact hbOne
  · simpa using hbb'
  · exact hnew

/-- On a good preliminary fiber, the raw scheduled-internal law supplies the
packing, disjointness, and scheduled-edge provenance required by the
correlated product estimate. -/
theorem RawResidualInternalFiberGood.supportedOn_combinedAdded
    {Omega V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A P0 : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {D R : ℕ} {omega : Omega}
    (hgood : RawResidualInternalFiberGood W i F G A P0 bits D R omega)
    (hpacking : IsPackingOn (P0 omega)) :
    (rawResidualInternalKernel W i F G A P0 bits D omega).SupportedOn
      (fun z ↦
        IsPackingOn
          (preliminaryInternalCombinedAdded (fun _ : Unit ↦ P0 omega)
            (fun _ z ↦ rawResidualInternalAdded P0 omega z) ((), z)) ∧
        Disjoint (P0 omega) (rawResidualInternalAdded P0 omega z) ∧
        NewTrianglesUseScheduledOuterEdges (W.U i.succ)
          (preliminaryResidualInternalEdges
            (G omega) (W.U i.succ) (P0 omega))
          (P0 omega)
          (preliminaryInternalCombinedAdded (fun _ : Unit ↦ P0 omega)
            (fun _ z ↦ rawResidualInternalAdded P0 omega z) ((), z))) := by
  intro z hz
  have houtcome := hgood.1 z hz
  have hsubset : P0 omega ⊆ z.chosen := houtcome.1.1.initial_subset
  have hunion : P0 omega ∪ rawResidualInternalAdded P0 omega z =
      z.chosen := by
    exact union_sdiff_of_subset hsubset
  refine ⟨?_, ?_, ?_⟩
  · simpa only [preliminaryInternalCombinedAdded, hunion] using
      houtcome.1.1.isPacking hpacking
  · rw [Finset.disjoint_left]
    intro T hTP hTnew
    exact (mem_sdiff.mp hTnew).2 hTP
  · simpa only [preliminaryInternalCombinedAdded, hunion] using
      houtcome.2.2.1

/-- Specialization of the correlated master update to the raw residual
internal kernel.  The sample type is right-associated so the two subphases
form one conditional kernel over the old master outcome. -/
theorem IsReserveStronglyWellDistributed.jointBind_protectedPreliminary_rawInternal_correlated
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega} {Kpre : Omega → FiniteLaw Xi}
    {W : Vortex V ell} {level next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {G : Omega → SimpleGraph V}
    {Aint : Omega × Xi → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b'
      alpha eta : ℝ≥0} {D R : ℕ}
    (i : Fin ell) (hU : U = W.U i.succ)
    (hstrong : IsReserveStronglyWellDistributed L W level
      (fun _ ↦ (∅ : TripleSystemOn V)) (fun _ ↦ ∅)
      sampled p reserveDensity C b)
    (addedPre : Omega → Xi → TripleSystemOn V)
    (Good : Omega × Xi → Prop)
    (hsampled : ∀ omega, sampled omega ⊆ crossingEdges (G omega) U)
    (hpre : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
            (addedPre omega xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hgoodSupport : (L.jointBind Kpre).SupportedOn Good)
    (hpackingPre : ∀ z, Good z → IsPackingOn (addedPre z.1 z.2))
    (hfiber : ∀ z, Good z →
      RawResidualInternalFiberGood W i F
        (fun z : Omega × Xi ↦ G z.1) Aint
        (fun z ↦ addedPre z.1 z.2) (fun z ↦ bits z.1) D R z)
    (hC4 : ∀ z Q,
      (rawResidualInternalKernel W i F
        (fun z : Omega × Xi ↦ G z.1) Aint
        (fun z ↦ addedPre z.1 z.2) (fun z ↦ bits z.1) D z).probability
          (fun w ↦ Q ⊆ rawResidualInternalAdded
            (fun z : Omega × Xi ↦ addedPre z.1 z.2) z w) ≤
        ((D : ℝ≥0)⁻¹ ^ Q.card))
    (hnonempty : ∀ j, (W.U j).Nonempty)
    (hlevelNext : level ≤ next) (hCC' : C ≤ C') (hC' : 1 ≤ C')
    (hpp' : p ≤ p') (hpOne : p ≤ 1)
    (hreserveMono : reserveDensity ≤ reserveDensity')
    (hreserveOne : reserveDensity ≤ 1)
    (hcombinedOne : alpha + eta * (D : ℝ≥0)⁻¹ ≤ 1)
    (hetaOne : eta ≤ 1) (hetaReserve : eta ≤ reserveDensity')
    (hbOne : b ≤ 1) (hbb' : b ≤ b')
    (hnew : ∀ T : TripleOn V,
      alpha + eta * (D : ℝ≥0)⁻¹ ≤
        p' / ((W.U (W.truncatedLevel next T)).card : ℝ≥0)) :
    let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
      addedPre z.1 z.2
    let Gpre : Omega × Xi → SimpleGraph V := fun z ↦ G z.1
    let bitsPre : Omega × Xi → Sym2 V → Bool := fun z ↦ bits z.1
    let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
    let K : Omega → FiniteLaw (Xi × InternalEdgeGreedyStateOn V) :=
      fun omega ↦ (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))
    let added : Omega → Xi × InternalEdgeGreedyStateOn V →
        TripleSystemOn V := fun omega z ↦
      preliminaryInternalCombinedAdded (addedPre omega)
        (fun xi w ↦ rawResidualInternalAdded P0 (omega, xi) w) z
    IsReserveStronglyWellDistributed (L.jointBind K) W next
        (jointInitial (fun _ ↦ (∅ : TripleSystemOn V)))
        (jointLater (fun _ ↦ (∅ : TripleSystemOn V)) added)
        (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
          (added z.1 z.2)) p' reserveDensity' (2 * C') b' ∧
      (L.jointBind K).SupportedOn (fun z ↦
        Good (z.1, z.2.1) ∧
        RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre D R
          (z.1, z.2.1) z.2.2) := by
  dsimp only
  subst U
  let P0 : Omega × Xi → TripleSystemOn V := fun z ↦
    addedPre z.1 z.2
  let Gpre : Omega × Xi → SimpleGraph V := fun z ↦ G z.1
  let bitsPre : Omega × Xi → Sym2 V → Bool := fun z ↦ bits z.1
  let Kint := rawResidualInternalKernel W i F Gpre Aint P0 bitsPre D
  let K : Omega → FiniteLaw (Xi × InternalEdgeGreedyStateOn V) :=
    fun omega ↦ (Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))
  let added : Omega → Xi × InternalEdgeGreedyStateOn V →
      TripleSystemOn V := fun omega z ↦
    preliminaryInternalCombinedAdded (addedPre omega)
      (fun xi w ↦ rawResidualInternalAdded P0 (omega, xi) w) z
  have hstruct : ∀ omega, 0 < L.mass omega →
      ((Kpre omega).jointBind (fun xi ↦ Kint (omega, xi))).SupportedOn
        (fun z ↦
          IsPackingOn (added omega z) ∧
          Disjoint (addedPre omega z.1)
            (rawResidualInternalAdded P0 (omega, z.1) z.2) ∧
          NewTrianglesUseScheduledOuterEdges (W.U i.succ)
            (preliminaryResidualInternalEdges (G omega) (W.U i.succ)
              (addedPre omega z.1))
            (addedPre omega z.1) (added omega z)) := by
    intro omega hmass z hz
    have hmasses := FiniteLaw.jointBind_mass_pos_iff (Kpre omega)
      (fun xi ↦ Kint (omega, xi)) z.1 z.2 |>.mp hz
    have hgood : Good (omega, z.1) :=
      hgoodSupport (omega, z.1)
        (FiniteLaw.jointBind_mass_pos_iff L Kpre omega z.1 |>.2
          ⟨hmass, hmasses.1⟩)
    have hs := (hfiber (omega, z.1) hgood).supportedOn_combinedAdded
      (hpackingPre (omega, z.1) hgood) z.2 hmasses.2
    simpa only [added, P0, Gpre, bitsPre, Kint,
      preliminaryInternalCombinedAdded] using hs
  have hdist : IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial (fun _ ↦ (∅ : TripleSystemOn V)))
      (jointLater (fun _ ↦ (∅ : TripleSystemOn V)) added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) (W.U i.succ)
        (sampled z.1) (added z.1 z.2)) p' reserveDensity'
      (2 * C') b' := by
    exact hstrong.jointBind_protectedPreliminaryInternal_of_numeric
      addedPre
      (fun omega xi w ↦ rawResidualInternalAdded P0 (omega, xi) w)
      hsampled hpre
      (fun omega xi Q ↦ by simpa only [Kint] using hC4 (omega, xi) Q)
      (fun omega hmass ↦ by
        simpa only [added, P0, Gpre, bitsPre, Kint] using
          hstruct omega hmass)
      hnonempty hlevelNext hCC' hC' hpp' hpOne hreserveMono hreserveOne
      hcombinedOne hetaOne hetaReserve hbOne hbb' hnew
  have hsupp : (L.jointBind K).SupportedOn (fun z ↦
      Good (z.1, z.2.1) ∧
      RawResidualInternalOutcomeGood W i F Gpre Aint P0 bitsPre D R
        (z.1, z.2.1) z.2.2) := by
    intro z hz
    have hmassesOuter := FiniteLaw.jointBind_mass_pos_iff L K z.1 z.2 |>.mp hz
    have hmassesInner := FiniteLaw.jointBind_mass_pos_iff (Kpre z.1)
      (fun xi ↦ Kint (z.1, xi)) z.2.1 z.2.2 |>.mp hmassesOuter.2
    have hgood : Good (z.1, z.2.1) :=
      hgoodSupport (z.1, z.2.1)
        (FiniteLaw.jointBind_mass_pos_iff L Kpre z.1 z.2.1 |>.2
          ⟨hmassesOuter.1, hmassesInner.1⟩)
    exact ⟨hgood,
      (hfiber (z.1, z.2.1) hgood).supportedOn_outcome z.2.2
        hmassesInner.2⟩
  exact ⟨by simpa only [K, added, P0, Gpre, bitsPre, Kint] using hdist,
    by simpa only [K, P0, Gpre, bitsPre, Kint] using hsupp⟩

end

end Erdos207
