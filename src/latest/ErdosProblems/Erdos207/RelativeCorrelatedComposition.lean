/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedCorrelatedComposition
import ErdosProblems.Erdos207.RelativeResidualEdges

/-!
# Correlated preliminary/internal update relative to an old packing

The sharp correlated product theorem is phrased for a stage beginning with
the empty packing.  A later master stage begins with an old packing `Pold`,
but its graph is contained in `leaveGraph Pold`.  The residual-edge
identities in `RelativeResidualEdges` therefore remove `Pold` from every
probabilistic event.  This file packages that conversion and preserves the
old initial/later classification in the reserve-aware law.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The correlated protected update with an arbitrary old packing.  Only the
genuinely new preliminary and internal families are adjoined to the strong
law; the schedule and packing certificates may use the full old packing. -/
theorem IsReserveStronglyWellDistributed.jointBind_relativeProtectedPreliminaryInternal_of_numeric
    {Omega Xi Zeta V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {L : FiniteLaw Omega}
    {Kpre : Omega → FiniteLaw Xi}
    {Kint : Omega → Xi → FiniteLaw Zeta}
    {W : Vortex V ell} {level next : Fin (ell + 1)}
    {initial later Pold : Omega → TripleSystemOn V}
    {sampled : Omega → Finset (Sym2 V)}
    {G : Omega → SimpleGraph V} {U : Finset V}
    {p reserveDensity C b p' reserveDensity' C' b'
      alpha eta delta : ℝ≥0}
    (hstrong : IsReserveStronglyWellDistributed L W level initial later
      sampled p reserveDensity C b)
    (addedPre : Omega → Xi → TripleSystemOn V)
    (addedInt : Omega → Xi → Zeta → TripleSystemOn V)
    (hGleave : ∀ omega, 0 < L.mass omega →
      G omega ≤ leaveGraph (Pold omega))
    (hsampled : ∀ omega, sampled omega ⊆ crossingEdges (G omega) U)
    (hpre : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
            (Pold omega ∪ addedPre omega xi)) ≤
        alpha ^ Q.card * eta ^ E.card)
    (hC4 : ∀ omega xi Q,
      (Kint omega xi).probability (fun z ↦
        Q ⊆ addedInt omega xi z) ≤ delta ^ Q.card)
    (hstruct : ∀ omega, 0 < L.mass omega →
      ((Kpre omega).jointBind (Kint omega)).SupportedOn fun z ↦
        let added := preliminaryInternalCombinedAdded
          (addedPre omega) (addedInt omega) z
        IsPackingOn (Pold omega ∪ added) ∧
          Disjoint (Pold omega) added ∧
          Disjoint (addedPre omega z.1) (addedInt omega z.1 z.2) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges (G omega) U
              (Pold omega ∪ addedPre omega z.1))
            (Pold omega ∪ addedPre omega z.1)
            (Pold omega ∪ added))
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
      preliminaryInternalCombinedAdded
        (addedPre omega) (addedInt omega) z
    IsReserveStronglyWellDistributed (L.jointBind K) W next
      (jointInitial initial) (jointLater later added)
      (fun z ↦ preliminaryAugmentedReserve (G z.1) U (sampled z.1)
        (added z.1 z.2)) p' reserveDensity' (2 * C') b' := by
  dsimp only
  let K : Omega → FiniteLaw (Xi × Zeta) := fun omega ↦
    (Kpre omega).jointBind (Kint omega)
  let added : Omega → Xi × Zeta → TripleSystemOn V := fun omega z ↦
    preliminaryInternalCombinedAdded
      (addedPre omega) (addedInt omega) z
  have hpre' : ∀ omega, 0 < L.mass omega → ∀ Q E,
      (Kpre omega).probability (fun xi ↦
        Q ⊆ addedPre omega xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
            (addedPre omega xi)) ≤
        alpha ^ Q.card * eta ^ E.card := by
    intro omega hmass Q E
    have hprotectedLeave :
      reserveProtectedOuterGraph (G omega) U (sampled omega) ≤
          leaveGraph (Pold omega) :=
      (reserveProtectedOuterGraph_le (G omega) U (sampled omega)).trans
        (hGleave omega hmass)
    have hpreSupport : (Kpre omega).SupportedOn fun xi ↦
        Disjoint (Pold omega) (addedPre omega xi) := by
      intro xi hxiMass
      obtain ⟨zeta, hzetaMass⟩ := (Kint omega xi).exists_mass_pos
      have hs := hstruct omega hmass (xi, zeta)
        (FiniteLaw.jointBind_mass_pos_iff (Kpre omega)
          (Kint omega) xi zeta |>.2 ⟨hxiMass, hzetaMass⟩)
      exact hs.2.1.mono_right subset_union_left
    have hmono : (Kpre omega).probability (fun xi ↦
          Q ⊆ addedPre omega xi ∧
            E ⊆ preliminaryResidualOuterEdges
              (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
              (addedPre omega xi)) ≤
        (Kpre omega).probability (fun xi ↦
          Q ⊆ addedPre omega xi ∧
            E ⊆ preliminaryResidualOuterEdges
              (reserveProtectedOuterGraph (G omega) U (sampled omega)) U
              (Pold omega ∪ addedPre omega xi)) := by
      apply (Kpre omega).probability_mono_of_supported hpreSupport
      intro xi hdisj hxi
      refine ⟨hxi.1, ?_⟩
      rw [preliminaryResidualOuterEdges_union_eq_of_le_leaveGraph
        hprotectedLeave hdisj]
      exact hxi.2
    exact hmono.trans (hpre omega hmass Q E)
  have hstruct' : ∀ omega, 0 < L.mass omega →
      ((Kpre omega).jointBind (Kint omega)).SupportedOn fun z ↦
        IsPackingOn (added omega z) ∧
          Disjoint (addedPre omega z.1) (addedInt omega z.1 z.2) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges (G omega) U
              (addedPre omega z.1))
            (addedPre omega z.1) (added omega z) := by
    intro omega hmass z hz
    have hs := hstruct omega hmass z hz
    have hpack : IsPackingOn (added omega z) :=
      hs.1.mono subset_union_right
    have hPpre : Disjoint (Pold omega) (addedPre omega z.1) :=
      hs.2.1.mono_right subset_union_left
    have hschedule : preliminaryResidualInternalEdges (G omega) U
          (Pold omega ∪ addedPre omega z.1) =
        preliminaryResidualInternalEdges (G omega) U
          (addedPre omega z.1) :=
      preliminaryResidualInternalEdges_union_eq_of_le_leaveGraph
        (hGleave omega hmass) hPpre
    refine ⟨hpack, hs.2.2.1, ?_⟩
    intro T hT
    have hTnew : T ∈
        (Pold omega ∪ added omega z) \
          (Pold omega ∪ addedPre omega z.1) := by
      have hTdata := mem_sdiff.mp hT
      refine mem_sdiff.mpr ⟨mem_union_right _ hTdata.1, ?_⟩
      intro hToldPre
      rcases mem_union.mp hToldPre with hTold | hTpre
      · exact Finset.disjoint_left.mp hs.2.1 hTold hTdata.1
      · exact hTdata.2 hTpre
    obtain ⟨e, he, hne, w, hw, hT⟩ := hs.2.2.2 T hTnew
    exact ⟨e, by simpa only [hschedule] using he, hne, w, hw, hT⟩
  exact hstrong.jointBind_protectedPreliminaryInternal_of_numeric
    addedPre addedInt hsampled hpre' hC4
    (by simpa only [added, K] using hstruct') hnonempty hlevelNext hCC'
    hC' hpp' hpOne hreserveMono hreserveOne hcombinedOne hetaOne
    hetaReserve hbOne hbb' hnew

end

end Erdos207
