/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedCorrelatedComposition
import ErdosProblems.Erdos207.RawInternalRootedConditioning
import ErdosProblems.Erdos207.RawInternalResidualLinks

/-!
# Rooted conditioning and residual links for the correlated stage

The protected preliminary and scheduled-internal samplers are combined into
one right-associated kernel in `ReserveProtectedCorrelatedComposition`.  This
file conditions that combined law directly on the terminal rooted-cap event.
In particular, the reserve used below is augmented by the *whole* correlated
addition, not merely by its preliminary part.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Root conditioning for arbitrary initial/later families. -/
theorem IsReserveStronglyWellDistributed.conditionOn_rootedActiveCapsGood_general
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {level : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {initial later : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0} {R q s : ℕ}
    (hreserve : IsReserveStronglyWellDistributed law W level
      initial later reserve p reserveDensity C b)
    (hC : 1 ≤ C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b ≤ setWeight (masterUnionTriangleWeight W level p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W level p) kappa)
    (htail : strongRootedTail V C kappa R q s < 1) :
    let RootGood : Omega → Prop := fun z ↦
      RootedActiveCapsGood F (initial z ∪ later z) R
    ∃ hpos : 0 < law.probability RootGood,
      let Lc := law.conditionOn RootGood hpos
      IsReserveStronglyWellDistributed Lc W level initial later reserve
          p reserveDensity
          (C / (1 - strongRootedTail V C kappa R q s)) b ∧
        Lc.SupportedOn RootGood ∧
        1 - strongRootedTail V C kappa R q s ≤
          law.probability RootGood := by
  dsimp only
  let RootGood : Omega → Prop := fun z ↦
    RootedActiveCapsGood F (initial z ∪ later z) R
  have hbad : law.probability (fun z ↦ ¬ RootGood z) ≤
      strongRootedTail V C kappa R q s := by
    simpa only [RootGood] using
      hreserve.toStrong.probability_not_rootedActiveCapsGood_le
        F R hC hFcard hb kappa hkappa
  have hlower : 1 - strongRootedTail V C kappa R q s ≤
      law.probability RootGood := by
    rw [law.probability_not RootGood] at hbad
    calc
      1 - strongRootedTail V C kappa R q s ≤
          1 - (1 - law.probability RootGood) :=
        tsub_le_tsub_left hbad 1
      _ = law.probability RootGood :=
        tsub_tsub_cancel_of_le (law.probability_le_one RootGood)
  have hpos : 0 < law.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower
  refine ⟨hpos, ?_⟩
  let Lc := law.conditionOn RootGood hpos
  have hconditioned := hreserve.conditionOn RootGood hpos
  have hden : 0 < 1 - strongRootedTail V C kappa R q s :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : C / law.probability RootGood ≤
      C / (1 - strongRootedTail V C kappa R q s) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  exact ⟨hconditioned.mono_factor hfactor,
    law.conditionOn_supported RootGood hpos, hlower⟩

/-- Root conditioning only uses strong distribution of the accumulated
family; it does not depend on how the law was assembled. -/
theorem IsReserveStronglyWellDistributed.conditionOn_rootedActiveCapsGood
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw Omega} {W : Vortex V ell}
    {level : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {total : Omega → TripleSystemOn V}
    {reserve : Omega → Finset (Sym2 V)}
    {p reserveDensity C b : ℝ≥0} {R q s : ℕ}
    (hreserve : IsReserveStronglyWellDistributed law W level
      (fun _ ↦ (∅ : TripleSystemOn V)) total reserve
      p reserveDensity C b)
    (hC : 1 ≤ C)
    (hFcard : ∀ S ∈ F, S.card ≤ q)
    (hb : ∀ T : TripleSystemOn V, T.card ≤ s * (q - 1) →
      b ≤ setWeight (masterUnionTriangleWeight W level p) T)
    (kappa : ℝ≥0)
    (hkappa : ∀ e : DistinctPair V,
      HasExtensionBound
        (fun z : RootedThreatWitness V F e.1.1 e.1.2 ↦
          rootedThreatRemainder z)
        (masterUnionTriangleWeight W level p) kappa)
    (htail : strongRootedTail V C kappa R q s < 1) :
    let RootGood : Omega → Prop := fun z ↦ RootedActiveCapsGood F (total z) R
    ∃ hpos : 0 < law.probability RootGood,
      let Lc := law.conditionOn RootGood hpos
      IsReserveStronglyWellDistributed Lc W level
          (fun _ ↦ (∅ : TripleSystemOn V)) total reserve
          p reserveDensity
          (C / (1 - strongRootedTail V C kappa R q s)) b ∧
        Lc.SupportedOn RootGood ∧
        1 - strongRootedTail V C kappa R q s ≤
          law.probability RootGood := by
  dsimp only
  let RootGood : Omega → Prop := fun z ↦ RootedActiveCapsGood F (total z) R
  have hbad : law.probability (fun z ↦ ¬ RootGood z) ≤
      strongRootedTail V C kappa R q s := by
    simpa only [RootGood, empty_union] using
      hreserve.toStrong.probability_not_rootedActiveCapsGood_le
        F R hC hFcard hb kappa hkappa
  have hlower : 1 - strongRootedTail V C kappa R q s ≤
      law.probability RootGood := by
    rw [law.probability_not RootGood] at hbad
    calc
      1 - strongRootedTail V C kappa R q s ≤
          1 - (1 - law.probability RootGood) :=
        tsub_le_tsub_left hbad 1
      _ = law.probability RootGood :=
        tsub_tsub_cancel_of_le (law.probability_le_one RootGood)
  have hpos : 0 < law.probability RootGood :=
    (tsub_pos_iff_lt.mpr htail).trans_le hlower
  refine ⟨hpos, ?_⟩
  let Lc := law.conditionOn RootGood hpos
  have hconditioned := hreserve.conditionOn RootGood hpos
  have hden : 0 < 1 - strongRootedTail V C kappa R q s :=
    tsub_pos_iff_lt.mpr htail
  have hfactor : C / law.probability RootGood ≤
      C / (1 - strongRootedTail V C kappa R q s) :=
    div_le_div_of_nonneg_left zero_le hden hlower
  refine ⟨hconditioned.mono_factor hfactor, ?_, hlower⟩
  exact law.conditionOn_supported RootGood hpos

/-- Conditioning preserves any old support predicate and appends the rooted
cap for the full correlated addition. -/
theorem FiniteLaw.SupportedOn.conditionOn_rootedActiveCapsGood
    {Omega : Type*} [Fintype Omega] [DecidableEq Omega]
    {law : FiniteLaw Omega} {Good RootGood : Omega → Prop}
    (hgood : law.SupportedOn Good)
    {hpos : 0 < law.probability RootGood} :
    (law.conditionOn RootGood hpos).SupportedOn
      (fun z ↦ Good z ∧ RootGood z) := by
  intro z hz
  exact ⟨hgood.conditionOn hpos z hz,
    law.conditionOn_supported RootGood hpos z hz⟩

/-- On the support of the correlated raw law, the full combined addition is
exactly the terminal chosen family. -/
theorem RawResidualInternalOutcomeGood.preliminaryInternalCombinedAdded_eq_chosen
    {Omega Xi V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {i : Fin ell}
    {F : ForbiddenFamilyOn V}
    {G : Omega × Xi → SimpleGraph V}
    {A P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool} {D R : ℕ}
    {omega : Omega} {xi : Xi} {z : InternalEdgeGreedyStateOn V}
    (houtcome : RawResidualInternalOutcomeGood W i F G A P0 bits D R
      (omega, xi) z) :
    preliminaryInternalCombinedAdded (fun _ : Xi ↦ P0 (omega, xi))
        (fun _ w ↦ rawResidualInternalAdded P0 (omega, xi) w) (xi, z) =
      z.chosen := by
  exact union_sdiff_of_subset houtcome.1.1.initial_subset

/-- The correlated law, after rooted conditioning, satisfies the complete
pointwise hypotheses needed to choose all residual links.  We take the full
combined addition as `Mstar`; on support it is equal to `chosen`, so the
remaining greedy reachability obligation is reflexive. -/
theorem FiniteLaw.SupportedOn.correlatedRawInternalOutcomeReady
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A : Omega → TripleSystemOn V}
    {Aint : Omega × Xi → TripleSystemOn V}
    {P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {D R : ℕ}
    {Good : Omega × Xi → Prop}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        RawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint P0 bits D R
          (z.1, z.2.1) z.2.2 ∧
        RootedActiveCapsGood F z.2.2.chosen R)
    (hP0 : ∀ z, Good z → P0 z ⊆ A z.1)
    (hAint : ∀ z, Good z → Aint z ⊆ A z.1)
    (hpacking : ∀ z, Good z → IsPackingOn (P0 z))
    (heven : ∀ omega v, Even ((neighborsIn (G omega) univ v).card))
    (hleave : ∀ omega, G omega ≤ leaveGraph (∅ : TripleSystemOn V))
    (htri : ∀ omega, ConsistsOfTriangles (G omega) (A omega)) :
    let total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        TripleSystemOn V := fun z ↦
      preliminaryInternalCombinedAdded (fun _ : Xi ↦ P0 (z.1, z.2.1))
        (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
    let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
        (total z)
    law.SupportedOn (InternalOutcomeReady
      (fun z ↦ G z.1) (W.U i.succ) reserve F (fun z ↦ A z.1)
      (fun _ ↦ ∅) (fun _ ↦ ∅) total (fun z ↦ z.2.2.chosen)) := by
  dsimp only
  let total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded (fun _ : Xi ↦ P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
      (total z)
  intro z hz
  have hzdata := hsupport z hz
  have hgood := hzdata.1
  have houtcome := hzdata.2.1
  have htotal : total z = z.2.2.chosen := by
    simpa only [total] using
      houtcome.preliminaryInternalCombinedAdded_eq_chosen
        (omega := z.1) (xi := z.2.1)
  have htotalExpr :
      preliminaryInternalCombinedAdded
          (fun _ : Xi ↦ P0 (z.1, z.2.1))
          (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2 =
        z.2.2.chosen := by
    simpa only [total] using htotal
  have hcomplete := houtcome.complete_internalCover hzdata.2.2
  have hchosenA : z.2.2.chosen ⊆ A z.1 := by
    intro T hT
    rcases mem_union.mp (hcomplete.2.1 hT) with hTP0 | hTAint
    · exact hP0 (z.1, z.2.1) hgood hTP0
    · exact hAint (z.1, z.2.1) hgood hTAint
  refine ⟨heven z.1, ?_, htri z.1, ?_, ?_, ?_, ?_, ?_,
    hcomplete.2.2.2, ?_⟩
  · simpa using hleave z.1
  · simpa only [empty_union, htotalExpr] using hchosenA
  · simp
  · simpa only [empty_union, htotalExpr] using
      hcomplete.1.isPacking (hpacking (z.1, z.2.1) hgood)
  · simpa only [empty_union, htotalExpr] using
      (GreedyReachable.refl :
        GreedyReachable F z.2.2.chosen z.2.2.chosen)
  · dsimp only
    rw [empty_union, empty_union, htotalExpr]
    exact subset_union_left
  · exact coversCrossingOutsideReserve_preliminaryAugmentedReserve
      (G z.1) (W.U i.succ) (sampled z.1) (total z)

/-- Canonical residual links for the conditioned correlated law. -/
theorem FiniteLaw.SupportedOn.correlatedRawInternalResidualLinks
    {Omega Xi V : Type*}
    [Fintype Omega] [DecidableEq Omega]
    [Fintype Xi] [DecidableEq Xi]
    [Fintype V] [DecidableEq V] {ell : ℕ}
    {law : FiniteLaw (Omega × (Xi × InternalEdgeGreedyStateOn V))}
    {W : Vortex V ell} {i : Fin ell} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V} {A : Omega → TripleSystemOn V}
    {Aint : Omega × Xi → TripleSystemOn V}
    {P0 : Omega × Xi → TripleSystemOn V}
    {bits : Omega × Xi → Sym2 V → Bool}
    {sampled : Omega → Finset (Sym2 V)} {D R : ℕ}
    {Good : Omega × Xi → Prop}
    (hsupport : law.SupportedOn fun z ↦
      Good (z.1, z.2.1) ∧
        RawResidualInternalOutcomeGood W i F
          (fun z : Omega × Xi ↦ G z.1) Aint P0 bits D R
          (z.1, z.2.1) z.2.2 ∧
        RootedActiveCapsGood F z.2.2.chosen R)
    (hP0 : ∀ z, Good z → P0 z ⊆ A z.1)
    (hAint : ∀ z, Good z → Aint z ⊆ A z.1)
    (hpacking : ∀ z, Good z → IsPackingOn (P0 z))
    (heven : ∀ omega v, Even ((neighborsIn (G omega) univ v).card))
    (hleave : ∀ omega, G omega ≤ leaveGraph (∅ : TripleSystemOn V))
    (htri : ∀ omega, ConsistsOfTriangles (G omega) (A omega)) :
    let total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        TripleSystemOn V := fun z ↦
      preliminaryInternalCombinedAdded (fun _ : Xi ↦ P0 (z.1, z.2.1))
        (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
    let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
        Finset (Sym2 V) := fun z ↦
      preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
        (total z)
    let links := Erdos207.internalOutcomeResidualLinks
      (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ G z.1)
      (W.U i.succ) reserve F
      (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ A z.1)
      (fun _ : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ ∅)
      (fun _ : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ ∅)
      total
      (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ z.2.2.chosen)
    law.SupportedOn fun z ↦
      IsIntermediateLinkState (G z.1) (W.U i.succ) (A z.1) ∅ ∅
          (internalStageFamily ∅ ∅ (total z) z.2.2.chosen) (links z) ∧
        (∀ o, (links z o).center = outsideVertexEmbedding (W.U i.succ) o) ∧
        (∀ o, outsideVertexEmbedding (W.U i.succ) o ∉ W.U i.succ) ∧
        (∀ o, (links z o).left ⊆ W.U i.succ) ∧
        (∀ o, (links z o).right ⊆ W.U i.succ) ∧
        (∀ o, (links z o).SpokesIn (reserve z)) := by
  dsimp only
  let total : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      TripleSystemOn V := fun z ↦
    preliminaryInternalCombinedAdded (fun _ : Xi ↦ P0 (z.1, z.2.1))
      (fun _ w ↦ rawResidualInternalAdded P0 (z.1, z.2.1) w) z.2
  let reserve : Omega × (Xi × InternalEdgeGreedyStateOn V) →
      Finset (Sym2 V) := fun z ↦
    preliminaryAugmentedReserve (G z.1) (W.U i.succ) (sampled z.1)
      (total z)
  let links := Erdos207.internalOutcomeResidualLinks
    (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ G z.1)
    (W.U i.succ) reserve F
    (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ A z.1)
    (fun _ : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ ∅)
    (fun _ : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ ∅)
    total
    (fun z : Omega × (Xi × InternalEdgeGreedyStateOn V) ↦ z.2.2.chosen)
  have hready := hsupport.correlatedRawInternalOutcomeReady
    (sampled := sampled) hP0 hAint hpacking heven hleave htri
  simpa only [total, reserve, links] using
    hready.internalOutcomeResidualLinks

end

end Erdos207
