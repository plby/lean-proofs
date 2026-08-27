/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeResidualProduct
import ErdosProblems.Erdos207.GraphMixedProductBound
import ErdosProblems.Erdos207.InitialProductResidualIncidence

/-! # Correlated internal covering retains the preliminary additive error -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem FiniteLaw.jointBind_probability_protectedPreliminary_internal_parts_error_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta]
    [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hreserve : reserve ⊆ crossingEdges G U)
    (addedPre : Xi → TripleSystemOn V)
    (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta J epsilon : ℝ≥0)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦
        Q ⊆ addedPre xi ∧
          E ⊆ preliminaryResidualOuterEdges
            (reserveProtectedOuterGraph G U reserve) U (addedPre xi)) ≤
        alpha ^ Q.card * eta ^ E.card + J ^ (Q.card + E.card) * epsilon)
    (hC4 : ∀ xi Q,
      (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤
        delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Qpre Qint : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      alpha ^ Qpre.card * (eta * delta) ^ Qint.card *
        eta ^ Efix.card + delta ^ Qint.card * J ^ (Qpre.card + Qint.card + Efix.card) * epsilon := by
  classical
  let Required : Finset (Sym2 V) :=
    internalRequiredOuterEdges U Qint ∪ Efix
  let PreEvent : Xi → Prop := fun xi ↦
    Qpre ⊆ addedPre xi ∧
      Required ⊆ preliminaryResidualOuterEdges
        (reserveProtectedOuterGraph G U reserve) U (addedPre xi)
  let IntEvent : Xi → Zeta → Prop := fun xi z ↦
    Qint ⊆ addedInt xi z ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) \ reserve
  have houter : ∀ xi e,
      e ∈ preliminaryResidualInternalEdges G U (addedPre xi) →
      e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro xi e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        G U (addedPre xi) he)).2
  have hsupportImp : ∀ z,
      (IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1))
          (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z)) →
      (Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) →
      PreEvent z.1 := by
    intro z hs hz
    refine ⟨hz.1, ?_⟩
    have hQdiff : Qint ⊆
        preliminaryInternalCombinedAdded addedPre addedInt z \ addedPre z.1 := by
      intro T hT
      exact mem_sdiff.mpr ⟨mem_union_right _ (hz.2.1 hT),
        fun hTpre ↦
          Finset.disjoint_left.mp hs.2.1 hTpre (hz.2.1 hT)⟩
    have hrequired : internalRequiredOuterEdges U Qint ⊆
        preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U (addedPre z.1) :=
      (internalRequiredOuterEdges_subset_of_usesScheduled
        (houter z.1) hs.2.2 hQdiff).trans
          (preliminaryResidualInternalEdges_subset_protectedResidualOuter
            G U reserve (addedPre z.1) hreserve)
    have hresidual : Efix ⊆
        preliminaryResidualOuterEdges
          (reserveProtectedOuterGraph G U reserve) U (addedPre z.1) := by
      rw [preliminaryResidualOuterEdges_reserveProtectedOuterGraph]
      intro e he
      have hedata := mem_sdiff.mp (hz.2.2 he)
      exact mem_sdiff.mpr
        ⟨preliminaryResidualCrossingEdges_union_subset_residualOuter
          G U (addedPre z.1) (addedInt z.1 z.2) hedata.1,
          hedata.2⟩
    exact union_subset hrequired hresidual
  have hmono :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := by
    apply (Kpre.jointBind Kint).probability_mono_of_supported hstruct
    intro z hs hz
    exact ⟨hsupportImp z hs hz, ⟨hz.2.1, hz.2.2⟩⟩
  have hconditional : ∀ xi, 0 < Kpre.mass xi → PreEvent xi →
      (Kint xi).probability (IntEvent xi) ≤ delta ^ Qint.card := by
    intro xi hmass _hpre
    have hfiber : (Kint xi).SupportedOn fun z ↦
        IsPackingOn
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) ∧
          Disjoint (addedPre xi) (addedInt xi z) ∧
          NewTrianglesUseScheduledOuterEdges U
            (preliminaryResidualInternalEdges G U (addedPre xi))
            (addedPre xi)
            (preliminaryInternalCombinedAdded addedPre addedInt (xi, z)) := by
      intro z hz
      exact hstruct (xi, z)
        (FiniteLaw.jointBind_mass_pos_iff Kpre Kint xi z |>.2
          ⟨hmass, hz⟩)
    calc
      (Kint xi).probability (IntEvent xi) ≤
          (Kint xi).probability (fun z ↦ Qint ⊆ addedInt xi z) := by
        apply (Kint xi).probability_mono_of_supported hfiber
        intro z _hs hz
        exact hz.1
      _ ≤ delta ^ Qint.card := hC4 xi Qint
  have hjoint :
      (Kpre.jointBind Kint).probability (fun z ↦
        PreEvent z.1 ∧ IntEvent z.1 z.2) ≤
        delta ^ Qint.card * Kpre.probability PreEvent := by
    exact Kpre.jointBind_probability_and_le_on_support Kint PreEvent IntEvent
      (delta ^ Qint.card) hconditional
  by_cases hzero :
      (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) = 0
  · rw [hzero]
    exact zero_le
  have hpos : 0 < (Kpre.jointBind Kint).probability (fun z ↦
      Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) :=
    pos_iff_ne_zero.mpr hzero
  obtain ⟨zWitness, hmassWitness, hzWitness⟩ :=
    (Kpre.jointBind Kint).exists_mass_pos_and_of_probability_pos hpos
  have hsWitness := hstruct zWitness hmassWitness
  have hQdiffWitness : Qint ⊆
      preliminaryInternalCombinedAdded addedPre addedInt zWitness \
        addedPre zWitness.1 := by
    intro T hT
    exact mem_sdiff.mpr ⟨mem_union_right _ (hzWitness.2.1 hT),
      fun hTpre ↦
        Finset.disjoint_left.mp hsWitness.2.1 hTpre (hzWitness.2.1 hT)⟩
  have hcard : Required.card = Qint.card + Efix.card := by
    exact card_internalRequired_union_residualCrossing_of_usesScheduled
      hsWitness.1 (houter zWitness.1) hsWitness.2.2 hQdiffWitness Efix
        (fun e he ↦ (mem_sdiff.mp (hzWitness.2.2 he)).1)
  calc
    (Kpre.jointBind Kint).probability (fun z ↦
        Qpre ⊆ addedPre z.1 ∧ Qint ⊆ addedInt z.1 z.2 ∧
          Efix ⊆ preliminaryResidualCrossingEdges G U
            (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
        (Kpre.jointBind Kint).probability (fun z ↦
          PreEvent z.1 ∧ IntEvent z.1 z.2) := hmono
    _ ≤ delta ^ Qint.card * Kpre.probability PreEvent := hjoint
    _ ≤ delta ^ Qint.card *
        (alpha ^ Qpre.card * eta ^ Required.card + J ^ (Qpre.card + Required.card) * epsilon) := by
      gcongr
      exact hpre Qpre Required
    _ = alpha ^ Qpre.card * (eta * delta) ^ Qint.card *
        eta ^ Efix.card + delta ^ Qint.card * J ^ (Qpre.card + Qint.card + Efix.card) * epsilon := by
      rw [hcard]
      simp only [pow_add, mul_pow]
      ring


theorem IsGraphMixedProductBound.preliminaryResidualOuter_le
    {Ω V : Type*} [Fintype Ω] [Fintype V] [DecidableEq V]
    {L : FiniteLaw Ω} {selected : Ω → TripleSystemOn V} {G : SimpleGraph V}
    {survival point C error : ℝ≥0}
    (h : IsGraphMixedProductBound L selected G survival point C error)
    (U : Finset V) (Q : TripleSystemOn V) (E : Finset (Sym2 V)) :
    L.probability (fun ω ↦ Q ⊆ selected ω ∧
      E ⊆ preliminaryResidualOuterEdges G U (selected ω)) ≤
        (C * point) ^ Q.card * (C * survival) ^ E.card + C ^ (Q.card + E.card) * error := by
  by_cases hE : E ⊆ graphEdges G
  · calc
      _ ≤ L.probability (fun ω ↦ Q ⊆ selected ω ∧
          ∀ e ∈ E, e ∉ (coveredGraph (selected ω)).edgeSet) :=
        L.probability_mono (fun _ hω ↦ ⟨hω.1, subset_uncovered_of_subset_preliminaryResidualOuterEdges hω.2⟩)
      _ ≤ _ := (h Q E hE).trans_eq (by simp only [mul_add, mul_pow, pow_add]; ring)
  · have hz : L.probability (fun ω ↦ Q ⊆ selected ω ∧
        E ⊆ preliminaryResidualOuterEdges G U (selected ω)) ≤ L.probability (fun _ ↦ False) := by
      apply L.probability_mono
      intro ω hω
      exact hE (fun e he ↦ (mem_outerGraphEdges_iff.mp (mem_sdiff.mp (hω.2 he)).1).1)
    rw [L.probability_false] at hz
    exact hz.trans zero_le

theorem FiniteLaw.jointBind_probability_protectedPreliminaryInternalCombined_error_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta] [Fintype V] [DecidableEq V]
    (Kpre : FiniteLaw Xi) (Kint : Xi → FiniteLaw Zeta)
    (G : SimpleGraph V) (U : Finset V) (reserve : Finset (Sym2 V))
    (hreserve : reserve ⊆ crossingEdges G U)
    (addedPre : Xi → TripleSystemOn V) (addedInt : Xi → Zeta → TripleSystemOn V)
    (alpha eta delta J epsilon : ℝ≥0) (hdelta : delta ≤ 1)
    (hpre : ∀ Q E,
      Kpre.probability (fun xi ↦ Q ⊆ addedPre xi ∧
        E ⊆ preliminaryResidualOuterEdges (reserveProtectedOuterGraph G U reserve) U (addedPre xi)) ≤
          alpha ^ Q.card * eta ^ E.card + J ^ (Q.card + E.card) * epsilon)
    (hC4 : ∀ xi Q, (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤ delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1)) (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Q : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      (alpha + eta * delta) ^ Q.card * eta ^ Efix.card + (2 * J) ^ (Q.card + Efix.card) * epsilon := by
  classical
  let Event := fun S : TripleSystemOn V ↦ fun z : Xi × Zeta ↦
    S ⊆ addedPre z.1 ∧ Q \ S ⊆ addedInt z.1 z.2 ∧
      Efix ⊆ preliminaryResidualCrossingEdges G U
        (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve
  have hmono : (Kpre.jointBind Kint).probability (fun z ↦
      Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      (Kpre.jointBind Kint).probability (fun z ↦ ∃ S ∈ Q.powerset, Event S z) := by
    apply (Kpre.jointBind Kint).probability_mono
    intro z hz
    obtain ⟨S, hS, hpre, hint⟩ := subset_preliminaryInternalCombinedAdded_partition addedPre addedInt Q z hz.1
    exact ⟨S, hS, hpre, hint, hz.2⟩
  calc
    _ ≤ (Kpre.jointBind Kint).probability (fun z ↦ ∃ S ∈ Q.powerset, Event S z) := hmono
    _ ≤ ∑ S ∈ Q.powerset, (Kpre.jointBind Kint).probability (Event S) :=
      (Kpre.jointBind Kint).probability_exists_le Q.powerset Event
    _ ≤ ∑ S ∈ Q.powerset,
        (alpha ^ S.card * (eta * delta) ^ (Q \ S).card * eta ^ Efix.card +
          J ^ (Q.card + Efix.card) * epsilon) := by
      apply sum_le_sum
      intro S hS
      have hraw := Kpre.jointBind_probability_protectedPreliminary_internal_parts_error_le
        Kint G U reserve hreserve addedPre addedInt alpha eta delta J epsilon hpre hC4 hstruct S (Q \ S) Efix
      have hcard : S.card + (Q \ S).card = Q.card := by
        rw [card_sdiff_of_subset (mem_powerset.mp hS)]
        have := card_le_card (mem_powerset.mp hS)
        omega
      rw [hcard] at hraw
      apply hraw.trans
      apply add_le_add le_rfl
      have hd := pow_le_one₀ (show 0 ≤ delta from zero_le) hdelta (n := (Q \ S).card)
      calc
        _ = delta ^ (Q \ S).card * (J ^ (Q.card + Efix.card) * epsilon) := by ring
        _ ≤ _ := mul_le_of_le_one_left zero_le hd
    _ = (∑ S ∈ Q.powerset, alpha ^ S.card * (eta * delta) ^ (Q \ S).card * eta ^ Efix.card) +
        (2 : ℝ≥0) ^ Q.card * (J ^ (Q.card + Efix.card) * epsilon) := by
      rw [sum_add_distrib]
      simp
    _ = (alpha + eta * delta) ^ Q.card * eta ^ Efix.card +
        (2 : ℝ≥0) ^ Q.card * (J ^ (Q.card + Efix.card) * epsilon) := by
      rw [← Finset.sum_mul, sum_powerset_pow_card_mul_pow_sdiff_card]
    _ ≤ _ := by
      apply add_le_add le_rfl
      calc
        _ ≤ (2 : ℝ≥0) ^ (Q.card + Efix.card) * (J ^ (Q.card + Efix.card) * epsilon) :=
          mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) (by omega)) zero_le
        _ = _ := by rw [mul_pow]; ring

theorem IsGraphMixedProductBound.protectedInternalCombined_le
    {Xi Zeta V : Type*} [Fintype Xi] [DecidableEq Xi]
    [Fintype Zeta] [DecidableEq Zeta] [Fintype V] [DecidableEq V]
    {Kpre : FiniteLaw Xi} (Kint : Xi → FiniteLaw Zeta)
    {G : SimpleGraph V} (U : Finset V) (reserve : Finset (Sym2 V))
    (hreserve : reserve ⊆ crossingEdges G U)
    {addedPre : Xi → TripleSystemOn V} (addedInt : Xi → Zeta → TripleSystemOn V)
    {survival point C error : ℝ≥0}
    (hmixed : IsGraphMixedProductBound Kpre addedPre (reserveProtectedOuterGraph G U reserve)
      survival point C error) (delta : ℝ≥0) (hdelta : delta ≤ 1)
    (hC4 : ∀ xi Q, (Kint xi).probability (fun z ↦ Q ⊆ addedInt xi z) ≤ delta ^ Q.card)
    (hstruct : (Kpre.jointBind Kint).SupportedOn fun z ↦
      IsPackingOn (preliminaryInternalCombinedAdded addedPre addedInt z) ∧
        Disjoint (addedPre z.1) (addedInt z.1 z.2) ∧
        NewTrianglesUseScheduledOuterEdges U
          (preliminaryResidualInternalEdges G U (addedPre z.1)) (addedPre z.1)
          (preliminaryInternalCombinedAdded addedPre addedInt z))
    (Q : TripleSystemOn V) (Efix : Finset (Sym2 V)) :
    (Kpre.jointBind Kint).probability (fun z ↦
      Q ⊆ preliminaryInternalCombinedAdded addedPre addedInt z ∧
        Efix ⊆ preliminaryResidualCrossingEdges G U
          (preliminaryInternalCombinedAdded addedPre addedInt z) \ reserve) ≤
      (C * point + (C * survival) * delta) ^ Q.card * (C * survival) ^ Efix.card +
        (2 * C) ^ (Q.card + Efix.card) * error := by
  exact Kpre.jointBind_probability_protectedPreliminaryInternalCombined_error_le
    Kint G U reserve hreserve addedPre addedInt (C * point) (C * survival) delta C error
    hdelta (hmixed.preliminaryResidualOuter_le U) hC4 hstruct Q Efix

end

end Erdos207
