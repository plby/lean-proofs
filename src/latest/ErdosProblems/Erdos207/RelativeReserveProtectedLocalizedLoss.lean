/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.RelativeReserveProtectedCorrelatedRooted
import ErdosProblems.Erdos207.LocalizedInternalStageLoss

/-!
# Localized loss of a relative reserve-protected stage

The coarse bound charges a preliminary family of size at most `n` by `2*n`.
When the reserve contains every crossing edge, however, the preliminary
family is wholly outside the next vortex set and contributes exactly zero.
The genuinely internal difference then contributes only the scheduled
incidence cutoff `d`.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Covering by a union of triangle families creates no neighbor outside the
union of the two individual covered-neighbor sets. -/
lemma coveredGraph_union_neighborFinset_subset
    {V : Type*} [Fintype V] [DecidableEq V]
    (P Q : TripleSystemOn V) (v : V) :
    (coveredGraph (P ∪ Q)).neighborFinset v ⊆
      (coveredGraph P).neighborFinset v ∪
        (coveredGraph Q).neighborFinset v := by
  intro w hw
  have hvw : (coveredGraph (P ∪ Q)).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using hw
  obtain ⟨T, hT, hvT, hwT, hvwne⟩ := coveredGraph_adj.mp hvw
  rcases mem_union.mp hT with hTP | hTQ
  · exact mem_union_left _ (by
      simpa only [SimpleGraph.mem_neighborFinset] using
        (coveredGraph_adj.mpr ⟨T, hTP, hvT, hwT, hvwne⟩))
  · exact mem_union_right _ (by
      simpa only [SimpleGraph.mem_neighborFinset] using
        (coveredGraph_adj.mpr ⟨T, hTQ, hvT, hwT, hvwne⟩))

/-- A packing with at most `n` triples covers at most `2*n` neighbors of a
fixed vertex, hence the same bound after localization to any set. -/
lemma IsPackingOn.card_coveredNeighborsIn_le_two_mul_card
    {V : Type*} [Fintype V] [DecidableEq V]
    {P : TripleSystemOn V} (hP : IsPackingOn P)
    (U : Finset V) (v : V) :
    ((coveredGraph P).neighborFinset v ∩ U).card ≤ 2 * P.card := by
  calc
    ((coveredGraph P).neighborFinset v ∩ U).card ≤
        ((coveredGraph P).neighborFinset v).card :=
      card_le_card inter_subset_left
    _ = (coveredGraph P).degree v :=
      SimpleGraph.card_neighborFinset_eq_degree (coveredGraph P) v
    _ = 2 * (triplesThrough P v).card :=
      hP.coveredGraph_degree_eq_two_mul_triplesThrough v
    _ ≤ 2 * P.card := Nat.mul_le_mul_left 2 (card_filter_le _ _)

/-- If every triangle meets `U` in at most one vertex, then the neighbors in
`U` covered at a fixed center inject into the selected triangles through the
center.  This is the sparse-reserve replacement for the false assertion that
the preliminary family is wholly outside `U`. -/
lemma card_coveredNeighborsIn_le_triplesThrough_of_atMostOne
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {P : TripleSystemOn V}
    (hone : TrianglesMeetAtMostOne U P) (v : V) :
    ((coveredGraph P).neighborFinset v ∩ U).card ≤
      (triplesThrough P v).card := by
  classical
  let S : Finset V := (coveredGraph P).neighborFinset v ∩ U
  have hwitness : ∀ y ∈ S,
      ∃ T : TripleOn V, T ∈ P ∧ v ∈ T.1 ∧ y ∈ T.1 := by
    intro y hy
    have hvy : (coveredGraph P).Adj v y := by
      simpa only [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hy).1
    obtain ⟨T, hTP, hvT, hyT, _⟩ := coveredGraph_adj.mp hvy
    exact ⟨T, hTP, hvT, hyT⟩
  let f : {y // y ∈ S} → {T // T ∈ triplesThrough P v} :=
    fun y ↦ ⟨Classical.choose (hwitness y.1 y.2), by
      have hs := Classical.choose_spec (hwitness y.1 y.2)
      exact mem_filter.mpr ⟨hs.1, hs.2.1⟩⟩
  have hf : Function.Injective f := by
    intro x y hxy
    apply Subtype.ext
    have hx := Classical.choose_spec (hwitness x.1 x.2)
    have hy := Classical.choose_spec (hwitness y.1 y.2)
    have hT : Classical.choose (hwitness x.1 x.2) =
        Classical.choose (hwitness y.1 y.2) := congrArg Subtype.val hxy
    have hyIn : y.1 ∈ (Classical.choose (hwitness x.1 x.2)).1 := by
      rw [hT]
      exact hy.2.2
    have hxU : x.1 ∈ U :=
      (mem_inter.mp (by simpa only [S] using x.2)).2
    have hyU : y.1 ∈ U :=
      (mem_inter.mp (by simpa only [S] using y.2)).2
    exact hone _ hx.1 hx.2.2 hxU hyIn hyU
  have hcard := Fintype.card_le_of_injective f hf
  simpa only [Fintype.card_coe, S] using hcard

/-- A family wholly outside `U` creates no covered neighbor in `U`. -/
lemma TrianglesDisjointFrom.card_coveredNeighborsIn_eq_zero
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {P : TripleSystemOn V}
    (hP : TrianglesDisjointFrom U P) (v : V) :
    ((coveredGraph P).neighborFinset v ∩ U).card = 0 := by
  apply card_eq_zero.mpr
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro w hw
  have hadj : (coveredGraph P).Adj v w := by
    simpa only [SimpleGraph.mem_neighborFinset] using (mem_inter.mp hw).1
  obtain ⟨T, hT, _, hwT, _⟩ := coveredGraph_adj.mp hadj
  exact (Finset.disjoint_left.mp (hP T hT) hwT (mem_inter.mp hw).2).elim

/-- The rooted relative correlated output supplies its own localized loss
bound.  No outer-only hypothesis on the preliminary family is used. -/
theorem RelativeReserveProtectedRootedOutput.localizedLoss
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {d Dint R : ℕ}
    {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedRootedOutput law W next F i
      G A I D bits d Dint R p reserveDensity C b) :
    law.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ W.U i.succ).card ≤ 2 * n + d := by
  intro z hz o
  let U := W.U i.succ
  let pre := relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1
  let P₀ := relativeReserveProtectedP0 I D (z.1, z.2.1)
  let Q := z.2.2.chosen
  let addedInt := Q \ P₀
  have htotal : relativeReserveProtectedTotal I D z.1 z.2 =
      pre ∪ addedInt := by
    rfl
  have hpackingAll := (hout.structural z hz).2.2.1
  have hpackingTotal : IsPackingOn
      (relativeReserveProtectedTotal I D z.1 z.2) :=
    hpackingAll.mono (by
      intro T hT
      exact mem_union_right _ (mem_union_right _ hT))
  have hpackingPre : IsPackingOn pre := hpackingTotal.mono (by
    intro T hT
    rw [htotal]
    exact mem_union_left _ hT)
  have hpreLoss :
      ((coveredGraph pre).neighborFinset o.1 ∩ U).card ≤ 2 * n :=
    (hpackingPre.card_coveredNeighborsIn_le_two_mul_card U o.1).trans
      (Nat.mul_le_mul_left 2 (hout.preliminaryCard z hz))
  have hraw := hout.outcome z hz
  have hP₀Q : P₀ ⊆ Q := hraw.1.1.initial_subset
  have hpackingQ : IsPackingOn Q := by
    have h := hpackingAll
    rw [hout.accumulate z hz] at h
    exact h
  let E := preliminaryResidualInternalEdges (G z.1) U P₀
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) U P₀ he)).2
  have hinternalLoss :
      ((coveredGraph addedInt).neighborFinset o.1 ∩ U).card ≤ d := by
    apply card_coveredNeighborsIn_newInternalAdded_le_scheduledIncidence
      (P₀ := P₀) (Q := Q) (E := E)
    · exact hP₀Q
    · exact hpackingQ
    · exact houter
    · simpa only [E, P₀, U, Q, relativeReserveProtectedP0,
        relativeReserveProtectedAint] using hraw.2.2.1
    · simpa only [E, P₀, U] using hout.incidence z hz
    · exact o.2
  have hsubset :
      (coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ U ⊆
        ((coveredGraph pre).neighborFinset o.1 ∩ U) ∪
          ((coveredGraph addedInt).neighborFinset o.1 ∩ U) := by
    intro v hv
    have hvparts := coveredGraph_union_neighborFinset_subset pre addedInt o.1
      (by
        rw [← htotal]
        exact (mem_inter.mp hv).1)
    have hvU := (mem_inter.mp hv).2
    rcases mem_union.mp hvparts with hvpre | hvint
    · exact mem_union_left _ (mem_inter.mpr ⟨hvpre, hvU⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hvint, hvU⟩)
  exact (card_le_card hsubset).trans
    ((card_union_le _ _).trans (Nat.add_le_add hpreLoss hinternalLoss))

/-- Under a preliminary vertex-star cap, the localized loss is the cap at
the outside center plus the scheduled incidence cutoff of the internal
stage. -/
theorem RelativeReserveProtectedCappedRootedOutput.localizedLoss
    {Omega V : Type*} [Fintype Omega] [DecidableEq Omega]
    [Fintype V] [DecidableEq V] {ell n : ℕ}
    {law : FiniteLaw (RelativeReserveProtectedCorrelatedSample Omega V n)}
    {W : Vortex V ell} {next : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V} {i : Fin ell}
    {G : Omega → SimpleGraph V} {A I D : Omega → TripleSystemOn V}
    {bits : Omega → Sym2 V → Bool} {d Dint R : ℕ}
    {caps : V → ℕ} {p reserveDensity C b : ℝ≥0}
    (hout : RelativeReserveProtectedCappedRootedOutput law W next F i
      G A I D bits d Dint R caps p reserveDensity C b) :
    law.SupportedOn fun z ↦
      ∀ o : {x : V // x ∉ W.U i.succ},
        ((coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ W.U i.succ).card ≤ caps o.1 + d := by
  intro z hz o
  let U := W.U i.succ
  let pre := relativeReserveProtectedPreliminaryAdded I D z.1 z.2.1
  let P₀ := relativeReserveProtectedP0 I D (z.1, z.2.1)
  let Q := z.2.2.chosen
  let addedInt := Q \ P₀
  have htotal : relativeReserveProtectedTotal I D z.1 z.2 =
      pre ∪ addedInt := by
    rfl
  have hpreLoss :
      ((coveredGraph pre).neighborFinset o.1 ∩ U).card ≤ caps o.1 := by
    calc
      ((coveredGraph pre).neighborFinset o.1 ∩ U).card ≤
          (triplesThrough pre o.1).card :=
        card_coveredNeighborsIn_le_triplesThrough_of_atMostOne
          (hout.preliminaryAtMostOne z hz) o.1
      _ ≤ caps o.1 := by
        exact Nat.le_of_lt (by
          simpa only [ambientTriplesThrough_inter, pre] using
            hout.preliminaryCaps z hz o.1)
  have hraw := hout.outcome z hz
  have hP₀Q : P₀ ⊆ Q := hraw.1.1.initial_subset
  have hpackingAll := (hout.structural z hz).2.2.1
  have hpackingQ : IsPackingOn Q := by
    have h := hpackingAll
    rw [hout.accumulate z hz] at h
    exact h
  let E := preliminaryResidualInternalEdges (G z.1) U P₀
  have houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G z.1) U P₀ he)).2
  have hinternalLoss :
      ((coveredGraph addedInt).neighborFinset o.1 ∩ U).card ≤ d := by
    apply card_coveredNeighborsIn_newInternalAdded_le_scheduledIncidence
      (P₀ := P₀) (Q := Q) (E := E)
    · exact hP₀Q
    · exact hpackingQ
    · exact houter
    · simpa only [E, P₀, U, Q, relativeReserveProtectedP0,
        relativeReserveProtectedAint] using hraw.2.2.1
    · simpa only [E, P₀, U] using hout.incidence z hz
    · exact o.2
  have hsubset :
      (coveredGraph (relativeReserveProtectedTotal I D z.1 z.2)).neighborFinset
          o.1 ∩ U ⊆
        ((coveredGraph pre).neighborFinset o.1 ∩ U) ∪
          ((coveredGraph addedInt).neighborFinset o.1 ∩ U) := by
    intro v hv
    have hvparts := coveredGraph_union_neighborFinset_subset pre addedInt o.1
      (by
        rw [← htotal]
        exact (mem_inter.mp hv).1)
    have hvU := (mem_inter.mp hv).2
    rcases mem_union.mp hvparts with hvpre | hvint
    · exact mem_union_left _ (mem_inter.mpr ⟨hvpre, hvU⟩)
    · exact mem_union_right _ (mem_inter.mpr ⟨hvint, hvU⟩)
  exact (card_le_card hsubset).trans
    ((card_union_le _ _).trans (Nat.add_le_add hpreLoss hinternalLoss))

end

end Erdos207
