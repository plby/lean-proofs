/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeScheduledStarBound
import ErdosProblems.Erdos207.InternalEdgeRandomCoverStage

/-!
# Internal random greedy cover on a residual outer-edge schedule

The original specialized internal kernel scheduled every outer edge of the
stage graph.  After the preliminary process, only the residual outer edges
need this treatment.  This file keeps the original graph and available
triangle family for typical candidate supply, while allowing an arbitrary
subfamily of its outer edges to be scheduled.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Reserve concentration and the scheduled random greedy argument for an
arbitrary residual subfamily of the stage's outer edges. -/
theorem IsIterationTypical.exists_scheduledOuterEdge_randomGreedyLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P0 : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (E : Finset (Sym2 V))
    (hE : E ⊆ internalOuterEdges G (W.U i.succ))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a D : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : (E.card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hblocked : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P0 Q,
      Q ⊆ P0 ∪ A →
      (Q \ P0).card ≤ E.card →
      NewTrianglesUseScheduledOuterEdges (W.U i.succ) E P0 Q →
      ∀ he : e ∈ E,
      ∀ hleave : (leaveGraph Q).Adj e.out.1 e.out.2,
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ)
              (hE he))) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ)
              (hE he)))).card ≤ a) :
    ∃ omega : Sym2 V → Bool,
      let S : Sym2 V → Finset V := fun e ↦
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (hE (by simpa only [Finset.mem_toList] using he)))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
        E.toList hne D P0
      L.SupportedOn (fun z ↦
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card ≤ E.card ∧
          (∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
          NewTrianglesUseScheduledOuterEdges
            (W.U i.succ) E P0 z.chosen) ∧
      ∀ Q : TripleSystemOn V, Disjoint Q P0 →
        L.probability (fun z ↦ Q ⊆ z.chosen) ≤
          (Q.card.factorial : ℝ≥0) * ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ) (hE he)
  have hadj : ∀ e ∈ E, G.Adj e.out.1 e.out.2 := by
    intro e he
    exact graph_adj_out_of_mem_graphEdges (hedge e he)
  have houter : ∀ e ∈ E,
      e.out.1 ∈ W.U i.castSucc ∧ e.out.2 ∈ W.U i.castSucc := by
    intro e he
    exact hGsupp (hadj e he)
  have hinner : ∀ e ∈ E,
      e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (hE he)).2
  obtain ⟨omega, homega⟩ :=
    htyp.exists_reserve_realization_with_internal_supplies htri i hstage E
      (fun e : Sym2 V ↦ e.out.1) (fun e : Sym2 V ↦ e.out.2)
      (fun e he ↦ out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (fun e he ↦ (houter e he).1) (fun e he ↦ (houter e he).2)
      (fun e he ↦ (hinner e he).1) (fun e he ↦ (hinner e he).2)
      hadj hh r hr m hm (fun _e ↦ a + D) (fun _e _he ↦ ha) hsmall
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (hedge e (by simpa only [Finset.mem_toList] using he))
  have hElist : E.toList.toFinset = E := by
    ext e
    simp
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (hinner e (by simpa only [Finset.mem_toList] using he)).1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (hinner e (by simpa only [Finset.mem_toList] using he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hAactive : ∀ e (he : e ∈ E.toList)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G (W.U i.succ) (S e)
        e.out.1 e.out.2 omega →
      internalEdgeTriangle e (hne e he) w ∈ A := by
    intro e he w hw
    have hwS := (mem_activeReserveWedgeVertices_iff.mp hw).1
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hwS
  have hfloor : ∀ Q e (he : e ∈ E.toList), GreedyReachable F P0 Q →
      Q ⊆ P0 ∪ A → (Q \ P0).card ≤ E.toList.length →
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E.toList.toFinset P0 Q →
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 →
      D ≤ (activeReserveLegalThirdVertices F G (W.U i.succ) (S e)
        omega Q e.out.1 e.out.2 (hne e he)).card := by
    intro Q e he hreach hsub hcard huse huncovered
    have heE : e ∈ E := by simpa only [Finset.mem_toList] using he
    have hleave : (leaveGraph Q).Adj e.out.1 e.out.2 := by
      apply leaveGraph_adj.mpr
      refine ⟨hne e he, ?_⟩
      rintro ⟨T, hTQ, hleft, hright, hneT⟩
      exact huncovered (coveredGraph_adj.mpr
        ⟨T, hTQ, hleft, hright, hneT⟩)
    have hcardE : (Q \ P0).card ≤ E.card := by
      simpa only [Finset.length_toList] using hcard
    have huseE :
        NewTrianglesUseScheduledOuterEdges (W.U i.succ) E P0 Q := by
      simpa only [hElist] using huse
    have hblock := hblocked Q e hreach hsub hcardE huseE heE hleave
    have hsupply := homega e heE
    dsimp only [S] at hsupply
    have hcount :
        (edgeBlockedThirdVertices A Q hleave.ne ∪
          forbiddenBlockedThirdVertices F A Q hleave.ne).card + D ≤
        (activeReserveWedgeVertices G (W.U i.succ) (S e)
          e.out.1 e.out.2 omega).card := by
      have hproof : hleave.ne =
          out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ)
              (hE heE)) := Subsingleton.elim _ _
      rw [hproof]
      dsimp only [S] at ⊢
      omega
    have hA : ∀ w, ∀ hwS : w ∈ S e,
        let w' : ThirdVertex e.out.1 e.out.2 :=
          ⟨w, fun h ↦ hu e he (h ▸ hSU e he hwS),
            fun h ↦ hv e he (h ▸ hSU e he hwS)⟩
        thirdVertexTriple hleave.ne w' ∈ A := by
      intro w hwS
      exact iterationExtensionVertices_edge_thirdVertexTriple_mem
        hleave.ne (hu e he) (hv e he) hwS
    have hlegal := card_activeReserveLegalThirdVertices_ge_of_blocked_add_le
      (hreach.isPacking hpacking0) (hreach.avoidsForbidden havoid0)
      hleave (hu e he) (hv e he) (hSU e he) omega hA D hcount
    simpa only using hlegal
  let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
    E.toList hne D P0
  have hcomplete :=
    internalEdgeGreedyProcessLaw_supported_complete_ambient_scheduled
      F G (W.U i.succ) omega S E.toList hne hSU D hD P0 A
        hAactive hfloor
  have hsupp : L.SupportedOn (fun z ↦
      GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
        (z.chosen \ P0).card ≤ E.card ∧
        (∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
        NewTrianglesUseScheduledOuterEdges
          (W.U i.succ) E P0 z.chosen) := by
    intro z hz
    have hz' := hcomplete z hz
    refine ⟨hz'.1.1, hz'.2.2.1, ?_, ?_, ?_⟩
    · simpa only [Finset.length_toList] using hz'.1.2.1
    · intro e he
      exact hz'.1.covers_mem hz'.2.1 e
        (by simpa only [Finset.mem_toList] using he)
    · simpa only [hElist] using hz'.2.2.2
  refine ⟨omega, ?_⟩
  dsimp only
  refine ⟨hsupp, ?_⟩
  intro Q hdisjoint
  exact internalEdgeGreedyProcess_probability_subset_chosen_le
    F G (W.U i.succ) omega S E.toList hne E.nodup_toList hu hv hSU
      D hD P0 Q hdisjoint

/-- Residual incidence and a uniform rooted-threat bound imply the blocker
premise of the arbitrary scheduled-edge kernel. -/
theorem IsIterationTypical.exists_scheduledOuterEdge_randomGreedyLaw_of_rooted
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P0 : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (E : Finset (Sym2 V))
    (hE : E ⊆ internalOuterEdges G (W.U i.succ))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m a D d R k : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmall : (E.card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hroot : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      GreedyReachable F P0 Q →
      Q ⊆ P0 ∪ A →
      (Q \ P0).card ≤ E.card →
      e ∈ E →
      NewTrianglesUseScheduledOuterEdges (W.U i.succ) E P0 Q →
      (rootedActiveForbiddenConfigurations F Q
        e.out.1 e.out.2).card ≤ R)
    (hscalar : 4 * d + R * k ≤ a) :
    ∃ omega : Sym2 V → Bool,
      let S : Sym2 V → Finset V := fun e ↦
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (hE (by simpa only [Finset.mem_toList] using he)))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
        E.toList hne D P0
      L.SupportedOn (fun z ↦
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card ≤ E.card ∧
          (∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
          NewTrianglesUseScheduledOuterEdges
            (W.U i.succ) E P0 z.chosen) ∧
      ∀ Q : TripleSystemOn V, Disjoint Q P0 →
        L.probability (fun z ↦ Q ⊆ z.chosen) ≤
          (Q.card.factorial : ℝ≥0) * ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  apply htyp.exists_scheduledOuterEdge_randomGreedyLaw htri i hstage
    hGsupp E hE hpacking0 havoid0 hh r hr m a D hD hm ha hsmall
  intro Q e hreach hsub hcard huseQ he hleave
  have houter : ∀ f ∈ E,
      f.out.1 ∉ W.U i.succ ∧ f.out.2 ∉ W.U i.succ := by
    intro f hf
    exact (mem_internalOuterEdges_iff.mp (hE hf)).2
  obtain ⟨hdu, hdv⟩ := new_endpoint_stars_le_of_scheduled_incidence
    (hreach.isPacking hpacking0) houter huseQ hincidence he
  exact card_blockedThirdVertices_le_four_mul_add_mul
    (hreach.isPacking hpacking0) hinitial hleave hdu hdv
      (hroot Q e hreach hsub hcard he huseQ) hfamily hscalar

end

end Erdos207
