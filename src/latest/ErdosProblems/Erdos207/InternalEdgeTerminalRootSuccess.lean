/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeResidualSchedule
import ErdosProblems.Erdos207.RootedThreatExtraction
import ErdosProblems.Erdos207.SharpInternalEdgeC4Law

/-!
# Retrospective success from a terminal rooted cap

The scheduled internal process freezes its chosen family as soon as its
failure bit is set.  Consequently a failed terminal state remembers an
uncovered scheduled edge whose legal candidate set had size below the
threshold.  If the terminal family satisfies the desired rooted cap, the
scheduled-incidence estimate and reserve surplus contradict that failure
certificate.  This removes the circular requirement that a rooted cap be
postulated for every hypothetical prefix before the random process is run.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- A failed state remembers an already exposed scheduled edge which was
uncovered and had fewer than `D` legal reserve choices. -/
def InternalEdgeFailureCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (bits : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (D k : ℕ) (z : InternalEdgeGreedyStateOn V) : Prop :=
  z.failed = true →
    ∃ j, ∃ hj : j < edges.length, j < k ∧
      ¬(coveredGraph z.chosen).Adj
        (edges.get ⟨j, hj⟩).out.1 (edges.get ⟨j, hj⟩).out.2 ∧
      (activeReserveLegalThirdVertices F G U
        (S (edges.get ⟨j, hj⟩)) bits z.chosen
        (edges.get ⟨j, hj⟩).out.1 (edges.get ⟨j, hj⟩).out.2
        (hne _ (List.get_mem edges ⟨j, hj⟩))).card < D

/-- One scheduled transition preserves an old failure witness or records the
current edge when the threshold test fails. -/
theorem internalEdgeGreedyKernel_supported_failureCertificate_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (bits : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (D : ℕ) (hD : 0 < D) (i : ℕ) (hi : i < edges.length)
    (z : InternalEdgeGreedyStateOn V)
    (hz : InternalEdgeFailureCertificate F G U bits S edges hne D i z) :
    (internalEdgeGreedyKernel F G U bits S edges hne D i z).SupportedOn
      (InternalEdgeFailureCertificate F G U bits S edges hne D (i + 1)) := by
  classical
  by_cases hfailed : z.failed = true
  · simp only [internalEdgeGreedyKernel, hfailed]
    apply FiniteLaw.supportedOn_pure
    intro _htrue
    obtain ⟨j, hj, hji, huncovered, hsmall⟩ := hz hfailed
    exact ⟨j, hj, hji.trans (Nat.lt_succ_self i), huncovered, hsmall⟩
  · have hzfalse : z.failed = false := Bool.eq_false_of_not_eq_true hfailed
    simp only [internalEdgeGreedyKernel, hzfalse, Bool.false_eq_true,
      hi, dite_true]
    let e := edges.get ⟨i, hi⟩
    let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
    let huv : e.out.1 ≠ e.out.2 := hne e he
    by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
    · simp only [e, he, huv, hcovered, dite_true]
      apply FiniteLaw.supportedOn_pure
      intro htrue
      simp [hzfalse] at htrue
    · simp only [e, he, huv, hcovered, dite_false]
      let C := activeReserveLegalThirdVertices F G U (S e) bits
        z.chosen e.out.1 e.out.2 huv
      by_cases hlarge : D ≤ C.card
      · rw [dif_pos (by simpa only [C, e, he, huv] using hlarge)]
        have hC : C.Nonempty := card_pos.mp (hD.trans_le hlarge)
        rw [dif_pos (by simpa only [C, e, he, huv] using hC)]
        let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
        have huLaw : FiniteLaw.SupportedOn (fun _ : C ↦ True)
            (FiniteLaw.uniform : FiniteLaw C) :=
          FiniteLaw.uniform_supported _ fun _ ↦ trivial
        refine huLaw.map
          (fun w : C ↦
            ({ chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
               failed := false } : InternalEdgeGreedyStateOn V)) ?_
        intro _w _hw
        intro htrue
        simp at htrue
      · rw [dif_neg (by simpa only [C, e, he, huv] using hlarge)]
        apply FiniteLaw.supportedOn_pure
        intro _htrue
        refine ⟨i, hi, Nat.lt_succ_self i, ?_, ?_⟩
        · simpa only [e] using hcovered
        · simpa only [C, e, he, huv] using (Nat.lt_of_not_ge hlarge)

/-- Every terminal state of the scheduled law carries the failure witness
certificate. -/
theorem internalEdgeGreedyProcessLaw_supported_failureCertificate
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (bits : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (D : ℕ) (hD : 0 < D) (P0 : TripleSystemOn V) :
    (internalEdgeGreedyProcessLaw F G U bits S edges hne D P0).SupportedOn
      (InternalEdgeFailureCertificate F G U bits S edges hne D
        edges.length) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k ≤ edges.length →
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U bits S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (InternalEdgeFailureCertificate F G U bits S edges hne D k) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      simp [z0, InternalEdgeFailureCertificate]
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U bits S edges hne D k) ?_
      intro z hz
      exact internalEdgeGreedyKernel_supported_failureCertificate_step
        F G U bits S edges hne D hD k (by omega) z hz

/-- The raw scheduled process preserves containment in the ambient triangle
family even when it freezes on a failed threshold test. -/
theorem internalEdgeGreedyProcessLaw_supported_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (bits : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (D : ℕ) (P0 A : TripleSystemOn V)
    (hAactive : ∀ e (he : e ∈ edges)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 bits →
      internalEdgeTriangle e (hne e he) w ∈ A)
    :
    (internalEdgeGreedyProcessLaw F G U bits S edges hne D P0).SupportedOn
      (fun z ↦ z.chosen ⊆ P0 ∪ A) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k ≤ edges.length →
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U bits S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (fun z ↦ z.chosen ⊆ P0 ∪ A) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      simp [z0]
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U bits S edges hne D k) ?_
      intro z hz
      classical
      by_cases hfailed : z.failed = true
      · simp only [internalEdgeGreedyKernel, hfailed]
        exact FiniteLaw.supportedOn_pure _ hz
      · have hzfalse : z.failed = false :=
          Bool.eq_false_of_not_eq_true hfailed
        simp only [internalEdgeGreedyKernel, hzfalse, Bool.false_eq_true,
          show k < edges.length by omega, dite_true]
        let e := edges.get ⟨k, by omega⟩
        let he : e ∈ edges := List.get_mem edges ⟨k, by omega⟩
        let huv : e.out.1 ≠ e.out.2 := hne e he
        by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
        · simp only [e, he, huv, hcovered, dite_true]
          exact FiniteLaw.supportedOn_pure _ hz
        · simp only [e, he, huv, hcovered, dite_false]
          let C := activeReserveLegalThirdVertices F G U (S e) bits
            z.chosen e.out.1 e.out.2 huv
          by_cases hlarge : D ≤ C.card
          · rw [dif_pos (by simpa only [C, e, he, huv] using hlarge)]
            by_cases hC : C.Nonempty
            · rw [dif_pos (by simpa only [C, e, he, huv] using hC)]
              let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
              have huLaw : FiniteLaw.SupportedOn (fun _ : C ↦ True)
                  (FiniteLaw.uniform : FiniteLaw C) :=
                FiniteLaw.uniform_supported _ fun _ ↦ trivial
              refine huLaw.map
                (fun w : C ↦
                  ({ chosen := insert (internalEdgeTriangle e huv w.1)
                      z.chosen
                     failed := false } : InternalEdgeGreedyStateOn V)) ?_
              intro w _hw T hT
              rcases mem_insert.mp hT with rfl | hT
              · apply mem_union_right
                exact hAactive e he w.1
                  (mem_activeReserveLegalThirdVertices_iff.mp w.2).1
              · exact hz hT
            · rw [dif_neg (by simpa only [C, e, he, huv] using hC)]
              exact FiniteLaw.supportedOn_pure _ hz
          · rw [dif_neg (by simpa only [C, e, he, huv] using hlarge)]
            exact FiniteLaw.supportedOn_pure _ hz

/-- A terminal rooted cap, scheduled incidence, and reserve surplus rule out
the remembered failure witness. -/
theorem internalEdge_terminal_notFailed_of_rootedCap
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U : Finset V}
    {bits : Sym2 V → Bool} {S : Sym2 V → Finset V}
    {E : Finset (Sym2 V)}
    {hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2}
    {D a d R k : ℕ} {P0 A : TripleSystemOn V}
    {z : InternalEdgeGreedyStateOn V}
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hinitial : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P0) T)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (hincidence : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    (hsupply : ∀ e ∈ E,
      a + D ≤ (activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 bits).card)
    (hSU : ∀ e, e ∈ E.toList → S e ⊆ U)
    (hA : ∀ e (he : e ∈ E.toList) (w : V), ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (houter e (by simpa only [Finset.mem_toList] using he)).1
            (h ▸ hSU e he hw),
          fun h ↦ (houter e (by simpa only [Finset.mem_toList] using he)).2
            (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A)
    (hscalar : 4 * d + R * k ≤ a)
    (hinv : InternalEdgeProcessInvariant F P0 E.toList E.toList.length z)
    (hambient : z.chosen ⊆ P0 ∪ A)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 z.chosen)
    (hfailure : InternalEdgeFailureCertificate F G U bits S E.toList hne
      D E.toList.length z)
    (hroot : RootedActiveCapsGood F z.chosen R) :
    z.failed = false := by
  apply Bool.eq_false_of_not_eq_true
  intro hfailed
  obtain ⟨j, hj, _hjlen, huncovered, hsmall⟩ := hfailure hfailed
  let e := E.toList.get ⟨j, hj⟩
  have heList : e ∈ E.toList := List.get_mem E.toList ⟨j, hj⟩
  have heE : e ∈ E := by simpa only [Finset.mem_toList] using heList
  have hleave : (leaveGraph z.chosen).Adj e.out.1 e.out.2 := by
    apply leaveGraph_adj.mpr
    refine ⟨hne e heList, ?_⟩
    rintro ⟨T, hT, hu, hv, hneT⟩
    exact huncovered (coveredGraph_adj.mpr ⟨T, hT, hu, hv, hneT⟩)
  obtain ⟨hdu, hdv⟩ := new_endpoint_stars_le_of_scheduled_incidence
    (hinv.1.isPacking hpacking0) houter huse hincidence heE
  have hrootE :
      (rootedActiveForbiddenConfigurations F z.chosen
        e.out.1 e.out.2).card ≤ R :=
    hroot e.out.1 e.out.2 (hne e heList)
  have hblocked :
      (edgeBlockedThirdVertices A z.chosen hleave.ne ∪
        forbiddenBlockedThirdVertices F A z.chosen hleave.ne).card ≤ a :=
    card_blockedThirdVertices_le_four_mul_add_mul
      (hinv.1.isPacking hpacking0) hinitial hleave hdu hdv hrootE hfamily
        hscalar
  have hcount :
      (edgeBlockedThirdVertices A z.chosen hleave.ne ∪
          forbiddenBlockedThirdVertices F A z.chosen hleave.ne).card + D ≤
        (activeReserveWedgeVertices G U (S e)
          e.out.1 e.out.2 bits).card :=
    (Nat.add_le_add_right hblocked D).trans (hsupply e heE)
  have hA' : ∀ w, ∀ hwS : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (houter e heE).1 (h ▸ hSU e heList hwS),
          fun h ↦ (houter e heE).2 (h ▸ hSU e heList hwS)⟩
      thirdVertexTriple hleave.ne w' ∈ A := by
    intro w hwS
    have hp : hleave.ne = hne e heList := Subsingleton.elim _ _
    rw [hp]
    exact hA e heList w hwS
  have hlegal := card_activeReserveLegalThirdVertices_ge_of_blocked_add_le
    (hinv.1.isPacking hpacking0) (hinv.1.avoidsForbidden havoid0)
    hleave (houter e heE).1 (houter e heE).2 (hSU e heList) bits hA' D
      hcount
  have hp : hleave.ne = hne e heList := Subsingleton.elim _ _
  rw [hp] at hlegal
  exact (not_lt_of_ge hlegal) (by simpa only [e] using hsmall)

/-- Reserve concentration may be performed before the rooted cap is known.
The raw scheduled law retains its sharp inclusion bound, and every terminal
outcome satisfying the cap is then certified successful retrospectively. -/
theorem IsIterationTypical.exists_scheduledOuterEdge_rawLaw_terminalRootSuccess
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
    (hscalar : 4 * d + R * k ≤ a) :
    ∃ bits : Sym2 V → Bool,
      let S : Sym2 V → Finset V := fun e ↦
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (hE (by simpa only [Finset.mem_toList] using he)))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
        E.toList hne D P0
      L.SupportedOn (fun z ↦
        InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
        z.chosen ⊆ P0 ∪ A ∧
        NewTrianglesUseScheduledOuterEdges
          (W.U i.succ) E P0 z.chosen ∧
        InternalEdgeFailureCertificate F G (W.U i.succ) bits S E.toList
          hne D E.toList.length z) ∧
      (∀ z, 0 < L.mass z → RootedActiveCapsGood F z.chosen R →
        z.failed = false ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
          ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ) (hE he)
  have hadj : ∀ e ∈ E, G.Adj e.out.1 e.out.2 := by
    intro e he
    exact graph_adj_out_of_mem_graphEdges (hedge e he)
  have houterSupport : ∀ e ∈ E,
      e.out.1 ∈ W.U i.castSucc ∧ e.out.2 ∈ W.U i.castSucc := by
    intro e he
    exact hGsupp (hadj e he)
  have houter : ∀ e ∈ E,
      e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp (hE he)).2
  obtain ⟨bits, hbits⟩ :=
    htyp.exists_reserve_realization_with_internal_supplies htri i hstage E
      (fun e : Sym2 V ↦ e.out.1) (fun e : Sym2 V ↦ e.out.2)
      (fun e he ↦ out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (fun e he ↦ (houterSupport e he).1)
      (fun e he ↦ (houterSupport e he).2)
      (fun e he ↦ (houter e he).1) (fun e he ↦ (houter e he).2)
      hadj hh r hr m hm (fun _e ↦ a + D) (fun _e _he ↦ ha) hsmall
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    exact out_fst_ne_snd_of_mem_graphEdges
      (hedge e (by simpa only [Finset.mem_toList] using he))
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (houter e (by simpa only [Finset.mem_toList] using he)).2
  have hSU : ∀ e, e ∈ E.toList → S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hAactive : ∀ e (he : e ∈ E.toList)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G (W.U i.succ) (S e)
        e.out.1 e.out.2 bits →
      internalEdgeTriangle e (hne e he) w ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he)
      (mem_activeReserveWedgeVertices_iff.mp hw).1
  have hAplain : ∀ e (he : e ∈ E.toList) (w : V), ∀ hw : w ∈ S e,
      let w' : ThirdVertex e.out.1 e.out.2 :=
        ⟨w, fun h ↦ (hu e he) (h ▸ hSU e he hw),
          fun h ↦ (hv e he) (h ▸ hSU e he hw)⟩
      thirdVertexTriple (hne e he) w' ∈ A := by
    intro e he w hw
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hw
  let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
    E.toList hne D P0
  have hinv := internalEdgeGreedyProcessLaw_supported_processInvariant
    F G (W.U i.succ) bits S E.toList hne D P0
  have hambient := internalEdgeGreedyProcessLaw_supported_ambient
    F G (W.U i.succ) bits S E.toList hne D P0 A hAactive
  have huseList := internalEdgeGreedyProcessLaw_supported_usesScheduledOuterEdges
    F G (W.U i.succ) bits S E.toList hne hSU D P0
  have hElist : E.toList.toFinset = E := by
    ext e
    simp
  have huse : L.SupportedOn (fun z ↦
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E P0 z.chosen) := by
    intro z hz
    have hz' := huseList z hz
    simpa only [hElist] using hz'
  have hfailure := internalEdgeGreedyProcessLaw_supported_failureCertificate
    F G (W.U i.succ) bits S E.toList hne D hD P0
  have hall : L.SupportedOn (fun z ↦
      InternalEdgeProcessInvariant F P0 E.toList E.toList.length z ∧
      z.chosen ⊆ P0 ∪ A ∧
      NewTrianglesUseScheduledOuterEdges
        (W.U i.succ) E P0 z.chosen ∧
      InternalEdgeFailureCertificate F G (W.U i.succ) bits S E.toList
        hne D E.toList.length z) := by
    intro z hz
    exact ⟨hinv z hz, hambient z hz, huse z hz, hfailure z hz⟩
  refine ⟨bits, ?_⟩
  dsimp only
  refine ⟨hall, ?_, ?_⟩
  · intro z hz hroot
    have hzall := hall z hz
    have hfalse := internalEdge_terminal_notFailed_of_rootedCap
      hpacking0 havoid0 hinitial hfamily houter hincidence
        (fun e he ↦ Nat.le_of_lt (hbits e he)) hSU
        hAplain hscalar hzall.1 hzall.2.1 hzall.2.2.1 hzall.2.2.2 hroot
    refine ⟨hfalse, ?_⟩
    intro e he
    exact hzall.1.covers_mem hfalse e
      (by simpa only [Finset.mem_toList] using he)
  · intro Q
    exact internalEdgeGreedyProcess_probability_subset_newChosen_le_sharp
      F G (W.U i.succ) bits S E.toList hne E.nodup_toList hu hv hSU
        D hD P0 Q

end

end Erdos207
