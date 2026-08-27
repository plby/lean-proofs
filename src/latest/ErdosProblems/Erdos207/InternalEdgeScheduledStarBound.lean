/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomCoverStage

/-!
# Endpoint-star bounds for an arbitrary scheduled outer-edge family

The internal cover is scheduled by the *uncovered* outer edges left by the
preliminary stage.  Its candidate triangles still live in the original
ambient graph, so bounding their endpoint stars by the degree of that ambient
graph loses the crucial preliminary sparsification.  This file separates the
two notions.  If every newly inserted triangle uses one scheduled edge and an
inner third vertex, packinghood injects the triangles through an outer vertex
into the scheduled edges incident with that vertex.
-/

namespace Erdos207

open Finset

noncomputable section

/-- Every triangle newly added after `P0` consists of a scheduled edge and a
third vertex in `U`. -/
def NewTrianglesUseScheduledOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (E : Finset (Sym2 V))
    (P0 Q : TripleSystemOn V) : Prop :=
  ∀ T ∈ Q \ P0, ∃ e ∈ E, ∃ (hne : e.out.1 ≠ e.out.2),
    ∃ w : ThirdVertex e.out.1 e.out.2,
      w.1 ∈ U ∧ T = internalEdgeTriangle e hne w

/-- The scheduled edges incident with a displayed vertex. -/
def scheduledEdgesAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (E : Finset (Sym2 V)) (v : V) : Finset (Sym2 V) :=
  E.filter fun e ↦ v ∈ e

@[simp]
lemma mem_scheduledEdgesAt_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {E : Finset (Sym2 V)} {v : V} {e : Sym2 V} :
    e ∈ scheduledEdgesAt E v ↔ e ∈ E ∧ v ∈ e := by
  simp [scheduledEdgesAt]

/-- Removing the inner set from a scheduled triangle leaves exactly its two
outer endpoints. -/
lemma thirdVertexTriple_sdiff_inner
    {V : Type*} [DecidableEq V] {U : Finset V}
    {u v : V} (huv : u ≠ v) (w : ThirdVertex u v)
    (hu : u ∉ U) (hv : v ∉ U) (hw : w.1 ∈ U) :
    (thirdVertexTriple huv w).1 \ U = {u, v} := by
  ext x
  simp only [thirdVertexTriple, tripleOfThree, mem_sdiff, mem_insert,
    mem_singleton]
  aesop

/-- Packinghood makes the outer endpoint pair determine a newly inserted
scheduled triangle. -/
theorem card_triplesThrough_sdiff_le_scheduledEdgesAt
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P0 Q : TripleSystemOn V}
    (hpacking : IsPackingOn Q)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 Q)
    {v : V} (hv : v ∉ U) :
    (triplesThrough (Q \ P0) v).card ≤ (scheduledEdgesAt E v).card := by
  let target : Finset (Finset V) :=
    (scheduledEdgesAt E v).image fun e ↦ {e.out.1, e.out.2}
  have htargetCard : target.card ≤ (scheduledEdgesAt E v).card := by
    exact card_image_le
  apply le_trans (b := target.card) _ htargetCard
  apply Finset.card_le_card_of_injOn (fun T : TripleOn V ↦ T.1 \ U)
  · intro T hT
    have hTnew : T ∈ Q \ P0 := (mem_filter.mp hT).1
    have hvT : v ∈ T.1 := (mem_filter.mp hT).2
    obtain ⟨e, heE, hne, w, hwU, rfl⟩ := huse T hTnew
    have heOuter := houter e heE
    have hpair := thirdVertexTriple_sdiff_inner hne w
      heOuter.1 heOuter.2 hwU
    apply mem_image.mpr
    refine ⟨e, ?_, hpair.symm⟩
    apply mem_scheduledEdgesAt_iff.mpr
    refine ⟨heE, ?_⟩
    have hvPair : v ∈ ({e.out.1, e.out.2} : Finset V) := by
      rw [← hpair]
      exact mem_sdiff.mpr ⟨hvT, hv⟩
    rcases mem_insert.mp hvPair with hvleft | hvright
    · subst v
      exact Sym2.out_fst_mem e
    · have hvright' : v = e.out.2 := by simpa using hvright
      subst v
      exact Sym2.out_snd_mem e
  · intro T hT T' hT' heq
    have hTnew : T ∈ Q \ P0 := (mem_filter.mp hT).1
    have hT'new : T' ∈ Q \ P0 := (mem_filter.mp hT').1
    obtain ⟨e, heE, hne, w, hwU, hTeq⟩ := huse T hTnew
    have heOuter := houter e heE
    have hpairT : T.1 \ U = {e.out.1, e.out.2} := by
      rw [hTeq]
      exact thirdVertexTriple_sdiff_inner hne w
        heOuter.1 heOuter.2 hwU
    have hleftT : e.out.1 ∈ T.1 := by
      rw [hTeq]
      exact left_mem_thirdVertexTriple hne w
    have hrightT : e.out.2 ∈ T.1 := by
      rw [hTeq]
      exact right_mem_thirdVertexTriple hne w
    have hleftT' : e.out.1 ∈ T'.1 := by
      have : e.out.1 ∈ T'.1 \ U := by
        have heq' : T.1 \ U = T'.1 \ U := heq
        rw [← heq', hpairT]
        simp
      exact (mem_sdiff.mp this).1
    have hrightT' : e.out.2 ∈ T'.1 := by
      have : e.out.2 ∈ T'.1 \ U := by
        have heq' : T.1 \ U = T'.1 \ U := heq
        rw [← heq', hpairT]
        simp
      exact (mem_sdiff.mp this).1
    exact hpacking e.out.1 e.out.2 hne T (mem_sdiff.mp hTnew).1
      hleftT hrightT T' (mem_sdiff.mp hT'new).1 hleftT' hrightT'

/-- A uniform residual-incidence cutoff gives the endpoint-star estimate
needed by the internal blocker bound. -/
theorem new_endpoint_stars_le_of_scheduled_incidence
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {E : Finset (Sym2 V)}
    {P0 Q : TripleSystemOn V} {d : ℕ}
    (hpacking : IsPackingOn Q)
    (houter : ∀ e ∈ E, e.out.1 ∉ U ∧ e.out.2 ∉ U)
    (huse : NewTrianglesUseScheduledOuterEdges U E P0 Q)
    (hdegree : ∀ v : V, (scheduledEdgesAt E v).card ≤ d)
    {e : Sym2 V} (he : e ∈ E) :
    (triplesThrough (Q \ P0) e.out.1).card ≤ d ∧
      (triplesThrough (Q \ P0) e.out.2).card ≤ d := by
  have heOuter := houter e he
  exact ⟨(card_triplesThrough_sdiff_le_scheduledEdgesAt
      hpacking houter huse heOuter.1).trans (hdegree e.out.1),
    (card_triplesThrough_sdiff_le_scheduledEdgesAt
      hpacking houter huse heOuter.2).trans (hdegree e.out.2)⟩

/-- One scheduled transition preserves the provenance of every triangle
inserted after the initial family. -/
theorem internalEdgeGreedyKernel_supported_usesScheduledOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (hSU : ∀ e, e ∈ edges → S e ⊆ U)
    (D i : ℕ) (P0 : TripleSystemOn V)
    (z : InternalEdgeGreedyStateOn V)
    (hz : NewTrianglesUseScheduledOuterEdges U edges.toFinset P0 z.chosen) :
    (internalEdgeGreedyKernel F G U omega S edges hne D i z).SupportedOn
      (fun z' ↦ NewTrianglesUseScheduledOuterEdges
        U edges.toFinset P0 z'.chosen) := by
  classical
  by_cases hzfailed : z.failed = false
  · simp only [internalEdgeGreedyKernel, hzfailed, Bool.false_eq_true,
      dite_false]
    by_cases hi : i < edges.length
    · simp only [hi, dite_true]
      let e := edges.get ⟨i, hi⟩
      let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
      let huv : e.out.1 ≠ e.out.2 := hne e he
      by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
      · simp only [e, he, huv, hcovered, dite_true]
        exact FiniteLaw.supportedOn_pure _ hz
      · simp only [e, he, huv, hcovered, dite_false]
        let C := activeReserveLegalThirdVertices F G U (S e) omega
          z.chosen e.out.1 e.out.2 huv
        by_cases hlarge : D ≤ C.card
        · rw [dif_pos (by simpa only [C, e, huv, he] using hlarge)]
          by_cases hC : C.Nonempty
          · rw [dif_pos (by simpa only [C, e, huv, he] using hC)]
            letI : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
            have huLaw : FiniteLaw.SupportedOn (fun _ : C ↦ True)
                (FiniteLaw.uniform : FiniteLaw C) :=
              FiniteLaw.uniform_supported _ fun _ ↦ trivial
            refine huLaw.map
              (fun w : C ↦
                ({ chosen := insert (internalEdgeTriangle e huv w.1)
                    z.chosen
                   failed := false } : InternalEdgeGreedyStateOn V)) ?_
            intro w _hw T hT
            obtain ⟨hTinsert, hTnotP0⟩ := mem_sdiff.mp hT
            rcases mem_insert.mp hTinsert with hnew | hold
            · subst T
              refine ⟨e, by simpa using he,
                huv, w.1, ?_, rfl⟩
              apply hSU e he
              exact (mem_activeReserveWedgeVertices_iff.mp
                (mem_activeReserveLegalThirdVertices_iff.mp w.2).1).1
            · exact hz T (mem_sdiff.mpr ⟨hold, hTnotP0⟩)
          · rw [dif_neg (by simpa only [C, e, huv, he] using hC)]
            apply FiniteLaw.supportedOn_pure
            simpa only using hz
        · rw [dif_neg (by simpa only [C, e, huv, he] using hlarge)]
          apply FiniteLaw.supportedOn_pure
          simpa only using hz
    · simp only [hi, dite_false]
      exact FiniteLaw.supportedOn_pure _ hz
  · have hztrue : z.failed = true := by
      cases h : z.failed <;> simp_all
    simp only [internalEdgeGreedyKernel, hztrue, dite_true]
    exact FiniteLaw.supportedOn_pure _ hz

/-- Every state in the complete scheduled process has the required
scheduled-edge provenance, independently of success or failure. -/
theorem internalEdgeGreedyProcessLaw_supported_usesScheduledOuterEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (hSU : ∀ e, e ∈ edges → S e ⊆ U)
    (D : ℕ) (P0 : TripleSystemOn V) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (fun z ↦ NewTrianglesUseScheduledOuterEdges
        U edges.toFinset P0 z.chosen) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k,
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U omega S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (fun z ↦ NewTrianglesUseScheduledOuterEdges
            U edges.toFinset P0 z.chosen) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using haux edges.length
  intro k
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      intro T hT
      have hpos : 0 < (P0 \ P0).card :=
        card_pos.mpr ⟨T, by simpa only [z0] using hT⟩
      have hfalse : False := by
        rw [sdiff_self] at hpos
        change 0 < 0 at hpos
        omega
      exact hfalse.elim
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      exact ih.bind
        (internalEdgeGreedyKernel F G U omega S edges hne D k)
        (fun z hz ↦
          internalEdgeGreedyKernel_supported_usesScheduledOuterEdges
            F G U omega S edges hne hSU D k P0 z hz)

/-- The complete-cover induction with scheduled-edge provenance threaded
through every prefix.  This is the correct interface for blocker estimates
whose endpoint-star bound depends on the residual schedule. -/
theorem internalEdgeGreedyProcessLaw_supported_complete_ambient_scheduled
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V → Bool) (S : Sym2 V → Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges → e.out.1 ≠ e.out.2)
    (hSU : ∀ e, e ∈ edges → S e ⊆ U)
    (D : ℕ) (hD : 0 < D) (P0 A : TripleSystemOn V)
    (hAactive : ∀ e (he : e ∈ edges)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 omega →
      internalEdgeTriangle e (hne e he) w ∈ A)
    (hfloor : ∀ Q e (he : e ∈ edges), GreedyReachable F P0 Q →
      Q ⊆ P0 ∪ A → (Q \ P0).card ≤ edges.length →
      NewTrianglesUseScheduledOuterEdges U edges.toFinset P0 Q →
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 →
      D ≤ (activeReserveLegalThirdVertices F G U (S e) omega Q
        e.out.1 e.out.2 (hne e he)).card) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (fun z ↦ InternalEdgeProcessInvariant F P0 edges edges.length z ∧
        z.failed = false ∧ z.chosen ⊆ P0 ∪ A ∧
        NewTrianglesUseScheduledOuterEdges U edges.toFinset P0 z.chosen) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k ≤ edges.length →
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U omega S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (fun z ↦ InternalEdgeProcessInvariant F P0 edges k z ∧
            z.failed = false ∧ z.chosen ⊆ P0 ∪ A ∧
            NewTrianglesUseScheduledOuterEdges
              U edges.toFinset P0 z.chosen) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      refine ⟨⟨GreedyReachable.refl, by simp [z0], by simp⟩,
        rfl, by simp [z0], ?_⟩
      intro T hT
      have hpos : 0 < (P0 \ P0).card :=
        card_pos.mpr ⟨T, by simpa only [z0] using hT⟩
      have hfalse : False := by
        rw [sdiff_self] at hpos
        change 0 < 0 at hpos
        omega
      exact hfalse.elim
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U omega S edges hne D k) ?_
      intro z hz
      have hklt : k < edges.length := by omega
      have hinv := internalEdgeGreedyKernel_supported_processInvariant_step
        F G U omega S edges hne D k hklt P0 z hz.1
      have hamb := internalEdgeGreedyKernel_supported_ambient_notFailed
        F G U omega S edges hne D hD P0 A hAactive k hklt z
          hz.2.2.1 hz.2.1
          (by
            intro huncovered
            exact hfloor z.chosen (edges.get ⟨k, hklt⟩)
              (List.get_mem edges ⟨k, hklt⟩) hz.1.1 hz.2.2.1
              (hz.1.2.1.trans (Nat.le_of_lt hklt)) hz.2.2.2 huncovered)
      have huse :=
        internalEdgeGreedyKernel_supported_usesScheduledOuterEdges
          F G U omega S edges hne hSU D k P0 z hz.2.2.2
      intro z' hz'
      exact ⟨hinv z' hz', (hamb z' hz').2, (hamb z' hz').1,
        huse z' hz'⟩

end

end Erdos207
