/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InhomogeneousWeightedJointInclusion
import ErdosProblems.Erdos207.InternalEdgeGreedyCover
import ErdosProblems.Erdos207.GreedyObstructionCount

/-!
# The scheduled random greedy process for internal edges

This is the finite probability kernel used in KSSS Section 10.2.  A fixed
list of internal edges is exposed once, in order.  An already covered edge
is skipped.  At an uncovered edge the process chooses uniformly among its
legal reserve-supported third vertices while their number is at least the
threshold `D`; if the threshold fails, a permanent failure bit is set.

The important probabilistic feature is scheduling: a reserve triangle with
two endpoints outside `U` and its third vertex in `U` can be proposed at
only one edge of a duplicate-free list.  Consequently its cumulative point
hazard is at most `D⁻¹`, with no factor equal to the length of the edge list.
-/

namespace Erdos207

open Finset
open scoped BigOperators NNReal

noncomputable section

/-- Legal reserve-supported third vertices for one displayed edge. -/
noncomputable def activeReserveLegalThirdVertices
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U S : Finset V)
    (omega : Sym2 V -> Bool) (Q : TripleSystemOn V)
    (u v : V) (huv : u ≠ v) : Finset (ThirdVertex u v) := by
  classical
  exact univ.filter fun w =>
    w.1 ∈ activeReserveWedgeVertices G U S u v omega ∧
      IsLegalExtension F Q (thirdVertexTriple huv w)

@[simp]
lemma mem_activeReserveLegalThirdVertices_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {G : SimpleGraph V} {U S : Finset V}
    {omega : Sym2 V -> Bool} {Q : TripleSystemOn V}
    {u v : V} {huv : u ≠ v} {w : ThirdVertex u v} :
    w ∈ activeReserveLegalThirdVertices F G U S omega Q u v huv <->
      w.1 ∈ activeReserveWedgeVertices G U S u v omega ∧
        IsLegalExtension F Q (thirdVertexTriple huv w) := by
  classical
  simp [activeReserveLegalThirdVertices]

/-- Quantitative reserve-wedge legality.  Every active reserve vertex is
either a legal extension or belongs to one of the two obstruction sets.
Thus a surplus of `D` vertices beyond all blockers leaves at least `D`
legal choices. -/
theorem card_activeReserveLegalThirdVertices_ge_of_blocked_add_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {A P : TripleSystemOn V}
    {G : SimpleGraph V} {U S : Finset V} {u v : V}
    (hpacking : IsPackingOn P) (havoid : AvoidsForbidden P F)
    (huvLeave : (leaveGraph P).Adj u v)
    (hu : u ∉ U) (hv : v ∉ U) (hSU : S ⊆ U)
    (omega : Sym2 V -> Bool)
    (hA : ∀ w, ∀ hwS : w ∈ S,
      let w' : ThirdVertex u v :=
        ⟨w, fun h => hu (h ▸ hSU hwS),
          fun h => hv (h ▸ hSU hwS)⟩
      thirdVertexTriple huvLeave.ne w' ∈ A)
    (D : Nat)
    (hcount :
      (edgeBlockedThirdVertices A P huvLeave.ne ∪
        forbiddenBlockedThirdVertices F A P huvLeave.ne).card + D <=
      (activeReserveWedgeVertices G U S u v omega).card) :
    D <= (activeReserveLegalThirdVertices F G U S omega P
      u v huvLeave.ne).card := by
  classical
  let C := activeReserveWedgeVertices G U S u v omega
  let e : {w // w ∈ C} ↪ ThirdVertex u v :=
    { toFun := fun w => ⟨w.1,
        fun h => hu (h ▸ hSU
          (mem_activeReserveWedgeVertices_iff.mp w.2).1),
        fun h => hv (h ▸ hSU
          (mem_activeReserveWedgeVertices_iff.mp w.2).1)⟩
      inj' := by
        intro x y hxy
        apply Subtype.ext
        exact congrArg (fun z : ThirdVertex u v => z.1) hxy }
  let C' : Finset (ThirdVertex u v) := C.attach.map e
  have hcardC' : C'.card = C.card := by
    simp [C']
  have hsub : C' ⊆
      activeReserveLegalThirdVertices F G U S omega P
          u v huvLeave.ne ∪
        (edgeBlockedThirdVertices A P huvLeave.ne ∪
          forbiddenBlockedThirdVertices F A P huvLeave.ne) := by
    intro w hw
    obtain ⟨x, hx, rfl⟩ := mem_map.mp hw
    have hxactive : x.1 ∈ C := x.2
    have hxS := (mem_activeReserveWedgeVertices_iff.mp x.2).1
    let z : ThirdVertex u v :=
      ⟨x.1, fun h => hu (h ▸ hSU hxS),
        fun h => hv (h ▸ hSU hxS)⟩
    have heq : e x = z := by
      apply Subtype.ext
      rfl
    rw [heq]
    have hzactive : z.1 ∈ activeReserveWedgeVertices G U S u v omega :=
      hxactive
    have hTA : thirdVertexTriple huvLeave.ne z ∈ A := hA x.1 hxS
    by_cases hlegal : IsLegalExtension F P
        (thirdVertexTriple huvLeave.ne z)
    · exact mem_union_left _
        (mem_activeReserveLegalThirdVertices_iff.mpr ⟨hzactive, hlegal⟩)
    · apply mem_union_right
      have hTnotP : thirdVertexTriple huvLeave.ne z ∉ P := by
        intro hTP
        exact huvLeave.2 ⟨thirdVertexTriple huvLeave.ne z, hTP,
          left_mem_thirdVertexTriple _ _, right_mem_thirdVertexTriple _ _,
          huvLeave.ne⟩
      have hobs :
          ¬TriangleAvoidsGraph (coveredGraph P)
              (thirdVertexTriple huvLeave.ne z) ∨
            CompletesForbidden F P (thirdVertexTriple huvLeave.ne z) := by
        have hiff := isLegalExtension_iff hpacking havoid
          (thirdVertexTriple huvLeave.ne z)
        tauto
      rcases hobs with hedge | hforbidden
      · exact mem_union_left _
          (mem_edgeBlockedThirdVertices_iff.mpr ⟨hTA, hedge⟩)
      · exact mem_union_right _
          (mem_forbiddenBlockedThirdVertices_iff.mpr ⟨hTA, hforbidden⟩)
  have hcover : C.card <=
      (activeReserveLegalThirdVertices F G U S omega P
          u v huvLeave.ne).card +
        (edgeBlockedThirdVertices A P huvLeave.ne ∪
          forbiddenBlockedThirdVertices F A P huvLeave.ne).card := by
    calc
      C.card = C'.card := hcardC'.symm
      _ <= (activeReserveLegalThirdVertices F G U S omega P
              u v huvLeave.ne ∪
            (edgeBlockedThirdVertices A P huvLeave.ne ∪
              forbiddenBlockedThirdVertices F A P huvLeave.ne)).card :=
        card_le_card hsub
      _ <= (activeReserveLegalThirdVertices F G U S omega P
              u v huvLeave.ne).card +
            (edgeBlockedThirdVertices A P huvLeave.ne ∪
              forbiddenBlockedThirdVertices F A P huvLeave.ne).card :=
        card_union_le _ _
  change _ <= C.card at hcount
  omega

/-- State of the edge-list process.  Once `failed` becomes true, every
later transition is deterministic. -/
structure InternalEdgeGreedyStateOn (V : Type*) [DecidableEq V] where
  chosen : TripleSystemOn V
  failed : Bool

instance {V : Type*} [DecidableEq V] :
    DecidableEq (InternalEdgeGreedyStateOn V) :=
  fun z z' ↦ decidable_of_iff
    (z.chosen = z'.chosen ∧ z.failed = z'.failed) ⟨by
      rintro ⟨hchosen, hfailed⟩
      cases z
      cases z'
      simp_all, by
      intro h
      subst z'
      exact ⟨rfl, rfl⟩⟩

instance {V : Type*} [Fintype V] [DecidableEq V] :
    Finite (InternalEdgeGreedyStateOn V) :=
  Finite.of_injective
    (fun z : InternalEdgeGreedyStateOn V ↦ (z.chosen, z.failed)) (by
      intro z z' h
      cases z
      cases z'
      simp_all)

instance {V : Type*} [Fintype V] [DecidableEq V] :
    Fintype (InternalEdgeGreedyStateOn V) := Fintype.ofFinite _

/-- The triangle inserted from a reserve third vertex at edge `e`. -/
def internalEdgeTriangle
    {V : Type*} [DecidableEq V] (e : Sym2 V)
    (hne : e.out.1 ≠ e.out.2) (w : ThirdVertex e.out.1 e.out.2) :
    TripleOn V :=
  thirdVertexTriple hne w

/-- One scheduled edge-list transition.  The proof arguments describe the
fixed geometric placement of every scheduled edge and its candidate set. -/
noncomputable def internalEdgeGreedyKernel
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (i : Nat) (z : InternalEdgeGreedyStateOn V) :
    FiniteLaw (InternalEdgeGreedyStateOn V) := by
  classical
  by_cases hfailed : z.failed = true
  · exact FiniteLaw.pure z
  by_cases hi : i < edges.length
  · let e := edges.get ⟨i, hi⟩
    let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
    let huv : e.out.1 ≠ e.out.2 := hne e he
    by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
    · exact FiniteLaw.pure z
    · let C := activeReserveLegalThirdVertices F G U (S e) omega
        z.chosen e.out.1 e.out.2 huv
      by_cases hlarge : D <= C.card
      · by_cases hC : C.Nonempty
        · letI : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
          exact FiniteLaw.map
            (fun w : C =>
              { chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
                failed := false })
            (FiniteLaw.uniform : FiniteLaw C)
        · exact FiniteLaw.pure
            { chosen := z.chosen, failed := true }
      · exact FiniteLaw.pure
          { chosen := z.chosen, failed := true }
  · exact FiniteLaw.pure z

/-- Terminal law after exposing every edge in the list once. -/
noncomputable def internalEdgeGreedyProcessLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (P0 : TripleSystemOn V) :
    FiniteLaw (InternalEdgeGreedyStateOn V) :=
  FiniteLaw.evolveKernels
    (internalEdgeGreedyKernel F G U omega S edges hne D)
    edges.length (FiniteLaw.pure { chosen := P0, failed := false })

/-- Support invariant after the first `k` scheduled edges: the chosen family
is legally reachable, contains at most `k` triangles beyond the initial
family, and a nonfailed state covers every exposed edge. -/
def InternalEdgeProcessInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (P0 : TripleSystemOn V)
    (edges : List (Sym2 V)) (k : Nat)
    (z : InternalEdgeGreedyStateOn V) : Prop :=
  GreedyReachable F P0 z.chosen ∧
    (z.chosen \ P0).card <= k ∧
      (z.failed = false ->
        ∀ j, ∀ hj : j < edges.length, j < k ->
          (coveredGraph z.chosen).Adj
            (edges.get ⟨j, hj⟩).out.1 (edges.get ⟨j, hj⟩).out.2)

/-- One supported scheduled transition advances the reachability-and-cover
invariant by one edge. -/
theorem internalEdgeGreedyKernel_supported_processInvariant_step
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D i : Nat) (hi : i < edges.length) (P0 : TripleSystemOn V)
    (z : InternalEdgeGreedyStateOn V)
    (hz : InternalEdgeProcessInvariant F P0 edges i z) :
    (internalEdgeGreedyKernel F G U omega S edges hne D i z).SupportedOn
      (InternalEdgeProcessInvariant F P0 edges (i + 1)) := by
  classical
  by_cases hfailed : z.failed = true
  · simp only [internalEdgeGreedyKernel, hfailed]
    apply FiniteLaw.supportedOn_pure
    refine ⟨hz.1, hz.2.1.trans (Nat.le_succ i), ?_⟩
    simp [hfailed]
  · have hzfalse : z.failed = false := Bool.eq_false_of_not_eq_true hfailed
    simp only [internalEdgeGreedyKernel, hzfalse, Bool.false_eq_true,
      hi, dite_true]
    let e := edges.get ⟨i, hi⟩
    let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
    let huv : e.out.1 ≠ e.out.2 := hne e he
    have hprevious : ∀ j, ∀ hj : j < edges.length, j < i ->
        (coveredGraph z.chosen).Adj
          (edges.get ⟨j, hj⟩).out.1 (edges.get ⟨j, hj⟩).out.2 :=
      hz.2.2 hzfalse
    by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
    · simp only [e, he, huv, hcovered, dite_true]
      apply FiniteLaw.supportedOn_pure
      refine ⟨hz.1, hz.2.1.trans (Nat.le_succ i), ?_⟩
      intro _hfalse
      intro j hj hji
      by_cases hjlt : j < i
      · exact hprevious j hj hjlt
      · have hji_eq : j = i := by omega
        subst j
        simpa only [e] using hcovered
    · simp only [e, he, huv, hcovered, dite_false]
      let C := activeReserveLegalThirdVertices F G U (S e) omega
        z.chosen e.out.1 e.out.2 huv
      by_cases hlarge : D <= C.card
      · rw [dif_pos (by simpa only [C, e, huv, he] using hlarge)]
        by_cases hC : C.Nonempty
        · rw [dif_pos (by simpa only [C, e, huv, he] using hC)]
          let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
          have huLaw : FiniteLaw.SupportedOn (fun _ : C => True)
              (FiniteLaw.uniform : FiniteLaw C) :=
            FiniteLaw.uniform_supported _ fun _ => trivial
          refine huLaw.map
            (fun w : C =>
              ({ chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
                 failed := false } : InternalEdgeGreedyStateOn V)) ?_
          intro w _hw
          have hwlegal : IsLegalExtension F z.chosen
              (internalEdgeTriangle e huv w.1) :=
            (mem_activeReserveLegalThirdVertices_iff.mp w.2).2
          have hreach : GreedyReachable F P0
              (insert (internalEdgeTriangle e huv w.1) z.chosen) :=
            GreedyReachable.step hz.1 hwlegal
          have hcard :
              (insert (internalEdgeTriangle e huv w.1) z.chosen \ P0).card <=
                i + 1 := by
            rw [card_sdiff_of_subset hreach.initial_subset]
            have hzcard : z.chosen.card - P0.card <= i := by
              rw [← card_sdiff_of_subset hz.1.initial_subset]
              exact hz.2.1
            have hinsert := card_insert_le
              (internalEdgeTriangle e huv w.1) z.chosen
            omega
          refine ⟨hreach, hcard, ?_⟩
          intro _hfalse
          intro j hj hji
          by_cases hjlt : j < i
          · exact coveredGraph_mono (subset_insert _ _)
              (hprevious j hj hjlt)
          · have hji_eq : j = i := by omega
            subst j
            exact coveredGraph_adj.mpr
              ⟨internalEdgeTriangle e huv w.1,
                mem_insert_self _ _, left_mem_thirdVertexTriple huv w.1,
                right_mem_thirdVertexTriple huv w.1, huv⟩
        · rw [dif_neg (by simpa only [C, e, huv, he] using hC)]
          apply FiniteLaw.supportedOn_pure
          refine ⟨hz.1, by simpa using hz.2.1.trans (Nat.le_succ i), ?_⟩
          simp
      · rw [dif_neg (by simpa only [C, e, huv, he] using hlarge)]
        apply FiniteLaw.supportedOn_pure
        refine ⟨hz.1, by simpa using hz.2.1.trans (Nat.le_succ i), ?_⟩
        simp

/-- The entire edge-list law is supported on legal greedy extensions, and
every nonfailed terminal state covers the whole list. -/
theorem internalEdgeGreedyProcessLaw_supported_processInvariant
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (P0 : TripleSystemOn V) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (InternalEdgeProcessInvariant F P0 edges edges.length) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k <= edges.length ->
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U omega S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (InternalEdgeProcessInvariant F P0 edges k) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      exact ⟨GreedyReachable.refl, by simp [z0], by simp⟩
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U omega S edges hne D k) ?_
      intro z hz
      exact internalEdgeGreedyKernel_supported_processInvariant_step
        F G U omega S edges hne D k (by omega) P0 z hz

/-- A uniform lower bound on the candidate set at every reachable,
budget-respecting state prevents one scheduled transition from setting the
failure bit. -/
theorem internalEdgeGreedyKernel_supported_notFailed_of_candidateFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (hfloor : ∀ Q e (he : e ∈ edges), GreedyReachable F P0 Q ->
      (Q \ P0).card <= edges.length ->
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 ->
      D <= (activeReserveLegalThirdVertices F G U (S e) omega Q
        e.out.1 e.out.2 (hne e he)).card)
    (i : Nat) (hi : i < edges.length) (z : InternalEdgeGreedyStateOn V)
    (hzreach : GreedyReachable F P0 z.chosen)
    (hzcard : (z.chosen \ P0).card <= i)
    (hzfailed : z.failed = false) :
    (internalEdgeGreedyKernel F G U omega S edges hne D i z).SupportedOn
      (fun z' => z'.failed = false) := by
  classical
  simp only [internalEdgeGreedyKernel, hzfailed, Bool.false_eq_true,
    hi, dite_true]
  let e := edges.get ⟨i, hi⟩
  let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
  let huv : e.out.1 ≠ e.out.2 := hne e he
  by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
  · simp only [e, he, huv, hcovered, dite_true]
    exact FiniteLaw.supportedOn_pure _ hzfailed
  · simp only [e, he, huv, hcovered, dite_false]
    let C := activeReserveLegalThirdVertices F G U (S e) omega
      z.chosen e.out.1 e.out.2 huv
    have hlarge : D <= C.card := by
      apply hfloor z.chosen e he hzreach
      · exact hzcard.trans (Nat.le_of_lt hi)
      · exact hcovered
    rw [dif_pos (by simpa only [C, e, huv, he] using hlarge)]
    have hC : C.Nonempty := card_pos.mp (hD.trans_le hlarge)
    rw [dif_pos (by simpa only [C, e, huv, he] using hC)]
    let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
    have huLaw : FiniteLaw.SupportedOn (fun _ : C => True)
        (FiniteLaw.uniform : FiniteLaw C) :=
      FiniteLaw.uniform_supported _ fun _ => trivial
    exact huLaw.map
      (fun w : C =>
        ({ chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
           failed := false } : InternalEdgeGreedyStateOn V))
      (by simp)

/-- Under the candidate-floor hypothesis, every state in the terminal law
is a legal extension, uses at most one new triangle per scheduled edge, and
covers every scheduled edge; failure has probability zero because it is
absent from the support. -/
theorem internalEdgeGreedyProcessLaw_supported_complete_of_candidateFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (hD : 0 < D) (P0 : TripleSystemOn V)
    (hfloor : ∀ Q e (he : e ∈ edges), GreedyReachable F P0 Q ->
      (Q \ P0).card <= edges.length ->
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 ->
      D <= (activeReserveLegalThirdVertices F G U (S e) omega Q
        e.out.1 e.out.2 (hne e he)).card) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (fun z => InternalEdgeProcessInvariant F P0 edges edges.length z ∧
        z.failed = false) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k <= edges.length ->
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U omega S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (fun z => InternalEdgeProcessInvariant F P0 edges k z ∧
            z.failed = false) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      exact ⟨⟨GreedyReachable.refl, by simp [z0], by simp⟩, rfl⟩
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U omega S edges hne D k) ?_
      intro z hz
      have hinv := internalEdgeGreedyKernel_supported_processInvariant_step
        F G U omega S edges hne D k (by omega) P0 z hz.1
      have hfalse :=
        internalEdgeGreedyKernel_supported_notFailed_of_candidateFloor
          F G U omega S edges hne D hD P0 hfloor k (by omega) z
            hz.1.1 hz.1.2.1 hz.2
      intro z' hz'
      exact ⟨hinv z' hz', hfalse z' hz'⟩

/-- Every scheduled transition either freezes the chosen family or inserts
one triangle. -/
theorem internalEdgeGreedyKernel_monotone_singleInsertion
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D i : Nat) :
    IsMonotoneSingleInsertionKernel
      (internalEdgeGreedyKernel F G U omega S edges hne D i)
      (fun z : InternalEdgeGreedyStateOn V => z.chosen) := by
  classical
  intro z
  by_cases hfailed : z.failed = true
  · simp only [internalEdgeGreedyKernel, hfailed]
    exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩
  · have hzfalse : z.failed = false := Bool.eq_false_of_not_eq_true hfailed
    simp only [internalEdgeGreedyKernel, hzfalse, Bool.false_eq_true, if_false]
    by_cases hi : i < edges.length
    · simp only [hi, dite_true]
      let e := edges.get ⟨i, hi⟩
      let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
      let huv : e.out.1 ≠ e.out.2 := hne e he
      by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
      · simp only [e, he, huv, hcovered, dite_true]
        exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩
      · simp only [e, he, huv, hcovered, dite_false]
        let C := activeReserveLegalThirdVertices F G U (S e) omega
          z.chosen e.out.1 e.out.2 huv
        by_cases hlarge : D <= C.card
        · rw [dif_pos (by simpa only [C, e, huv, he] using hlarge)]
          by_cases hC : C.Nonempty
          ·
            rw [dif_pos (by simpa only [C, e, huv, he] using hC)]
            let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
            have hu : FiniteLaw.SupportedOn (fun _ : C => True)
                (FiniteLaw.uniform : FiniteLaw C) :=
              FiniteLaw.uniform_supported _ fun _ => trivial
            refine hu.map
              (fun w : C =>
                ({ chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
                   failed := false } : InternalEdgeGreedyStateOn V)) ?_
            intro w _hw
            constructor
            · exact subset_insert _ _
            · by_cases hmem : internalEdgeTriangle e huv w.1 ∈ z.chosen
              · simp [hmem]
              · simp [hmem]
          · rw [dif_neg (by simpa only [C, e, huv, he] using hC)]
            exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩
        · rw [dif_neg (by simpa only [C, e, huv, he] using hlarge)]
          exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩
    · simp only [hi, dite_false]
      exact FiniteLaw.supportedOn_pure _ ⟨Subset.rfl, by simp⟩

/-- A triangle is scheduled at time `i` when it is the triangle through the
`i`th edge and a third vertex in the inner set `U`. -/
def InternalEdgeTriangleScheduledAt
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (i : Nat) (T : TripleOn V) : Prop :=
  ∃ hi : i < edges.length,
    ∃ w : ThirdVertex
        (edges.get ⟨i, hi⟩).out.1 (edges.get ⟨i, hi⟩).out.2,
      w.1 ∈ U ∧
        T = internalEdgeTriangle (edges.get ⟨i, hi⟩)
          (hne _ (List.get_mem edges ⟨i, hi⟩)) w

/-- A triangle with its third vertex in `U` cannot be scheduled at two
different duplicate-free outer edges. -/
lemma internalEdgeTriangleScheduledAt_index_unique
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {edges : List (Sym2 V)}
    {hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2}
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    {i j : Nat} {T : TripleOn V}
    (hiT : InternalEdgeTriangleScheduledAt U edges hne i T)
    (hjT : InternalEdgeTriangleScheduledAt U edges hne j T) :
    i = j := by
  classical
  rcases hiT with ⟨hi, w, hwU, hTw⟩
  rcases hjT with ⟨hj, z, hzU, hTz⟩
  let ei := edges.get ⟨i, hi⟩
  let ej := edges.get ⟨j, hj⟩
  have hei : ei ∈ edges := List.get_mem edges ⟨i, hi⟩
  have hej : ej ∈ edges := List.get_mem edges ⟨j, hj⟩
  have hei_ne : ei.out.1 ≠ ei.out.2 := hne ei hei
  have hej_ne : ej.out.1 ≠ ej.out.2 := hne ej hej
  have endpoint_mem_ej (x : V)
      (hxout : x ∉ U)
      (hxT : x ∈ (internalEdgeTriangle ei hei_ne w).1) :
      x ∈ ej := by
    have hxT' : x ∈ (internalEdgeTriangle ej hej_ne z).1 := by
      rw [← hTz, hTw]
      exact hxT
    have hx : x = ej.out.1 ∨ x = ej.out.2 ∨ x = z.1 := by
      simpa [internalEdgeTriangle, thirdVertexTriple, tripleOfThree,
        ej, hej_ne] using hxT'
    have hxpair : x = ej.out.1 ∨ x = ej.out.2 := by
      rcases hx with hx | hx | hx
      · exact Or.inl hx
      · exact Or.inr hx
      · exact (hxout (hx ▸ hzU)).elim
    rw [← ej.out_eq, Sym2.mem_iff]
    exact hxpair
  have hfst : ei.out.1 ∈ ej :=
    endpoint_mem_ej ei.out.1 (hu ei hei)
      (left_mem_thirdVertexTriple hei_ne w)
  have hsnd : ei.out.2 ∈ ej :=
    endpoint_mem_ej ei.out.2 (hv ei hei)
      (right_mem_thirdVertexTriple hei_ne w)
  have heq : ei = ej :=
    Sym2.eq_of_ne_mem hei_ne (Sym2.out_fst_mem ei)
      (Sym2.out_snd_mem ei) hfst hsnd
  have hfin : (⟨i, hi⟩ : Fin edges.length) = ⟨j, hj⟩ :=
    hnodup.injective_get heq
  exact congrArg Fin.val hfin

/-- Point hazard attached to the unique scheduled edge of a triangle. -/
noncomputable def internalEdgePointHazard
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (i : Nat) (T : TripleOn V) : NNReal := by
  classical
  exact if InternalEdgeTriangleScheduledAt U edges hne i T
    then (D : NNReal)⁻¹ else 0

/-- Times at which one fixed triangle could be proposed. -/
noncomputable def internalEdgeScheduledTimes
    {V : Type*} [Fintype V] [DecidableEq V]
    (U : Finset V) (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (T : TripleOn V) : Finset Nat := by
  classical
  exact (range edges.length).filter fun i =>
    InternalEdgeTriangleScheduledAt U edges hne i T

lemma card_internalEdgeScheduledTimes_le_one
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {edges : List (Sym2 V)}
    {hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2}
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (T : TripleOn V) :
    (internalEdgeScheduledTimes U edges hne T).card <= 1 := by
  classical
  rw [card_le_one]
  intro i hi j hj
  have hiT : InternalEdgeTriangleScheduledAt U edges hne i T :=
    (mem_filter.mp hi).2
  have hjT : InternalEdgeTriangleScheduledAt U edges hne j T :=
    (mem_filter.mp hj).2
  exact internalEdgeTriangleScheduledAt_index_unique hnodup hu hv hiT hjT

/-- The cumulative hazard of one triangle over the whole edge list is at
most one reciprocal threshold. -/
theorem cumulative_internalEdgePointHazard_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {edges : List (Sym2 V)}
    {hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2}
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (D : Nat) (T : TripleOn V) :
    cumulativePointHazard
        (internalEdgePointHazard U edges hne D) edges.length T <=
      (D : NNReal)⁻¹ := by
  classical
  let I := internalEdgeScheduledTimes U edges hne T
  have hI : I.card <= 1 :=
    card_internalEdgeScheduledTimes_le_one hnodup hu hv T
  unfold cumulativePointHazard internalEdgePointHazard
  rw [← sum_filter]
  change (∑ _i ∈ I, (D : NNReal)⁻¹) <= (D : NNReal)⁻¹
  rw [sum_const, nsmul_eq_mul]
  calc
    (I.card : NNReal) * (D : NNReal)⁻¹ <=
        1 * (D : NNReal)⁻¹ := by
      gcongr
      exact_mod_cast hI
    _ = (D : NNReal)⁻¹ := one_mul _

/-- One scheduled transition inserts a specified new triangle with
probability at most its scheduled point hazard. -/
theorem internalEdgeGreedyKernel_probability_new_triangle_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (i : Nat)
    (z : InternalEdgeGreedyStateOn V) (T : TripleOn V)
    (hTnot : T ∉ z.chosen) :
    (internalEdgeGreedyKernel F G U omega S edges hne D i z).probability
        (fun z' => T ∈ z'.chosen) <=
      internalEdgePointHazard U edges hne D i T := by
  classical
  by_cases hfailed : z.failed = true
  · simp only [internalEdgeGreedyKernel, hfailed,
      FiniteLaw.probability_pure]
    simp [hTnot]
  · have hzfalse : z.failed = false := Bool.eq_false_of_not_eq_true hfailed
    simp only [internalEdgeGreedyKernel, hzfalse, Bool.false_eq_true]
    by_cases hi : i < edges.length
    · simp only [hi, dite_true]
      let e := edges.get ⟨i, hi⟩
      let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
      let huv : e.out.1 ≠ e.out.2 := hne e he
      by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
      · simp only [e, he, huv, hcovered, dite_true,
          FiniteLaw.probability_pure]
        simp [hTnot]
      · simp only [e, he, huv, hcovered, dite_false]
        let C := activeReserveLegalThirdVertices F G U (S e) omega
          z.chosen e.out.1 e.out.2 huv
        by_cases hlarge : D <= C.card
        · rw [dif_pos (by simpa only [C, e, huv, he] using hlarge)]
          by_cases hC : C.Nonempty
          · rw [dif_pos (by simpa only [C, e, huv, he] using hC)]
            let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
            rw [FiniteLaw.probability_map]
            by_cases hex : ∃ w : C,
                T = internalEdgeTriangle e huv w.1
            · obtain ⟨w0, hw0⟩ := hex
              have hsched :
                  InternalEdgeTriangleScheduledAt U edges hne i T := by
                refine ⟨hi, w0.1, ?_, ?_⟩
                · exact hSU e he
                    (mem_activeReserveWedgeVertices_iff.mp
                      (mem_activeReserveLegalThirdVertices_iff.mp w0.2).1).1
                · simpa only [e, he, huv] using hw0
              have hunique : ∀ w : C,
                  T ∈ insert (internalEdgeTriangle e huv w.1) z.chosen <->
                    w = w0 := by
                intro w
                constructor
                · intro hw
                  rcases mem_insert.mp hw with hw | hw
                  · apply Subtype.ext
                    exact thirdVertexTriple_injective huv
                      (hw.symm.trans hw0)
                  · exact (hTnot hw).elim
                · intro hw
                  subst w
                  exact mem_insert.mpr (Or.inl hw0)
              have hprob := @FiniteLaw.uniform_probability_unique C _
                inferInstance
                (fun w => T ∈ insert
                  (internalEdgeTriangle e huv w.1) z.chosen)
                w0 hunique
              calc
                (FiniteLaw.uniform : FiniteLaw C).probability
                    (fun w => T ∈ insert
                      (internalEdgeTriangle e huv w.1) z.chosen) =
                    (C.card : NNReal)⁻¹ := by
                      simpa only [Fintype.card_coe] using hprob
                _ <= (D : NNReal)⁻¹ := by
                  simpa only [one_div] using
                    (one_div_le_one_div_of_le
                      (by exact_mod_cast hD : (0 : NNReal) < D)
                      (by exact_mod_cast hlarge : (D : NNReal) <= C.card))
                _ = internalEdgePointHazard U edges hne D i T := by
                  simp [internalEdgePointHazard, hsched]
            · have hfalse :
                  (fun w : C => T ∈ insert
                    (internalEdgeTriangle e huv w.1) z.chosen) =
                    (fun _ => False) := by
                funext w
                apply propext
                constructor
                · intro hw
                  rcases mem_insert.mp hw with hw | hw
                  · exact hex ⟨w, hw⟩
                  · exact hTnot hw
                · exact False.elim
              rw [hfalse, FiniteLaw.probability_false]
              exact bot_le
          · rw [dif_neg (by simpa only [C, e, huv, he] using hC)]
            rw [FiniteLaw.probability_pure]
            simp [hTnot]
        · rw [dif_neg (by simpa only [C, e, huv, he] using hlarge)]
          rw [FiniteLaw.probability_pure]
          simp [hTnot]
    · simp only [hi, dite_false, FiniteLaw.probability_pure]
      simp [hTnot]

/-- KSSS condition B4 for the internal-edge process.  A fixed family of
new triangles is jointly selected with probability at most its factorial
times one reciprocal threshold per triangle; crucially, there is no factor
depending on the number of scheduled edges. -/
theorem internalEdgeGreedyProcess_probability_subset_chosen_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (hnodup : edges.Nodup)
    (hu : ∀ e, e ∈ edges -> e.out.1 ∉ U)
    (hv : ∀ e, e ∈ edges -> e.out.2 ∉ U)
    (hSU : ∀ e, e ∈ edges -> S e ⊆ U)
    (D : Nat) (hD : 0 < D) (P0 Q : TripleSystemOn V)
    (hdisjoint : Disjoint Q P0) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen) <=
      (Q.card.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  have hjoint := evolveKernels_probability_subset_le_pointWeights
    (internalEdgeGreedyKernel F G U omega S edges hne D)
    (fun z : InternalEdgeGreedyStateOn V => z.chosen)
    (internalEdgePointHazard U edges hne D)
    (internalEdgeGreedyKernel_monotone_singleInsertion
      F G U omega S edges hne D)
    (internalEdgeGreedyKernel_probability_new_triangle_le
      F G U omega S edges hne hSU D hD)
    z0 Q hdisjoint edges.length
  have hweight :
      setWeight
          (cumulativePointHazard
            (internalEdgePointHazard U edges hne D) edges.length) Q <=
        setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := by
    unfold setWeight
    apply prod_le_prod
    · intro T hTQ
      exact bot_le
    · intro T hTQ
      exact cumulative_internalEdgePointHazard_le hnodup hu hv D T
  calc
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).probability
        (fun z => Q ⊆ z.chosen) <=
      (Q.card.factorial : NNReal) *
        setWeight
          (cumulativePointHazard
            (internalEdgePointHazard U edges hne D) edges.length) Q := by
      simpa only [internalEdgeGreedyProcessLaw, z0] using hjoint
    _ <= (Q.card.factorial : NNReal) *
        setWeight (fun _ : TripleOn V => (D : NNReal)⁻¹) Q := by
      gcongr
    _ = (Q.card.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
      simp [setWeight]

end

end Erdos207
