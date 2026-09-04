/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeRandomGreedy
import ErdosProblems.Erdos207.InternalEdgeBlockerBound

/-!
# The random internal-edge cover stage

This file combines the scheduled random greedy process with the common
reserve realization.  A reserve surplus of `D` beyond all deterministic
blockers gives `D` legal choices at every exposed edge.  Consequently every
trajectory covers the internal edge list, while the terminal law retains
the factorial joint-inclusion bound B4.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- If the current edge has the required legal-candidate floor, one
transition both stays inside the ambient triangle family and keeps the
failure bit false. -/
theorem internalEdgeGreedyKernel_supported_ambient_notFailed
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (hD : 0 < D) (P0 A : TripleSystemOn V)
    (hAactive : ∀ e (he : e ∈ edges)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 omega ->
      internalEdgeTriangle e (hne e he) w ∈ A)
    (i : Nat) (hi : i < edges.length) (z : InternalEdgeGreedyStateOn V)
    (hzsub : z.chosen ⊆ P0 ∪ A) (hzfailed : z.failed = false)
    (hcurrent : ¬(coveredGraph z.chosen).Adj
        (edges.get ⟨i, hi⟩).out.1 (edges.get ⟨i, hi⟩).out.2 ->
      D <= (activeReserveLegalThirdVertices F G U
        (S (edges.get ⟨i, hi⟩)) omega z.chosen
        (edges.get ⟨i, hi⟩).out.1 (edges.get ⟨i, hi⟩).out.2
        (hne _ (List.get_mem edges ⟨i, hi⟩))).card) :
    (internalEdgeGreedyKernel F G U omega S edges hne D i z).SupportedOn
      (fun z' => z'.chosen ⊆ P0 ∪ A ∧ z'.failed = false) := by
  classical
  simp only [internalEdgeGreedyKernel, hzfailed, Bool.false_eq_true,
    hi, dite_true]
  let e := edges.get ⟨i, hi⟩
  let he : e ∈ edges := List.get_mem edges ⟨i, hi⟩
  let huv : e.out.1 ≠ e.out.2 := hne e he
  by_cases hcovered : (coveredGraph z.chosen).Adj e.out.1 e.out.2
  · simp only [e, he, huv, hcovered, dite_true]
    exact FiniteLaw.supportedOn_pure _ ⟨hzsub, hzfailed⟩
  · simp only [e, he, huv, hcovered, dite_false]
    let C := activeReserveLegalThirdVertices F G U (S e) omega
      z.chosen e.out.1 e.out.2 huv
    have hlarge : D <= C.card := by
      simpa only [C, e, he, huv] using hcurrent (by simpa only [e] using hcovered)
    rw [dif_pos (by simpa only [C, e, he, huv] using hlarge)]
    have hC : C.Nonempty := card_pos.mp (hD.trans_le hlarge)
    rw [dif_pos (by simpa only [C, e, he, huv] using hC)]
    let : Nonempty C := ⟨⟨hC.choose, hC.choose_spec⟩⟩
    have huLaw : FiniteLaw.SupportedOn (fun _ : C => True)
        (FiniteLaw.uniform : FiniteLaw C) :=
      FiniteLaw.uniform_supported _ fun _ => trivial
    refine huLaw.map
      (fun w : C =>
        ({ chosen := insert (internalEdgeTriangle e huv w.1) z.chosen
           failed := false } : InternalEdgeGreedyStateOn V)) ?_
    intro w _hw
    refine ⟨?_, rfl⟩
    intro T hT
    rcases mem_insert.mp hT with rfl | hT
    · apply mem_union_right
      apply hAactive e he w.1
      exact (mem_activeReserveLegalThirdVertices_iff.mp w.2).1
    · exact hzsub hT

/-- Abstract random cover theorem.  It is phrased using a pointwise
candidate-floor hypothesis so that deterministic obstruction estimates and
reserve concentration can be plugged in independently. -/
theorem internalEdgeGreedyProcessLaw_supported_complete_ambient
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (hD : 0 < D) (P0 A : TripleSystemOn V)
    (hAactive : ∀ e (he : e ∈ edges)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 omega ->
      internalEdgeTriangle e (hne e he) w ∈ A)
    (hfloor : ∀ Q e (he : e ∈ edges), GreedyReachable F P0 Q ->
      Q ⊆ P0 ∪ A -> (Q \ P0).card <= edges.length ->
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 ->
      D <= (activeReserveLegalThirdVertices F G U (S e) omega Q
        e.out.1 e.out.2 (hne e he)).card) :
    (internalEdgeGreedyProcessLaw F G U omega S edges hne D P0).SupportedOn
      (fun z => InternalEdgeProcessInvariant F P0 edges edges.length z ∧
        z.failed = false ∧ z.chosen ⊆ P0 ∪ A) := by
  let z0 : InternalEdgeGreedyStateOn V :=
    { chosen := P0, failed := false }
  suffices haux : ∀ k, k <= edges.length ->
      (FiniteLaw.evolveKernels
        (internalEdgeGreedyKernel F G U omega S edges hne D) k
        (FiniteLaw.pure z0)).SupportedOn
          (fun z => InternalEdgeProcessInvariant F P0 edges k z ∧
            z.failed = false ∧ z.chosen ⊆ P0 ∪ A) by
    simpa only [internalEdgeGreedyProcessLaw, z0] using
      haux edges.length le_rfl
  intro k hk
  induction k with
  | zero =>
      apply FiniteLaw.supportedOn_pure
      exact ⟨⟨GreedyReachable.refl, by simp [z0], by simp⟩,
        rfl, by simp [z0]⟩
  | succ k ih =>
      rw [FiniteLaw.evolveKernels_succ]
      refine (ih (by omega)).bind
        (internalEdgeGreedyKernel F G U omega S edges hne D k) ?_
      intro z hz
      have hklt : k < edges.length := by omega
      have hinv := internalEdgeGreedyKernel_supported_processInvariant_step
        F G U omega S edges hne D k hklt P0 z hz.1
      have hamb := internalEdgeGreedyKernel_supported_ambient_notFailed
        F G U omega S edges hne D hD P0 A hAactive k hklt z hz.2.2 hz.2.1
          (by
            intro huncovered
            exact hfloor z.chosen (edges.get ⟨k, hklt⟩)
              (List.get_mem edges ⟨k, hklt⟩) hz.1.1 hz.2.2
                (hz.1.2.1.trans (Nat.le_of_lt hklt)) huncovered)
      intro z' hz'
      exact ⟨hinv z' hz', (hamb z' hz').2, (hamb z' hz').1⟩

/-- Choose one terminal outcome from the preceding everywhere-successful
finite law. -/
theorem exists_internalEdgeGreedy_complete_ambient_of_candidateFloor
    {V : Type*} [Fintype V] [DecidableEq V]
    (F : ForbiddenFamilyOn V) (G : SimpleGraph V) (U : Finset V)
    (omega : Sym2 V -> Bool) (S : Sym2 V -> Finset V)
    (edges : List (Sym2 V))
    (hne : ∀ e, e ∈ edges -> e.out.1 ≠ e.out.2)
    (D : Nat) (hD : 0 < D) (P0 A : TripleSystemOn V)
    (hAactive : ∀ e (he : e ∈ edges)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G U (S e)
        e.out.1 e.out.2 omega ->
      internalEdgeTriangle e (hne e he) w ∈ A)
    (hfloor : ∀ Q e (he : e ∈ edges), GreedyReachable F P0 Q ->
      Q ⊆ P0 ∪ A -> (Q \ P0).card <= edges.length ->
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 ->
      D <= (activeReserveLegalThirdVertices F G U (S e) omega Q
        e.out.1 e.out.2 (hne e he)).card) :
    ∃ Q : TripleSystemOn V,
      GreedyReachable F P0 Q ∧ Q ⊆ P0 ∪ A ∧
        (Q \ P0).card <= edges.length ∧
        ∀ e ∈ edges, (coveredGraph Q).Adj e.out.1 e.out.2 := by
  let L := internalEdgeGreedyProcessLaw F G U omega S edges hne D P0
  have hsupp := internalEdgeGreedyProcessLaw_supported_complete_ambient
    F G U omega S edges hne D hD P0 A hAactive hfloor
  have hpos : 0 < ∑ z, L.mass z := by
    rw [L.sum_mass]
    exact zero_lt_one
  obtain ⟨z, _hzuniv, hzmass⟩ := Finset.sum_pos_iff.mp hpos
  have hz := hsupp z hzmass
  refine ⟨z.chosen, hz.1.1, hz.2.2, hz.1.2.1, ?_⟩
  intro e he
  obtain ⟨j, hj⟩ := List.get_of_mem he
  have hjlt : j < edges.length := j.isLt
  have hget : edges.get ⟨j, hjlt⟩ = e := by
    simpa using hj
  simpa only [hget] using hz.1.2.2 hz.2.1 j hjlt hjlt

/-- A terminal process invariant with a false failure bit covers every
member of the scheduled list. -/
lemma InternalEdgeProcessInvariant.covers_mem
    {V : Type*} [Fintype V] [DecidableEq V]
    {F : ForbiddenFamilyOn V} {P0 : TripleSystemOn V}
    {edges : List (Sym2 V)} {z : InternalEdgeGreedyStateOn V}
    (hz : InternalEdgeProcessInvariant F P0 edges edges.length z)
    (hfalse : z.failed = false) :
    ∀ e ∈ edges, (coveredGraph z.chosen).Adj e.out.1 e.out.2 := by
  intro e he
  obtain ⟨j, hj⟩ := List.get_of_mem he
  have hjlt : j < edges.length := j.isLt
  have hget : edges.get ⟨j, hjlt⟩ = e := by
    simpa using hj
  simpa only [hget] using hz.2.2 hfalse j hjlt hjlt

/-- Reserve concentration and a uniform obstruction bound produce a common
reserve realization whose scheduled terminal law is everywhere successful
and satisfies KSSS condition B4. -/
theorem IsIterationTypical.exists_internalOuterEdge_randomGreedyLaw
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : Nat} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P0 : TripleSystemOn V}
    {p eta xi : NNReal} {h : Nat}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val <= i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (hh : 2 <= h) (r : NNReal) (hr : r <= 1)
    (m a D : Nat) (hD : 0 < D)
    (hm : (m : NNReal) <=
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : Nat) : Real) <=
      ((r ^ 2 : NNReal) : Real) * m / 4)
    (hsmall : ((internalOuterEdges G (W.U i.succ)).card : Real) *
      Real.exp (-(((r ^ 2 : NNReal) : Real) * m) / 4) < 1)
    (hblocked : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P0 Q,
      Q ⊆ P0 ∪ A ->
      (Q \ P0).card <= (internalOuterEdges G (W.U i.succ)).card ->
      ∀ he : e ∈ internalOuterEdges G (W.U i.succ),
      ∀ hleave : (leaveGraph Q).Adj e.out.1 e.out.2,
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he))).card <= a) :
    ∃ omega : Sym2 V -> Bool,
      let E := internalOuterEdges G (W.U i.succ)
      let S : Sym2 V -> Finset V := fun e =>
        iterationExtensionVertices A
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
      let hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := fun e he =>
        out_fst_ne_snd_of_mem_graphEdges
          (internalOuterEdges_subset_graphEdges G (W.U i.succ)
            (by simpa only [Finset.mem_toList] using he))
      let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) omega S
        E.toList hne D P0
      L.SupportedOn (fun z =>
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card <= E.card ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V, Disjoint Q P0 ->
        L.probability (fun z => Q ⊆ z.chosen) <=
          (Q.card.factorial : NNReal) * ((D : NNReal)⁻¹ ^ Q.card) := by
  let E := internalOuterEdges G (W.U i.succ)
  let S : Sym2 V -> Finset V := fun e =>
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  obtain ⟨omega, homega⟩ :=
    htyp.exists_reserve_realization_for_internalOuterEdges htri i hstage
      hGsupp hh r hr m (a + D) hm ha hsmall
  have hne : ∀ e, e ∈ E.toList -> e.out.1 ≠ e.out.2 := by
    intro e he
    apply out_fst_ne_snd_of_mem_graphEdges
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ)
      (by simpa only [E, Finset.mem_toList] using he)
  have hu : ∀ e, e ∈ E.toList -> e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.1
  have hv : ∀ e, e ∈ E.toList -> e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.2
  have hSU : ∀ e, e ∈ E.toList -> S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hAactive : ∀ e (he : e ∈ E.toList)
      (w : ThirdVertex e.out.1 e.out.2),
      w.1 ∈ activeReserveWedgeVertices G (W.U i.succ) (S e)
        e.out.1 e.out.2 omega ->
      internalEdgeTriangle e (hne e he) w ∈ A := by
    intro e he w hw
    have hwS := (mem_activeReserveWedgeVertices_iff.mp hw).1
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hwS
  have hfloor : ∀ Q e (he : e ∈ E.toList), GreedyReachable F P0 Q ->
      Q ⊆ P0 ∪ A -> (Q \ P0).card <= E.toList.length ->
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 ->
      D <= (activeReserveLegalThirdVertices F G (W.U i.succ) (S e)
        omega Q e.out.1 e.out.2 (hne e he)).card := by
    intro Q e he hreach hsub hcard huncovered
    have heE : e ∈ internalOuterEdges G (W.U i.succ) := by
      simpa only [E, Finset.mem_toList] using he
    have hleave : (leaveGraph Q).Adj e.out.1 e.out.2 := by
      apply leaveGraph_adj.mpr
      refine ⟨hne e he, ?_⟩
      rintro ⟨T, hTQ, hleft, hright, hneT⟩
      exact huncovered (coveredGraph_adj.mpr
        ⟨T, hTQ, hleft, hright, hneT⟩)
    have hcardE : (Q \ P0).card <=
        (internalOuterEdges G (W.U i.succ)).card := by
      simpa only [E, Finset.length_toList] using hcard
    have hblock := hblocked Q e hreach hsub hcardE heE hleave
    have hsupply := homega e heE
    dsimp only [S] at hsupply
    have hcount :
        (edgeBlockedThirdVertices A Q hleave.ne ∪
          forbiddenBlockedThirdVertices F A Q hleave.ne).card + D <=
        (activeReserveWedgeVertices G (W.U i.succ) (S e)
          e.out.1 e.out.2 omega).card := by
      have hproof : hleave.ne =
          out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) heE) :=
        Subsingleton.elim _ _
      rw [hproof]
      dsimp only [S] at ⊢
      omega
    have hA : ∀ w, ∀ hwS : w ∈ S e,
        let w' : ThirdVertex e.out.1 e.out.2 :=
          ⟨w, fun h => hu e he (h ▸ hSU e he hwS),
            fun h => hv e he (h ▸ hSU e he hwS)⟩
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
  have hcomplete := internalEdgeGreedyProcessLaw_supported_complete_ambient
    F G (W.U i.succ) omega S E.toList hne D hD P0 A hAactive hfloor
  have hsupp : L.SupportedOn (fun z =>
      GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
        (z.chosen \ P0).card <= E.card ∧
        ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) := by
    intro z hz
    have hz' := hcomplete z hz
    refine ⟨hz'.1.1, hz'.2.2, ?_, ?_⟩
    · simpa only [Finset.length_toList] using hz'.1.2.1
    · intro e he
      exact hz'.1.covers_mem hz'.2.1 e
        (by simpa only [Finset.mem_toList] using he)
  refine ⟨omega, ?_⟩
  dsimp only
  refine ⟨hsupp, ?_⟩
  intro Q hdisjoint
  exact internalEdgeGreedyProcess_probability_subset_chosen_le
    F G (W.U i.succ) omega S E.toList hne E.nodup_toList hu hv hSU
      D hD P0 Q hdisjoint

end

end Erdos207
