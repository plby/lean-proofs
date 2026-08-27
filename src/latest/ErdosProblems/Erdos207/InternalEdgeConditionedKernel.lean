/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeC4Law
import ErdosProblems.Erdos207.SimultaneousReserveWedgeLaw

/-!
# The internal-edge kernel on every good reserve outcome

The earlier extraction theorem chose one reserve realization before running
the internal random greedy cover.  For the reserve-aware master law we need
the stronger pointwise statement proved here: every reserve outcome with the
simultaneous wedge-supply property supports a successful internal cover
kernel, and that kernel satisfies a uniform exponential C4 bound for its
genuinely new triangles.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The reserve-supply event for all internal outer edges at one vortex
level. -/
def InternalOuterReserveGood
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (G : SimpleGraph V) (A : TripleSystemOn V) (cutoff : ℕ)
    (bits : Sym2 V → Bool) : Prop :=
  let E := internalOuterEdges G (W.U i.succ)
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  AllReserveWedgeSupplies G (W.U i.succ) E
    (fun e ↦ e.out.1) (fun e ↦ e.out.2) S (fun _ ↦ cutoff) bits

/-- Uniform failure estimate for the internal-edge reserve event.  The
right-hand side is stated as an `NNReal` parameter so it plugs directly into
dependent joint conditioning. -/
theorem IsIterationTypical.reserveEdgeLaw_probability_not_internalOuterReserveGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta ξ : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta ξ h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (m cutoff : ℕ)
    (hm : (m : ℝ≥0) ≤
      (1 - ξ) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : (cutoff : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (epsilon : ℝ≥0)
    (hfailure : ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
      Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) ≤ epsilon) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ InternalOuterReserveGood W i G A cutoff bits) ≤
        epsilon := by
  let E := internalOuterEdges G (W.U i.succ)
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hedge : ∀ e ∈ E, e ∈ graphEdges G := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp he).1
  have hadjEdge : ∀ e ∈ E, G.Adj e.out.1 e.out.2 := by
    intro e he
    exact graph_adj_out_of_mem_graphEdges (hedge e he)
  have houter : ∀ e ∈ E,
      e.out.1 ∈ W.U i.castSucc ∧ e.out.2 ∈ W.U i.castSucc := by
    intro e he
    exact hGsupp (hadjEdge e he)
  have hinner : ∀ e ∈ E,
      e.out.1 ∉ W.U i.succ ∧ e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp he).2
  have hSU : ∀ e ∈ E, S e ⊆ W.U i.succ := by
    intro e _he
    exact iterationExtensionVertices_subset A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hadj : ∀ e ∈ E, ∀ w ∈ S e,
      G.Adj e.out.1 w ∧ G.Adj e.out.2 w := by
    intro e he w hw
    have hwInner := hSU e he hw
    apply iterationExtensionVertices_edge_adjacencies
      (out_fst_ne_snd_of_mem_graphEdges (hedge e he))
    · intro huw
      subst w
      exact (hinner e he).1 hwInner
    · intro hvw
      subst w
      exact (hinner e he).2 hwInner
    · exact htri
    · exact hw
  have hwindow : ∀ e ∈ E,
      WithinMultiplicativeError ξ ((S e).card : ℝ≥0)
        (p ^ 2 * eta * (W.U i.succ).card) := by
    intro e he
    exact htyp.edge_extension_window i hstage
      (out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (houter e he).1 (houter e he).2 (hadjEdge e he) hh
  have hmS : ∀ e ∈ E, m ≤ (S e).card := by
    intro e he
    exact_mod_cast hm.trans (hwindow e he).1
  have hcutoffS : ∀ e ∈ E,
      (cutoff : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S e).card / 4 := by
    intro e he
    have hmSR : (m : ℝ) ≤ ((S e).card : ℝ) := by
      exact_mod_cast hmS e he
    calc
      (cutoff : ℝ) ≤ ((r ^ 2 : ℝ≥0) : ℝ) * m / 4 := hcutoff
      _ ≤ ((r ^ 2 : ℝ≥0) : ℝ) * (S e).card / 4 := by gcongr
  have hraw := reserveEdgeLaw_probability_not_allReserveWedgeSupplies_le
    G (W.U i.succ) E (fun e : Sym2 V ↦ e.out.1)
      (fun e : Sym2 V ↦ e.out.2) S (fun _ ↦ cutoff) r hr
      (fun e he ↦ out_fst_ne_snd_of_mem_graphEdges (hedge e he))
      (fun e he ↦ (hinner e he).1) (fun e he ↦ (hinner e he).2)
      hSU hadj (fun _e _he ↦ hcutoffS _e _he)
  have hsum :
      ∑ e ∈ E, Real.exp
          (-(((r ^ 2 : ℝ≥0) : ℝ) * (S e).card) / 4) ≤
        (E.card : ℝ) *
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by
    calc
      ∑ e ∈ E, Real.exp
          (-(((r ^ 2 : ℝ≥0) : ℝ) * (S e).card) / 4) ≤
        ∑ _e ∈ E,
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by
        apply sum_le_sum
        intro e he
        rw [Real.exp_le_exp]
        have hmSR : (m : ℝ) ≤ ((S e).card : ℝ) := by
          exact_mod_cast hmS e he
        have hr2 : 0 ≤ ((r ^ 2 : ℝ≥0) : ℝ) := by positivity
        nlinarith
      _ = (E.card : ℝ) *
          Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by simp
  have hreal :
      ((reserveEdgeLaw G (W.U i.succ) r hr).probability
        (fun bits ↦ ¬ InternalOuterReserveGood W i G A cutoff bits) : ℝ) ≤
        (epsilon : ℝ) := by
    have hevent : (fun bits ↦ ¬ InternalOuterReserveGood W i G A cutoff bits) =
        (fun bits ↦ ¬ AllReserveWedgeSupplies G (W.U i.succ) E
          (fun e ↦ e.out.1) (fun e ↦ e.out.2) S
          (fun _ ↦ cutoff) bits) := by
      rfl
    rw [hevent]
    exact hraw.trans (hsum.trans (by simpa only [E] using hfailure))
  exact_mod_cast hreal

/-- A good reserve outcome gives a successful internal-edge random-greedy
kernel and its uniform C4 bound. -/
theorem internalOuterEdge_randomGreedyKernel_of_goodReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell}
    {F : ForbiddenFamilyOn V}
    {G : SimpleGraph V} {A P0 : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell)
    (hpacking0 : IsPackingOn P0) (havoid0 : AvoidsForbidden P0 F)
    (bits : Sym2 V → Bool)
    (a D horizon : ℕ) (hD : 0 < D)
    (horizonBound : (internalOuterEdges G (W.U i.succ)).card ≤ horizon)
    (hgood : InternalOuterReserveGood W i G A (a + D) bits)
    (hblocked : ∀ (Q : TripleSystemOn V) (e : Sym2 V),
      ∀ hreach : GreedyReachable F P0 Q,
      Q ⊆ P0 ∪ A →
      (Q \ P0).card ≤ (internalOuterEdges G (W.U i.succ)).card →
      ∀ he : e ∈ internalOuterEdges G (W.U i.succ),
      ∀ hleave : (leaveGraph Q).Adj e.out.1 e.out.2,
      (edgeBlockedThirdVertices A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he)) ∪
        forbiddenBlockedThirdVertices F A Q
          (out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) he))).card ≤ a) :
    let E := internalOuterEdges G (W.U i.succ)
    let S : Sym2 V → Finset V := fun e ↦
      iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
    let hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := fun e he ↦
      out_fst_ne_snd_of_mem_graphEdges
        (internalOuterEdges_subset_graphEdges G (W.U i.succ)
          (by simpa only [Finset.mem_toList] using he))
    let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
      E.toList hne D P0
    L.SupportedOn (fun z ↦
        GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
          (z.chosen \ P0).card ≤ E.card ∧
          ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) ∧
      ∀ Q : TripleSystemOn V,
        L.probability (fun z ↦ Q ⊆ z.chosen \ P0) ≤
          internalEdgeC4Factor D horizon ^ Q.card := by
  dsimp only
  let E := internalOuterEdges G (W.U i.succ)
  let S : Sym2 V → Finset V := fun e ↦
    iterationExtensionVertices A
      (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)
  have hne : ∀ e, e ∈ E.toList → e.out.1 ≠ e.out.2 := by
    intro e he
    apply out_fst_ne_snd_of_mem_graphEdges
    exact internalOuterEdges_subset_graphEdges G (W.U i.succ)
      (by simpa only [E, Finset.mem_toList] using he)
  have hu : ∀ e, e ∈ E.toList → e.out.1 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.1
  have hv : ∀ e, e ∈ E.toList → e.out.2 ∉ W.U i.succ := by
    intro e he
    exact (mem_internalOuterEdges_iff.mp
      (by simpa only [E, Finset.mem_toList] using he)).2.2
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
    have hwS := (mem_activeReserveWedgeVertices_iff.mp hw).1
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem
      (hne e he) (hu e he) (hv e he) hwS
  have hgood' : ∀ e ∈ E, a + D <
      (activeReserveWedgeVertices G (W.U i.succ) (S e)
        e.out.1 e.out.2 bits).card := by
    simpa only [InternalOuterReserveGood, E, S,
      AllReserveWedgeSupplies] using hgood
  have hfloor : ∀ Q e (he : e ∈ E.toList), GreedyReachable F P0 Q →
      Q ⊆ P0 ∪ A → (Q \ P0).card ≤ E.toList.length →
      ¬(coveredGraph Q).Adj e.out.1 e.out.2 →
      D ≤ (activeReserveLegalThirdVertices F G (W.U i.succ) (S e)
        bits Q e.out.1 e.out.2 (hne e he)).card := by
    intro Q e he hreach hsub hcard huncovered
    have heE : e ∈ internalOuterEdges G (W.U i.succ) := by
      simpa only [E, Finset.mem_toList] using he
    have hleave : (leaveGraph Q).Adj e.out.1 e.out.2 := by
      apply leaveGraph_adj.mpr
      refine ⟨hne e he, ?_⟩
      rintro ⟨T, hTQ, hleft, hright, hneT⟩
      exact huncovered (coveredGraph_adj.mpr
        ⟨T, hTQ, hleft, hright, hneT⟩)
    have hcardE : (Q \ P0).card ≤
        (internalOuterEdges G (W.U i.succ)).card := by
      simpa only [E, Finset.length_toList] using hcard
    have hblock := hblocked Q e hreach hsub hcardE heE hleave
    have hsupply := hgood' e (by simpa only [E] using heE)
    have hcount :
        (edgeBlockedThirdVertices A Q hleave.ne ∪
          forbiddenBlockedThirdVertices F A Q hleave.ne).card + D ≤
        (activeReserveWedgeVertices G (W.U i.succ) (S e)
          e.out.1 e.out.2 bits).card := by
      have hproof : hleave.ne =
          out_fst_ne_snd_of_mem_graphEdges
            (internalOuterEdges_subset_graphEdges G (W.U i.succ) heE) :=
        Subsingleton.elim _ _
      rw [hproof]
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
      hleave (hu e he) (hv e he) (hSU e he) bits hA D hcount
    simpa only using hlegal
  let L := internalEdgeGreedyProcessLaw F G (W.U i.succ) bits S
    E.toList hne D P0
  have hcomplete := internalEdgeGreedyProcessLaw_supported_complete_ambient
    F G (W.U i.succ) bits S E.toList hne D hD P0 A hAactive hfloor
  have hsupp : L.SupportedOn (fun z ↦
      GreedyReachable F P0 z.chosen ∧ z.chosen ⊆ P0 ∪ A ∧
        (z.chosen \ P0).card ≤ E.card ∧
        ∀ e ∈ E, (coveredGraph z.chosen).Adj e.out.1 e.out.2) := by
    intro z hz
    have hz' := hcomplete z hz
    refine ⟨hz'.1.1, hz'.2.2, ?_, ?_⟩
    · simpa only [Finset.length_toList] using hz'.1.2.1
    · intro e he
      exact hz'.1.covers_mem hz'.2.1 e
        (by simpa only [Finset.mem_toList] using he)
  refine ⟨hsupp, ?_⟩
  intro Q
  apply internalEdgeGreedyProcess_probability_subset_newChosen_le_pow
    F G (W.U i.succ) bits S E.toList hne E.nodup_toList hu hv hSU
      D hD P0 horizon
  intro z hz
  exact (hsupp z hz).2.2.1.trans (by simpa only [E] using horizonBound)

end

end Erdos207
