/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.ReserveProtectedPairAlive

/-!
# The common reserve-good event

The same sampled crossing reserve must do two jobs.  It supplies two-spoke
wedges for the later internal-edge cover, while its complement must leave a
live pair star for every edge on which the preliminary process can run.
This file intersects those events and records their uniform union bound.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- The reserve outcome simultaneously supports the internal and protected
preliminary stages. -/
def ReserveProtectedStageGood
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (G : SimpleGraph V) (A P : TripleSystemOn V) (cutoff : ℕ)
    (bits : Sym2 V → Bool) : Prop :=
  InternalOuterReserveGood W i G A cutoff bits ∧
    ReserveProtectedPairAliveGood G (W.U i.succ) A P bits

theorem probability_not_reserveProtectedStageGood_le_of_parts
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} (W : Vortex V ell) (i : Fin ell)
    (G : SimpleGraph V) (A P : TripleSystemOn V) (cutoff : ℕ)
    (r : ℝ≥0) (hr : r ≤ 1)
    (epsilonSupply epsilonAlive : ℝ≥0)
    (hSupply : (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ InternalOuterReserveGood W i G A cutoff bits) ≤
        epsilonSupply)
    (hAlive : (reserveEdgeLaw G (W.U i.succ) r hr).probability
      (fun bits ↦ ¬ ReserveProtectedPairAliveGood G (W.U i.succ)
        A P bits) ≤ epsilonAlive) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability
        (fun bits ↦ ¬ ReserveProtectedStageGood W i G A P cutoff bits) ≤
      epsilonSupply + epsilonAlive := by
  let L := reserveEdgeLaw G (W.U i.succ) r hr
  have hmono : L.probability
      (fun bits ↦ ¬ ReserveProtectedStageGood W i G A P cutoff bits) ≤
      L.probability (fun bits ↦
        ¬ InternalOuterReserveGood W i G A cutoff bits ∨
          ¬ ReserveProtectedPairAliveGood G (W.U i.succ) A P bits) := by
    apply L.probability_mono
    intro bits hbad
    simpa only [ReserveProtectedStageGood, not_and_or] using hbad
  exact hmono.trans ((L.probability_or_le _ _).trans
    (add_le_add hSupply hAlive))

/-- Iteration typicality discharges both parts of the common reserve event.
All numerical estimates remain explicit so this theorem can be instantiated
uniformly over the support of a state-dependent master law. -/
theorem IsIterationTypical.reserveEdgeLaw_probability_not_reserveProtectedStageGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A P : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (r : ℝ≥0) (hr : r ≤ 1)
    (mSupply cutoff : ℕ)
    (hmSupply : (mSupply : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : (cutoff : ℝ) ≤
      ((r ^ 2 : ℝ≥0) : ℝ) * mSupply / 4)
    (epsilonSupply : ℝ≥0)
    (hfailureSupply :
      ((internalOuterEdges G (W.U i.succ)).card : ℝ) *
        Real.exp (-(((r ^ 2 : ℝ≥0) : ℝ) * mSupply) / 4) ≤
          epsilonSupply)
    (mAlive : ℕ)
    (hgapAlive :
      ((((W.U i.succ).card + 2 + mAlive : ℕ) : ℝ≥0)) <
        (1 - xi) *
          (p ^ 2 * eta * (W.U i.castSucc).card))
    (epsilonAlive : ℝ≥0)
    (hfailureAlive :
      ((outerGraphEdges G (W.U i.succ)).card : ℝ≥0) * r ^ mAlive ≤
        epsilonAlive) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability
        (fun bits ↦ ¬ ReserveProtectedStageGood W i G A P cutoff bits) ≤
      epsilonSupply + epsilonAlive := by
  have hSupply :=
    htyp.reserveEdgeLaw_probability_not_internalOuterReserveGood_le
      htri i hstage hGsupp hh r hr mSupply cutoff hmSupply hcutoff
        epsilonSupply hfailureSupply
  have hAlive :=
    (htyp.reserveEdgeLaw_probability_not_reserveProtectedPairAliveGood_le
      (P := P) htri i hstage hGsupp hh mAlive hgapAlive r hr).trans
        hfailureAlive
  exact probability_not_reserveProtectedStageGood_le_of_parts
    W i G A P cutoff r hr epsilonSupply epsilonAlive hSupply hAlive

/-- With the full crossing reserve, both parts of the reserve-good event are
deterministic.  Typicality supplies every internal edge with enough wedge
vertices, while every edge left for the preliminary process is necessarily
outside--outside and hence has an unaffected outer extension. -/
theorem IsIterationTypical.reserveProtectedStageGood_of_fullReserve
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A P : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (bits : Sym2 V → Bool)
    (hfull : reserveEdges G (W.U i.succ) bits =
      crossingEdges G (W.U i.succ))
    (mSupply cutoff : ℕ)
    (hmSupply : (mSupply : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (hcutoff : cutoff < mSupply)
    (hgapAlive : ((((W.U i.succ).card + 2 : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card)) :
    ReserveProtectedStageGood W i G A P cutoff bits := by
  let U := W.U i.succ
  let Uouter := W.U i.castSucc
  have hsupply : InternalOuterReserveGood W i G A cutoff bits := by
    let E := internalOuterEdges G U
    let S : Sym2 V → Finset V := fun e ↦
      iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U
    change AllReserveWedgeSupplies G U E
      (fun e ↦ e.out.1) (fun e ↦ e.out.2) S (fun _ ↦ cutoff) bits
    intro e he
    have hedge : e ∈ graphEdges G :=
      (mem_internalOuterEdges_iff.mp he).1
    have hadjEdge : G.Adj e.out.1 e.out.2 :=
      graph_adj_out_of_mem_graphEdges hedge
    have houter : e.out.1 ∈ Uouter ∧ e.out.2 ∈ Uouter :=
      hGsupp hadjEdge
    have hinner : e.out.1 ∉ U ∧ e.out.2 ∉ U :=
      (mem_internalOuterEdges_iff.mp he).2
    have hSU : S e ⊆ U :=
      iterationExtensionVertices_subset A
        (SimpleGraph.edge e.out.1 e.out.2) U
    have hadj : ∀ w ∈ S e,
        G.Adj e.out.1 w ∧ G.Adj e.out.2 w := by
      intro w hw
      have hwU := hSU hw
      exact iterationExtensionVertices_edge_adjacencies
        (out_fst_ne_snd_of_mem_graphEdges hedge)
        (fun huw ↦ hinner.1 (huw ▸ hwU))
        (fun hvw ↦ hinner.2 (hvw ▸ hwU)) htri hw
    have hwindow : WithinMultiplicativeError xi ((S e).card : ℝ≥0)
        (p ^ 2 * eta * (W.U i.succ).card) := by
      exact htyp.edge_extension_window i hstage
        (out_fst_ne_snd_of_mem_graphEdges hedge) houter.1 houter.2
        hadjEdge hh
    have hmS : mSupply ≤ (S e).card := by
      exact_mod_cast hmSupply.trans hwindow.1
    have hcross : ∀ w ∈ S e,
        reserveWedgeBlock e.out.1 e.out.2 w ⊆ crossingEdges G U := by
      intro w hw
      exact reserveWedgeBlock_subset_crossingEdges hinner.1 hinner.2
        (hSU hw) (hadj w hw).1 (hadj w hw).2
    rw [activeReserveWedgeVertices_eq_of_reserveEdges_eq_crossingEdges
      hcross (by simpa only [U] using hfull)]
    exact hcutoff.trans_le hmS
  refine ⟨hsupply, ?_⟩
  intro e heProtected
  have heOuter : e ∈ outerGraphEdges G U := (mem_sdiff.mp heProtected).1
  have heNotCross : e ∉ crossingEdges G U := by
    intro heCross
    exact (mem_sdiff.mp heProtected).2 (by
      rw [hfull]
      exact heCross)
  have heInternal : e ∈ internalOuterEdges G U :=
    mem_internalOuterEdges_of_mem_outerGraphEdges_of_not_crossing
      heOuter heNotCross
  have haliveOuter := htyp.internalOuter_pairAlive_outerOnly i hstage
    hGsupp hh (by simpa only [U, Uouter] using hgapAlive) P heInternal
  exact haliveOuter.of_available_subset
    (outerOnlyAvailable_subset_reserveProtectedOuterAvailable htri bits)

end

end Erdos207
