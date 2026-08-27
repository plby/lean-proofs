/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryInternalSafeCandidates
import ErdosProblems.Erdos207.LocalizedPreliminaryResidualInternalKernel

/-! # Outer-only safe candidates for the localized internal kernel -/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

theorem exists_localizedRawResidualInternalKernel_of_outerOnly
    {Omega V : Type*} [Fintype Omega] [Fintype V]
    [DecidableEq V] {ell : ℕ} {W : Vortex V ell}
    {stage : Fin (ell + 1)} {F : ForbiddenFamilyOn V}
    {G : Omega → SimpleGraph V}
    {A P M : Omega → TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (Good : Omega → Prop)
    (htyp : ∀ omega, Good omega →
      IsIterationTypical W stage (G omega) (A omega) p eta xi h)
    (htri : ∀ omega, Good omega → ConsistsOfTriangles (G omega) (A omega))
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : ∀ omega, Good omega →
      GraphSupportedOn (G omega) (W.U i.castSucc : Set V))
    (hpacking : ∀ omega, Good omega →
      IsPackingOn (P omega ∪ M omega))
    (havoid : ∀ omega, Good omega →
      AvoidsForbidden (P omega ∪ M omega) F)
    (hold : ∀ omega, Good omega → ∀ T ∈ A omega,
      TriangleAvoidsGraph (coveredGraph (P omega)) T)
    (houterOnly : ∀ omega, Good omega →
      TrianglesDisjointFrom (W.U i.succ) (M omega))
    (hh : 2 ≤ h) (reserveRate : ℝ≥0) (hreserveRate : reserveRate ≤ 1)
    (m a D d R k : ℕ) (hD : 0 < D)
    (hm : (m : ℝ≥0) ≤
      (1 - xi) * (p ^ 2 * eta * (W.U i.succ).card))
    (ha : ((a + D : ℕ) : ℝ) ≤
      ((reserveRate ^ 2 : ℝ≥0) : ℝ) * m / 4)
    (hsmallUniform : ∀ omega, Good omega →
      let E := preliminaryResidualInternalEdges
        (G omega) (W.U i.succ) (P omega ∪ M omega)
      (E.card : ℝ) *
        Real.exp
          (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) < 1)
    (hfamily : ∀ C ∈ F, C.card ≤ k)
    (hincidence : ∀ omega, Good omega → ∀ v : V,
      (scheduledEdgesAt
        (preliminaryResidualInternalEdges (G omega) (W.U i.succ)
          (P omega ∪ M omega)) v).card ≤ d)
    (hscalar : 4 * d + R * k ≤ a) :
    let Aint : Omega → TripleSystemOn V := fun omega ↦
      pairSafeAvailable (A omega) (P omega ∪ M omega)
    let P0 : Omega → TripleSystemOn V := fun omega ↦ P omega ∪ M omega
    ∃ bits : Omega → Sym2 V → Bool,
      (∀ omega, Good omega →
        LocalizedRawResidualInternalFiberGood W i F G Aint P0 bits D R omega) ∧
      ∀ omega Q,
        (rawResidualInternalKernel W i F G Aint P0 bits D omega).probability
          (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
            ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  dsimp only
  let Aint : Omega → TripleSystemOn V := fun omega ↦
    pairSafeAvailable (A omega) (P omega ∪ M omega)
  let P0 : Omega → TripleSystemOn V := fun omega ↦ P omega ∪ M omega
  apply exists_localizedRawResidualInternalKernel_of_directSupply Good
      (G := G) (A := Aint) (P0 := P0) (i := i)
      (reserveRate := reserveRate) (a := a) (D := D) (d := d)
      (R := R) (k := k)
  · intro omega hgood
    exact (htri omega hgood).pairSafeAvailable
  · exact hpacking
  · exact havoid
  · intro omega _hgood
    exact pairSafeAvailable_triangleAvoids _ _
  · exact hreserveRate
  · exact hD
  · intro omega hgood
    dsimp only
    intro e he
    have heInternal : e ∈ internalOuterEdges (G omega) (W.U i.succ) :=
      preliminaryResidualInternalEdges_subset_internalOuterEdges
        (G omega) (W.U i.succ) (P omega ∪ M omega) he
    have heGraph : e ∈ graphEdges (G omega) :=
      internalOuterEdges_subset_graphEdges (G omega) (W.U i.succ) heInternal
    have hadj : (G omega).Adj e.out.1 e.out.2 :=
      graph_adj_out_of_mem_graphEdges heGraph
    have hsupport := hGsupp omega hgood hadj
    have hne := out_fst_ne_snd_of_mem_graphEdges heGraph
    have hwindow := (htyp omega hgood).edge_extension_window i hstage hne
      hsupport.1 hsupport.2 hadj hh
    have hmInitial : m ≤
        (iterationExtensionVertices (A omega)
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)).card := by
      exact_mod_cast hm.trans hwindow.1
    have hmSafe : m ≤
        (iterationExtensionVertices (Aint omega)
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)).card :=
      hmInitial.trans (by
        simpa only [Aint] using card_iterationExtensionVertices_pairSafe_ge
          he (houterOnly omega hgood) (hold omega hgood))
    have hmSafeR : (m : ℝ) ≤
        ((iterationExtensionVertices (Aint omega)
          (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)).card : ℝ) := by
      exact_mod_cast hmSafe
    exact ha.trans (by gcongr)
  · intro omega hgood
    dsimp only
    let E := preliminaryResidualInternalEdges
      (G omega) (W.U i.succ) (P omega ∪ M omega)
    change
      (∑ e ∈ E,
          (let S := residualInternalExtensionSet W i (Aint omega) e
           Real.exp
             (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card) / 4))) < 1
    calc
      ∑ e ∈ E,
          (let S := residualInternalExtensionSet W i (Aint omega) e;
            Real.exp
              (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * S.card) / 4)) ≤
          ∑ _e ∈ E,
            Real.exp
              (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by
        apply sum_le_sum
        intro e he
        rw [Real.exp_le_exp]
        have heInternal : e ∈ internalOuterEdges (G omega) (W.U i.succ) :=
          preliminaryResidualInternalEdges_subset_internalOuterEdges
            (G omega) (W.U i.succ) (P omega ∪ M omega) he
        have heGraph : e ∈ graphEdges (G omega) :=
          internalOuterEdges_subset_graphEdges
            (G omega) (W.U i.succ) heInternal
        have hadj : (G omega).Adj e.out.1 e.out.2 :=
          graph_adj_out_of_mem_graphEdges heGraph
        have hsupport := hGsupp omega hgood hadj
        have hne := out_fst_ne_snd_of_mem_graphEdges heGraph
        have hwindow := (htyp omega hgood).edge_extension_window i hstage hne
          hsupport.1 hsupport.2 hadj hh
        have hmInitial : m ≤
            (iterationExtensionVertices (A omega)
              (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)).card := by
          exact_mod_cast hm.trans hwindow.1
        have hmSafe : m ≤
            (iterationExtensionVertices (Aint omega)
              (SimpleGraph.edge e.out.1 e.out.2) (W.U i.succ)).card :=
          hmInitial.trans (by
            simpa only [Aint] using
              card_iterationExtensionVertices_pairSafe_ge he
                (houterOnly omega hgood) (hold omega hgood))
        have hmSafeR : (m : ℝ) ≤
            ((residualInternalExtensionSet W i (Aint omega) e).card : ℝ) := by
          exact_mod_cast hmSafe
        have hr2 : 0 ≤ ((reserveRate ^ 2 : ℝ≥0) : ℝ) := by positivity
        nlinarith
      _ = (E.card : ℝ) *
          Real.exp
            (-(((reserveRate ^ 2 : ℝ≥0) : ℝ) * m) / 4) := by simp
      _ < 1 := hsmallUniform omega hgood
  · exact hfamily
  · exact hincidence
  · exact hscalar

end

end Erdos207
