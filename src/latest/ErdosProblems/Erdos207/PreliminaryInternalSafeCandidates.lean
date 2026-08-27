/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.PreliminaryResidualInternalDirectKernel

/-!
# Internal candidates protected by an outer-only preliminary family

If every preliminary triangle is disjoint from the next vortex set, it can
consume neither spoke of a candidate which completes an outside--outside
edge through an inner vertex.  For an edge which is still residual, it also
did not consume the outside edge itself.  Thus all initial one-edge
extension vertices survive in the pair-safe subfamily used by the internal
stage.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Every triangle in `P` is wholly outside `U`. -/
def TrianglesDisjointFrom
    {V : Type*} [DecidableEq V]
    (U : Finset V) (P : TripleSystemOn V) : Prop :=
  ∀ T ∈ P, Disjoint T.1 U

/-- The part of an ambient family whose pairs are all uncovered by `P`. -/
def pairSafeAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) : TripleSystemOn V := by
  classical
  exact A.filter fun T ↦ TriangleAvoidsGraph (coveredGraph P) T

@[simp]
lemma mem_pairSafeAvailable_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A P : TripleSystemOn V} {T : TripleOn V} :
    T ∈ pairSafeAvailable A P ↔
      T ∈ A ∧ TriangleAvoidsGraph (coveredGraph P) T := by
  simp [pairSafeAvailable]

lemma pairSafeAvailable_subset_left
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) : pairSafeAvailable A P ⊆ A := by
  intro T hT
  exact (mem_pairSafeAvailable_iff.mp hT).1

lemma pairSafeAvailable_triangleAvoids
    {V : Type*} [Fintype V] [DecidableEq V]
    (A P : TripleSystemOn V) :
    ∀ T ∈ pairSafeAvailable A P,
      TriangleAvoidsGraph (coveredGraph P) T := by
  intro T hT
  exact (mem_pairSafeAvailable_iff.mp hT).2

lemma ConsistsOfTriangles.pairSafeAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A P : TripleSystemOn V}
    (hA : ConsistsOfTriangles G A) :
    ConsistsOfTriangles G (pairSafeAvailable A P) := by
  intro T hT
  exact hA T (pairSafeAvailable_subset_left A P hT)

/-- A triangle through two outer endpoints and one inner vertex avoids an
outer-only packing as soon as its outside edge is still uncovered. -/
lemma thirdVertexTriple_avoids_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {M : TripleSystemOn V} {u v : V}
    (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hM : TrianglesDisjointFrom U M)
    (hnot : ¬ (coveredGraph M).Adj u v)
    (w : ThirdVertex u v) (hwU : w.1 ∈ U) :
    TriangleAvoidsGraph (coveredGraph M) (thirdVertexTriple huv w) := by
  intro x hx y hy hxy hcovered
  obtain ⟨S, hSM, hxS, hyS, _hxyS⟩ := coveredGraph_adj.mp hcovered
  have hdisj := hM S hSM
  have hnotwS : w.1 ∉ S.1 := by
    intro hwS
    exact Finset.disjoint_left.mp hdisj hwS hwU
  simp only [thirdVertexTriple, tripleOfThree, mem_insert,
    mem_singleton] at hx hy
  have hxuv : x = u ∨ x = v := by
    rcases hx with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hnotwS hxS).elim
  have hyuv : y = u ∨ y = v := by
    rcases hy with rfl | rfl | rfl
    · exact Or.inl rfl
    · exact Or.inr rfl
    · exact (hnotwS hyS).elim
  rcases hxuv with rfl | rfl <;> rcases hyuv with rfl | rfl
  · exact hxy rfl
  · exact hnot (coveredGraph_adj.mpr ⟨S, hSM, hxS, hyS, huv⟩)
  · exact hnot (coveredGraph_adj.mpr ⟨S, hSM, hyS, hxS, huv⟩)
  · exact hxy rfl

/-- Pair-avoidance with respect to an old packing and an outer-only new
packing combines across their union. -/
lemma thirdVertexTriple_avoids_old_union_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {U : Finset V} {P M : TripleSystemOn V} {u v : V}
    (huv : u ≠ v) (hu : u ∉ U) (hv : v ∉ U)
    (hM : TrianglesDisjointFrom U M)
    (hnot : ¬ (coveredGraph (P ∪ M)).Adj u v)
    (w : ThirdVertex u v) (hwU : w.1 ∈ U)
    (hold : TriangleAvoidsGraph (coveredGraph P)
      (thirdVertexTriple huv w)) :
    TriangleAvoidsGraph (coveredGraph (P ∪ M))
      (thirdVertexTriple huv w) := by
  have hnotM : ¬ (coveredGraph M).Adj u v := by
    intro hcovered
    apply hnot
    obtain ⟨T, hTM, huT, hvT, huvT⟩ := coveredGraph_adj.mp hcovered
    exact coveredGraph_adj.mpr
      ⟨T, mem_union_right P hTM, huT, hvT, huvT⟩
  have hnew := thirdVertexTriple_avoids_outerOnly huv hu hv hM hnotM w hwU
  intro x hx y hy hxy hcovered
  obtain ⟨T, hT, hxT, hyT, hxyT⟩ := coveredGraph_adj.mp hcovered
  rcases mem_union.mp hT with hTP | hTM
  · exact hold x hx y hy hxy
      (coveredGraph_adj.mpr ⟨T, hTP, hxT, hyT, hxyT⟩)
  · exact hnew x hx y hy hxy
      (coveredGraph_adj.mpr ⟨T, hTM, hxT, hyT, hxyT⟩)

/-- Every initial inner extension of a residual outside--outside edge is
still present in the pair-safe family after an outer-only preliminary
packing. -/
lemma iterationExtensionVertices_subset_pairSafe_of_outerOnly
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {A P M : TripleSystemOn V} {e : Sym2 V}
    (he : e ∈ preliminaryResidualInternalEdges G U (P ∪ M))
    (hM : TrianglesDisjointFrom U M)
    (hold : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P) T) :
    iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U ⊆
      iterationExtensionVertices (pairSafeAvailable A (P ∪ M))
        (SimpleGraph.edge e.out.1 e.out.2) U := by
  intro w hw
  have heInternal :=
    preliminaryResidualInternalEdges_subset_internalOuterEdges G U (P ∪ M) he
  have heGraph := internalOuterEdges_subset_graphEdges G U heInternal
  have hne := out_fst_ne_snd_of_mem_graphEdges heGraph
  have houter := (mem_internalOuterEdges_iff.mp heInternal).2
  have hwU := iterationExtensionVertices_subset A
    (SimpleGraph.edge e.out.1 e.out.2) U hw
  let w' : ThirdVertex e.out.1 e.out.2 :=
    ⟨w, fun h ↦ houter.1 (h ▸ hwU), fun h ↦ houter.2 (h ▸ hwU)⟩
  have hTA : thirdVertexTriple hne w' ∈ A :=
    iterationExtensionVertices_edge_thirdVertexTriple_mem
      hne houter.1 houter.2 hw
  have hnot : ¬ (coveredGraph (P ∪ M)).Adj e.out.1 e.out.2 := by
    intro hcovered
    have heResidual :=
      preliminaryResidualInternalEdges_subset_residualOuterEdges
        G U (P ∪ M) he
    apply (mem_sdiff.mp heResidual).2
    rw [← e.out_eq]
    exact mem_graphEdges_iff.mpr hcovered
  have hsafe : thirdVertexTriple hne w' ∈ pairSafeAvailable A (P ∪ M) := by
    apply mem_pairSafeAvailable_iff.mpr
    exact ⟨hTA,
      thirdVertexTriple_avoids_old_union_outerOnly hne houter.1 houter.2
        hM hnot w' hwU (hold _ hTA)⟩
  apply mem_iterationExtensionVertices_iff.mpr
  refine ⟨hwU, ?_⟩
  intro f hf
  rw [graphEdges_edge hne] at hf
  have hfe : f = s(e.out.1, e.out.2) := by simpa using hf
  subst f
  refine ⟨thirdVertexTriple hne w', hsafe,
    third_mem_thirdVertexTriple hne w', ?_⟩
  exact mk_mem_tripleEdgeFinset_iff.mpr
    ⟨left_mem_thirdVertexTriple hne w',
      right_mem_thirdVertexTriple hne w', hne⟩

lemma card_iterationExtensionVertices_pairSafe_ge
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V}
    {A P M : TripleSystemOn V} {e : Sym2 V}
    (he : e ∈ preliminaryResidualInternalEdges G U (P ∪ M))
    (hM : TrianglesDisjointFrom U M)
    (hold : ∀ T ∈ A, TriangleAvoidsGraph (coveredGraph P) T) :
    (iterationExtensionVertices A
        (SimpleGraph.edge e.out.1 e.out.2) U).card ≤
      (iterationExtensionVertices (pairSafeAvailable A (P ∪ M))
        (SimpleGraph.edge e.out.1 e.out.2) U).card :=
  card_le_card (iterationExtensionVertices_subset_pairSafe_of_outerOnly
    he hM hold)

/-- Initial iteration typicality supplies the direct residual-internal
kernel after an outer-only preliminary family.  The internal ambient family
is the pair-safe subfamily; it is still a subfamily of the original master
availability. -/
theorem exists_rawResidualInternalKernel_of_outerOnly
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
        RawResidualInternalFiberGood W i F G Aint P0 bits D R omega) ∧
      ∀ omega Q,
        (rawResidualInternalKernel W i F G Aint P0 bits D omega).probability
          (fun z ↦ Q ⊆ rawResidualInternalAdded P0 omega z) ≤
            ((D : ℝ≥0)⁻¹ ^ Q.card) := by
  dsimp only
  let Aint : Omega → TripleSystemOn V := fun omega ↦
    pairSafeAvailable (A omega) (P omega ∪ M omega)
  let P0 : Omega → TripleSystemOn V := fun omega ↦ P omega ∪ M omega
  apply exists_rawResidualInternalKernel_of_directSupply Good
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
