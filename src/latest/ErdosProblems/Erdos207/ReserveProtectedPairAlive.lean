/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Boris Alexeev, Codex
-/
import ErdosProblems.Erdos207.InternalEdgeConditionedKernel
import ErdosProblems.Erdos207.OuterOnlyPreliminaryGeometry
import ErdosProblems.Erdos207.ReserveProtectedPreliminaryGeometry

/-!
# Pair survival under a sampled reserve

The preliminary process runs only on edges outside the sampled crossing
reserve.  An outside--outside edge has a completely outside extension and is
therefore unaffected by the reserve.  A crossing edge has many completely
outside extension vertices; if it is itself absent from the reserve, such an
extension is lost only when its one other crossing edge is sampled.  Those
companion edges are distinct, so the product Bernoulli law gives the exact
power bound used below.
-/

namespace Erdos207

open Finset
open scoped NNReal

noncomputable section

/-- Extension vertices in the current vortex layer that lie outside the next
layer and differ from both endpoints. -/
def outerExtensionCandidates
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Uouter Uinner : Finset V) (u v : V) :
    Finset V :=
  iterationExtensionVertices A (SimpleGraph.edge u v) Uouter \
    (Uinner ∪ {u, v})

lemma outerExtensionCandidates_subset_extensions
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Uouter Uinner : Finset V) (u v : V) :
    outerExtensionCandidates A Uouter Uinner u v ⊆
      iterationExtensionVertices A (SimpleGraph.edge u v) Uouter :=
  sdiff_subset

lemma outerExtensionCandidates_comm
    {V : Type*} [Fintype V] [DecidableEq V]
    (A : TripleSystemOn V) (Uouter Uinner : Finset V) (u v : V) :
    outerExtensionCandidates A Uouter Uinner u v =
      outerExtensionCandidates A Uouter Uinner v u := by
  have hedge : SimpleGraph.edge u v = SimpleGraph.edge v u := by
    ext x y
    simp only [SimpleGraph.edge_adj]
    tauto
  simp only [outerExtensionCandidates, hedge]
  congr 2
  ext x
  simp [or_comm]

lemma mem_outerExtensionCandidates_iff
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {Uouter Uinner : Finset V} {u v w : V} :
    w ∈ outerExtensionCandidates A Uouter Uinner u v ↔
      w ∈ iterationExtensionVertices A (SimpleGraph.edge u v) Uouter ∧
        w ∉ Uinner ∧ w ≠ u ∧ w ≠ v := by
  rw [outerExtensionCandidates, mem_sdiff]
  simp only [mem_union, mem_insert, mem_singleton, not_or]

/-- Removing the next layer and the two endpoints costs at most
`|Uinner| + 2` candidates. -/
lemma card_outerExtensionCandidates_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {Uouter Uinner : Finset V} {u v : V}
    (d : ℕ)
    (hcard : Uinner.card + 2 + d <
      (iterationExtensionVertices A
        (SimpleGraph.edge u v) Uouter).card) :
    d < (outerExtensionCandidates A Uouter Uinner u v).card := by
  let S := iterationExtensionVertices A (SimpleGraph.edge u v) Uouter
  let B := Uinner ∪ {u, v}
  have hB : B.card ≤ Uinner.card + 2 := by
    calc
      B.card ≤ Uinner.card + ({u, v} : Finset V).card := card_union_le _ _
      _ ≤ Uinner.card + 2 := by
        gcongr
        by_cases huv : u = v <;> simp [huv]
  have hpartition := card_sdiff_add_card_inter S B
  have hinter : (S ∩ B).card ≤ B.card := card_le_card inter_subset_right
  have hS : Uinner.card + 2 + d < S.card := by
    simpa only [S] using hcard
  have hdiff : d < (S \ B).card := by omega
  simpa only [outerExtensionCandidates, S, B] using hdiff

/-- The canonical triangle through an extension vertex, assuming directly
that the vertex differs from the endpoints. -/
lemma iterationExtensionVertices_edge_thirdVertexTriple_mem_of_ne
    {V : Type*} [Fintype V] [DecidableEq V]
    {A : TripleSystemOn V} {U : Finset V}
    {u v w : V} (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hw : w ∈ iterationExtensionVertices A (SimpleGraph.edge u v) U) :
    thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩ ∈ A := by
  have hwdata := mem_iterationExtensionVertices_iff.mp hw
  have hedge : s(u, v) ∈ graphEdges (SimpleGraph.edge u v) := by
    rw [graphEdges_edge huv]
    simp
  obtain ⟨T, hTA, hwT, heT⟩ := hwdata.2 s(u, v) hedge
  have huvT := mk_mem_tripleEdgeFinset_iff.mp heT
  have hsub :
      (thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩).1 ⊆ T.1 := by
    intro x hx
    simp only [thirdVertexTriple, tripleOfThree, mem_insert,
      mem_singleton] at hx
    rcases hx with rfl | rfl | rfl
    · exact huvT.1
    · exact huvT.2.1
    · exact hwT
  have heq : thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩ = T := by
    apply Subtype.ext
    exact Finset.eq_of_subset_of_card_le hsub (by
      rw [T.2]
      exact (thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩).2.ge)
  rw [heq]
  exact hTA

/-- In the orientation `u ∈ U`, `v,w ∉ U`, a nonsampled fixed edge
and nonsampled companion edge give a triangle of the protected preliminary
family. -/
lemma thirdVertexTriple_mem_reserveProtectedOuterAvailable_of_left_inside
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {Uouter U : Finset V} {u v w : V} {bits : Sym2 V → Bool}
    (htri : ConsistsOfTriangles G A)
    (huv : u ≠ v) (huw : u ≠ w) (hvw : v ≠ w)
    (hu : u ∈ U) (hv : v ∉ U) (hwU : w ∉ U)
    (hw : w ∈ iterationExtensionVertices A
      (SimpleGraph.edge u v) Uouter)
    (huvFalse : bits s(u, v) = false)
    (huwFalse : bits s(u, w) = false) :
    thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩ ∈
      reserveProtectedOuterAvailable G U (reserveEdges G U bits) A := by
  let T : TripleOn V := thirdVertexTriple huv ⟨w, huw.symm, hvw.symm⟩
  have hTA : T ∈ A := by
    exact iterationExtensionVertices_edge_thirdVertexTriple_mem_of_ne
      huv huw hvw hw
  rw [mem_reserveProtectedOuterAvailable_iff]
  refine ⟨hTA, ?_⟩
  intro e heT
  induction e using Sym2.inductionOn with
  | _ x y =>
      have hxy := mk_mem_tripleEdgeFinset_iff.mp heT
      have hx : x = u ∨ x = v ∨ x = w := by
        simpa only [T, thirdVertexTriple, tripleOfThree, mem_insert,
          mem_singleton] using hxy.1
      have hy : y = u ∨ y = v ∨ y = w := by
        simpa only [T, thirdVertexTriple, tripleOfThree, mem_insert,
          mem_singleton] using hxy.2.1
      rw [reserveProtectedOuterEdges, mem_sdiff]
      refine ⟨?_, ?_⟩
      · rw [mem_outerGraphEdges_iff]
        refine ⟨mem_graphEdges_iff.mpr
          (htri T hTA x hxy.1 y hxy.2.1 hxy.2.2), ?_⟩
        intro hsub
        have hxU : x ∈ U := hsub (by simp)
        have hyU : y ∈ U := hsub (by simp)
        rcases hx with rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl <;> simp_all
      · intro heReserve
        have htrue := (mem_reserveEdges_iff.mp heReserve).2
        have hcross := isCrossingEdge_mk_iff.mp
          (mem_crossingEdges_iff.mp
            (reserveEdges_subset_crossingEdges G U bits heReserve)).2
        have hvuFalse : bits s(v, u) = false := by
          simpa only [Sym2.eq_swap] using huvFalse
        have hwuFalse : bits s(w, u) = false := by
          simpa only [Sym2.eq_swap] using huwFalse
        rcases hx with rfl | rfl | rfl <;>
          rcases hy with rfl | rfl | rfl <;> simp_all

/-- Companion edges based at a fixed inside endpoint. -/
def reserveCompanionEdges
    {V : Type*} [DecidableEq V] (u : V) (S : Finset V) :
    Finset (Sym2 V) :=
  S.image fun w ↦ s(u, w)

lemma card_reserveCompanionEdges
    {V : Type*} [DecidableEq V] {u : V} {S : Finset V}
    (hu : ∀ w ∈ S, w ≠ u) :
    (reserveCompanionEdges u S).card = S.card := by
  rw [reserveCompanionEdges, card_image_iff]
  intro x hx y hy hxy
  simp only [Sym2.eq_iff] at hxy
  rcases hxy with hxy | hxy
  · exact hxy.2
  · exact (hu x hx hxy.2).elim

lemma reserveCompanionEdges_subset_crossingEdges
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {Uouter U : Finset V} {u v : V}
    (htri : ConsistsOfTriangles G A) (huv : u ≠ v)
    (hu : u ∈ U)
    (S : Finset V)
    (hS : S ⊆ outerExtensionCandidates A Uouter U u v) :
    reserveCompanionEdges u S ⊆ crossingEdges G U := by
  intro e he
  obtain ⟨w, hwS, rfl⟩ := mem_image.mp he
  have hwdata := mem_outerExtensionCandidates_iff.mp (hS hwS)
  simpa only [Sym2.eq_swap] using
    crossingEdge_mk_of_outside_inside hwdata.2.1 hu
      (iterationExtensionVertices_edge_adjacencies huv
        hwdata.2.2.1.symm hwdata.2.2.2.symm htri hwdata.1).1.symm

/-- Fixed-edge failure bound in the orientation where the first endpoint is
inside the next vortex layer. -/
theorem reserveEdgeLaw_probability_not_pairAlive_left_inside_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A P : TripleSystemOn V)
    (Uouter U : Finset V) (u v : V)
    (htri : ConsistsOfTriangles G A) (huv : u ≠ v)
    (hu : u ∈ U) (hv : v ∉ U)
    (huvCross : s(u, v) ∈ crossingEdges G U)
    (r : ℝ≥0) (hr : r ≤ 1) (m : ℕ)
    (hm : m ≤ (outerExtensionCandidates A Uouter U u v).card) :
    (reserveEdgeLaw G U r hr).probability (fun bits ↦
        s(u, v) ∈ reserveProtectedOuterEdges G U (reserveEdges G U bits) ∧
          ¬ PairAlive s(u, v).toFinset
            (relativePreliminaryInitialState P
              (reserveProtectedOuterAvailable G U
                (reserveEdges G U bits) A))) ≤
      r ^ m := by
  let S := outerExtensionCandidates A Uouter U u v
  let C := reserveCompanionEdges u S
  let L := reserveEdgeLaw G U r hr
  have hCcross : C ⊆ crossingEdges G U := by
    exact reserveCompanionEdges_subset_crossingEdges htri huv hu S Subset.rfl
  have hCcard : C.card = S.card := by
    apply card_reserveCompanionEdges
    intro w hw
    exact (mem_outerExtensionCandidates_iff.mp hw).2.2.1
  have hmono : ∀ bits,
      (s(u, v) ∈
          reserveProtectedOuterEdges G U (reserveEdges G U bits) ∧
        ¬ PairAlive s(u, v).toFinset
          (relativePreliminaryInitialState P
            (reserveProtectedOuterAvailable G U
              (reserveEdges G U bits) A))) →
      C ⊆ reserveEdges G U bits := by
    intro bits hbad e heC
    obtain ⟨w, hwS, he⟩ := mem_image.mp heC
    subst e
    have hwdata := mem_outerExtensionCandidates_iff.mp hwS
    by_contra hnotReserve
    have huvFalse : bits s(u, v) = false := by
      cases hbit : bits s(u, v)
      · rfl
      · exact (mem_sdiff.mp hbad.1).2
          (mem_reserveEdges_iff.mpr ⟨huvCross, hbit⟩) |>.elim
    have huwCross : s(u, w) ∈ crossingEdges G U := hCcross (by
      exact mem_image.mpr ⟨w, hwS, rfl⟩)
    have huwFalse : bits s(u, w) = false := by
      cases hbit : bits s(u, w)
      · rfl
      · exact (hnotReserve
          (mem_reserveEdges_iff.mpr ⟨huwCross, hbit⟩)).elim
    let T : TripleOn V := thirdVertexTriple huv
      ⟨w, hwdata.2.2.1, hwdata.2.2.2⟩
    have hT : T ∈ reserveProtectedOuterAvailable G U
        (reserveEdges G U bits) A := by
      exact thirdVertexTriple_mem_reserveProtectedOuterAvailable_of_left_inside
        htri huv hwdata.2.2.1.symm hwdata.2.2.2.symm hu hv
          hwdata.2.1 hwdata.1 huvFalse huwFalse
    apply hbad.2
    refine ⟨T, mem_availableTrianglesContainingPair_iff.mpr ⟨?_, ?_⟩⟩
    · simpa only [relativePreliminaryInitialState_available] using hT
    · intro x hx
      have hx' : x = u ∨ x = v := by
        simpa only [Sym2.toFinset_mk_eq, mem_insert, mem_singleton] using hx
      rcases hx' with rfl | rfl <;>
        simp [T, thirdVertexTriple, tripleOfThree]
  calc
    L.probability (fun bits ↦
        s(u, v) ∈ reserveProtectedOuterEdges G U
          (reserveEdges G U bits) ∧
        ¬ PairAlive s(u, v).toFinset
          (relativePreliminaryInitialState P
            (reserveProtectedOuterAvailable G U
              (reserveEdges G U bits) A))) ≤
        L.probability (fun bits ↦ C ⊆ reserveEdges G U bits) :=
      L.probability_mono hmono
    _ = r ^ C.card := by
      exact reserveEdgeLaw_probability_subset_reserveEdges
        G U r hr C hCcross
    _ = r ^ S.card := by rw [hCcard]
    _ ≤ r ^ m := pow_le_pow_right_of_le_one' hr (by
      simpa only [S] using hm)

/-- Symmetric fixed-crossing-edge form of the preceding estimate. -/
theorem reserveEdgeLaw_probability_not_pairAlive_crossing_le
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (A P : TripleSystemOn V)
    (Uouter U : Finset V) (u v : V)
    (htri : ConsistsOfTriangles G A) (huv : u ≠ v)
    (huvCross : s(u, v) ∈ crossingEdges G U)
    (r : ℝ≥0) (hr : r ≤ 1) (m : ℕ)
    (hm : m ≤ (outerExtensionCandidates A Uouter U u v).card) :
    (reserveEdgeLaw G U r hr).probability (fun bits ↦
        s(u, v) ∈ reserveProtectedOuterEdges G U (reserveEdges G U bits) ∧
          ¬ PairAlive s(u, v).toFinset
            (relativePreliminaryInitialState P
              (reserveProtectedOuterAvailable G U
                (reserveEdges G U bits) A))) ≤
      r ^ m := by
  rcases isCrossingEdge_mk_iff.mp
      (mem_crossingEdges_iff.mp huvCross).2 with hcross | hcross
  · exact reserveEdgeLaw_probability_not_pairAlive_left_inside_le
      G A P Uouter U u v htri huv hcross.1 hcross.2 huvCross r hr m hm
  · have hm' : m ≤
        (outerExtensionCandidates A Uouter U v u).card := by
      rw [← outerExtensionCandidates_comm]
      exact hm
    have hbound := reserveEdgeLaw_probability_not_pairAlive_left_inside_le
      G A P Uouter U v u htri huv.symm hcross.1 hcross.2
        (by simpa only [Sym2.eq_swap] using huvCross) r hr m hm'
    simpa only [Sym2.eq_swap] using hbound

/-- A wholly outside available triangle uses no sampled crossing edge and
hence remains in the reserve-protected preliminary family. -/
lemma outerOnlyAvailable_subset_reserveProtectedOuterAvailable
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {A : TripleSystemOn V}
    (htri : ConsistsOfTriangles G A) (bits : Sym2 V → Bool) :
    outerOnlyAvailable U A ⊆
      reserveProtectedOuterAvailable G U (reserveEdges G U bits) A := by
  intro T hT
  have hTdata := mem_outerOnlyAvailable_iff.mp hT
  rw [mem_reserveProtectedOuterAvailable_iff]
  refine ⟨hTdata.1, ?_⟩
  intro e heT
  induction e using Sym2.inductionOn with
  | _ u v =>
      have huvT := mk_mem_tripleEdgeFinset_iff.mp heT
      have huout : u ∉ U := by
        exact fun hu ↦ Finset.disjoint_left.mp hTdata.2 huvT.1 hu
      have hvout : v ∉ U := by
        exact fun hv ↦ Finset.disjoint_left.mp hTdata.2 huvT.2.1 hv
      rw [reserveProtectedOuterEdges, mem_sdiff,
        mem_outerGraphEdges_iff]
      refine ⟨⟨mem_graphEdges_iff.mpr
        (htri T hTdata.1 u huvT.1 v huvT.2.1 huvT.2.2), ?_⟩, ?_⟩
      · intro hsub
        exact huout (hsub (by simp))
      · intro heReserve
        have hcross := isCrossingEdge_mk_iff.mp
          (mem_crossingEdges_iff.mp
            (reserveEdges_subset_crossingEdges G U bits heReserve)).2
        aesop

/-- The usual iteration-typical extension window supplies a uniform lower
bound on the completely outside candidates through every current graph
edge. -/
lemma IsIterationTypical.outerExtensionCandidates_card_gt
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (m : ℕ)
    (hgap : ((((W.U i.succ).card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    {e : Sym2 V} (he : e ∈ graphEdges G) :
    m < (outerExtensionCandidates A (W.U i.castSucc)
      (W.U i.succ) e.out.1 e.out.2).card := by
  let u := e.out.1
  let v := e.out.2
  have huv : u ≠ v := out_fst_ne_snd_of_mem_graphEdges he
  have hadj : G.Adj u v := graph_adj_out_of_mem_graphEdges he
  have hsupp := hGsupp hadj
  have hwindow := htyp.2 i hstage i.castSucc (Or.inl rfl)
    (SimpleGraph.edge u v)
    (SimpleGraph.edge_le_iff G |>.mpr (Or.inr hadj))
    (edge_graphSupportedOn hsupp.1 hsupp.2) (by
      rw [graphSupportFinset_edge huv, card_pair huv]
      exact hh)
  rw [graphSupportFinset_edge huv, card_pair huv,
    graphEdges_edge huv, card_singleton, pow_one] at hwindow
  have hcard : (W.U i.succ).card + 2 + m <
      (iterationExtensionVertices A (SimpleGraph.edge u v)
        (W.U i.castSucc)).card := by
    exact_mod_cast hgap.trans_le hwindow.1
  exact card_outerExtensionCandidates_gt m hcard

/-- An outer graph edge which is not crossing has both endpoints outside. -/
lemma mem_internalOuterEdges_of_mem_outerGraphEdges_of_not_crossing
    {V : Type*} [Fintype V] [DecidableEq V]
    {G : SimpleGraph V} {U : Finset V} {e : Sym2 V}
    (he : e ∈ outerGraphEdges G U) (hnot : e ∉ crossingEdges G U) :
    e ∈ internalOuterEdges G U := by
  have hedata := mem_outerGraphEdges_iff.mp he
  have hnotCases : ¬((e.out.1 ∈ U ∧ e.out.2 ∉ U) ∨
      (e.out.2 ∈ U ∧ e.out.1 ∉ U)) := by
    intro hcases
    apply hnot
    rw [mem_crossingEdges_iff]
    refine ⟨mem_graphEdges_iff.mp hedata.1, ?_⟩
    rw [← e.out_eq, isCrossingEdge_mk_iff]
    exact hcases
  have hout : e.out.1 ∉ U ∧ e.out.2 ∉ U := by
    by_contra hbad
    push Not at hbad
    by_cases hu : e.out.1 ∈ U
    · by_cases hv : e.out.2 ∈ U
      · exact hedata.2 (by
          intro x hx
          have hx' := Sym2.mem_toFinset.mp hx
          have hxpair : x ∈ s(e.out.1, e.out.2) := by
            simpa only [e.out_eq] using hx'
          rcases Sym2.mem_iff.mp hxpair with rfl | rfl
          · exact hu
          · exact hv)
      · exact hnotCases (Or.inl ⟨hu, hv⟩)
    · have hv : e.out.2 ∈ U := hbad hu
      exact hnotCases (Or.inr ⟨hv, hu⟩)
  exact mem_internalOuterEdges_iff.mpr ⟨hedata.1, hout⟩

/-- Every edge left in the protected preliminary graph has a live initial
pair star. -/
def ReserveProtectedPairAliveGood
    {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) (U : Finset V) (A P : TripleSystemOn V)
    (bits : Sym2 V → Bool) : Prop :=
  ∀ e ∈ reserveProtectedOuterEdges G U (reserveEdges G U bits),
    PairAlive e.toFinset
      (relativePreliminaryInitialState P
        (reserveProtectedOuterAvailable G U (reserveEdges G U bits) A))

/-- Uniform failure bound for protected-pair survival.  The power `r^m`
comes from the `m` distinct companion crossing edges of one failed pair; the
outer-edge factor is the finite union bound. -/
theorem IsIterationTypical.reserveEdgeLaw_probability_not_reserveProtectedPairAliveGood_le
    {V : Type*} [Fintype V] [DecidableEq V]
    {ell : ℕ} {W : Vortex V ell} {stage : Fin (ell + 1)}
    {G : SimpleGraph V} {A P : TripleSystemOn V}
    {p eta xi : ℝ≥0} {h : ℕ}
    (htyp : IsIterationTypical W stage G A p eta xi h)
    (htri : ConsistsOfTriangles G A)
    (i : Fin ell) (hstage : stage.val ≤ i.val)
    (hGsupp : GraphSupportedOn G (W.U i.castSucc : Set V))
    (hh : 2 ≤ h) (m : ℕ)
    (hgap : ((((W.U i.succ).card + 2 + m : ℕ) : ℝ≥0)) <
      (1 - xi) * (p ^ 2 * eta * (W.U i.castSucc).card))
    (r : ℝ≥0) (hr : r ≤ 1) :
    (reserveEdgeLaw G (W.U i.succ) r hr).probability
        (fun bits ↦ ¬ ReserveProtectedPairAliveGood G (W.U i.succ)
          A P bits) ≤
      ((outerGraphEdges G (W.U i.succ)).card : ℝ≥0) * r ^ m := by
  let U := W.U i.succ
  let Uouter := W.U i.castSucc
  let L := reserveEdgeLaw G U r hr
  let Bad : Sym2 V → (Sym2 V → Bool) → Prop := fun e bits ↦
    e ∈ reserveProtectedOuterEdges G U (reserveEdges G U bits) ∧
      ¬ PairAlive e.toFinset
        (relativePreliminaryInitialState P
          (reserveProtectedOuterAvailable G U (reserveEdges G U bits) A))
  have hreduce : L.probability
      (fun bits ↦ ¬ ReserveProtectedPairAliveGood G U A P bits) ≤
      L.probability (fun bits ↦
        ∃ e ∈ outerGraphEdges G U, Bad e bits) := by
    apply L.probability_mono
    intro bits hbad
    simp only [ReserveProtectedPairAliveGood] at hbad
    push Not at hbad
    obtain ⟨e, heProtected, heNotAlive⟩ := hbad
    exact ⟨e, (mem_sdiff.mp heProtected).1, heProtected, heNotAlive⟩
  have hedge : ∀ e ∈ outerGraphEdges G U,
      L.probability (Bad e) ≤ r ^ m := by
    intro e heOuter
    by_cases heCross : e ∈ crossingEdges G U
    · have heGraph := (mem_outerGraphEdges_iff.mp heOuter).1
      have hmcand : m ≤
          (outerExtensionCandidates A Uouter U e.out.1 e.out.2).card := by
        exact Nat.le_of_lt (htyp.outerExtensionCandidates_card_gt i hstage
          hGsupp hh m (by simpa only [U, Uouter] using hgap) heGraph)
      have hbound := reserveEdgeLaw_probability_not_pairAlive_crossing_le
        G A P Uouter U e.out.1 e.out.2 htri
          (out_fst_ne_snd_of_mem_graphEdges heGraph)
          (by simpa only [e.out_eq] using heCross) r hr m hmcand
      simpa only [Bad, L, e.out_eq] using hbound
    · have heInternal :=
        mem_internalOuterEdges_of_mem_outerGraphEdges_of_not_crossing
          heOuter heCross
      have hgap₀ : (((U.card + 2 : ℕ) : ℝ≥0)) <
          (1 - xi) * (p ^ 2 * eta * Uouter.card) := by
        have hle : (((U.card + 2 : ℕ) : ℝ≥0)) ≤
            (((U.card + 2 + m : ℕ) : ℝ≥0)) := by
          exact_mod_cast (show U.card + 2 ≤ U.card + 2 + m by omega)
        exact hle.trans_lt (by simpa only [U, Uouter] using hgap)
      have haliveOuter := htyp.internalOuter_pairAlive_outerOnly i hstage
        hGsupp hh (by simpa only [U, Uouter] using hgap₀) P heInternal
      have halive : ∀ bits, PairAlive e.toFinset
          (relativePreliminaryInitialState P
            (reserveProtectedOuterAvailable G U
              (reserveEdges G U bits) A)) := by
        intro bits
        apply haliveOuter.of_available_subset
        exact outerOnlyAvailable_subset_reserveProtectedOuterAvailable
          htri bits
      calc
        L.probability (Bad e) ≤ L.probability (fun _ ↦ False) := by
          apply L.probability_mono
          intro bits hbad
          exact hbad.2 (halive bits)
        _ = 0 := L.probability_false
        _ ≤ r ^ m := zero_le
  calc
    L.probability
        (fun bits ↦ ¬ ReserveProtectedPairAliveGood G U A P bits) ≤
        L.probability (fun bits ↦
          ∃ e ∈ outerGraphEdges G U, Bad e bits) := hreduce
    _ ≤ ∑ e ∈ outerGraphEdges G U, L.probability (Bad e) :=
      L.probability_exists_le (outerGraphEdges G U) Bad
    _ ≤ ∑ _e ∈ outerGraphEdges G U, r ^ m := by
      apply sum_le_sum
      intro e he
      exact hedge e he
    _ = ((outerGraphEdges G U).card : ℝ≥0) * r ^ m := by simp
    _ = ((outerGraphEdges G (W.U i.succ)).card : ℝ≥0) * r ^ m := by
      rfl

end

end Erdos207
