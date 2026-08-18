/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos570.SparseDegree
import Mathlib.Combinatorics.SimpleGraph.Ends.Defs

/-!
# Degree-two components in a sparse connected target

The vertices outside `sparseCoreVertices` all have degree two.  This file
packages their components, attaches every such component to the core, and
turns a component into a suspended path.  The resulting cardinal estimate
is the contraction step in the classical sparse-target lemma.
-/

open scoped SimpleGraph

noncomputable section

namespace Erdos570

open Erdos79

abbrev DegreeTwoComponent (H : GraphCode) [DecidableRel H.graph.Adj] :=
  H.graph.ComponentCompl (sparseCoreVertices H : Set (Fin H.vertexCount))

noncomputable instance degreeTwoComponentFintype
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) :
    Fintype C :=
  @Subtype.fintype (Fin H.vertexCount)
    (fun v ↦ v ∈ (C : Set (Fin H.vertexCount)))
    (Classical.decPred _) (inferInstance : Fintype (Fin H.vertexCount))

theorem degreeTwoComponent_mem_degreeTwo
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) (v : Fin H.vertexCount) (hv : v ∈ C) :
    H.graph.degree v = 2 := by
  have hvnot : v ∉ (sparseCoreVertices H : Set (Fin H.vertexCount)) :=
    C.notMem_of_mem hv
  simpa using (not_not.mp (by simpa using hvnot))

/-- The canonical nested-subtype vertex belonging to a degree-two
component. -/
def degreeTwoComponentVertex
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) (v : Fin H.vertexCount) (hv : v ∈ C) :
    C :=
  ⟨v, hv⟩

def degreeTwoComponentEquiv
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) :
    SimpleGraph.ConnectedComponent.supp C ≃ C where
  toFun z := ⟨z.1.1, ⟨z.1.2,
    (SimpleGraph.ConnectedComponent.mem_supp_iff C z.1).mp z.2⟩⟩
  invFun z := ⟨⟨z.1, z.2.choose⟩,
    (SimpleGraph.ConnectedComponent.mem_supp_iff C
      ⟨z.1, z.2.choose⟩).mpr z.2.choose_spec⟩
  left_inv z := by apply Subtype.ext; apply Subtype.ext; rfl
  right_inv z := by apply Subtype.ext; rfl

def degreeTwoComponentIso
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) : C.toSimpleGraph ≃g C.coeGraph where
  toEquiv := degreeTwoComponentEquiv H C
  map_rel_iff' := by
    intro u v
    simp [degreeTwoComponentEquiv, SimpleGraph.ComponentCompl.coeGraph,
      SimpleGraph.ConnectedComponent.toSimpleGraph]

theorem degreeTwoComponent_connected
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) : C.coeGraph.Connected := by
  exact (degreeTwoComponentIso H C).connected_iff.mp C.connected_toSimpleGraph

theorem degree_degreeTwoComponent_le_two
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (C : DegreeTwoComponent H) (v : C) :
    C.coeGraph.degree v ≤ 2 := by
  classical
  have hle : C.coeGraph.degree v ≤ H.graph.degree v :=
    degree_induce_le (G := H.graph) (S := (C : Set (Fin H.vertexCount))) v
  exact hle.trans_eq (degreeTwoComponent_mem_degreeTwo H C v.1 v.2)

/-- Every component outside the core has a selected edge to the core. -/
def degreeTwoAttachment
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty)
    (C : DegreeTwoComponent H) : Fin H.vertexCount × Fin H.vertexCount :=
  (C.exists_adj_boundary_pair hconn.preconnected
    (by simpa using hcore)).choose

theorem degreeTwoAttachment_spec
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty)
    (C : DegreeTwoComponent H) :
    (degreeTwoAttachment H hconn hcore C).1 ∈ C ∧
      (degreeTwoAttachment H hconn hcore C).2 ∈ sparseCoreVertices H ∧
      H.graph.Adj (degreeTwoAttachment H hconn hcore C).1
        (degreeTwoAttachment H hconn hcore C).2 := by
  exact (C.exists_adj_boundary_pair hconn.preconnected
    (by simpa using hcore)).choose_spec

theorem degree_degreeTwoComponent_start_le_one
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty)
    (C : DegreeTwoComponent H) :
    C.coeGraph.degree
      (degreeTwoComponentVertex H C (degreeTwoAttachment H hconn hcore C).1
        (degreeTwoAttachment_spec H hconn hcore C).1) ≤ 1 := by
  classical
  let x := (degreeTwoAttachment H hconn hcore C).1
  let a := (degreeTwoAttachment H hconn hcore C).2
  have hxa : H.graph.Adj x a :=
    (degreeTwoAttachment_spec H hconn hcore C).2.2
  have hxdeg : H.graph.degree x = 2 :=
    degreeTwoComponent_mem_degreeTwo H C x
      (degreeTwoAttachment_spec H hconn hcore C).1
  let xC : C :=
    degreeTwoComponentVertex H C x
    (degreeTwoAttachment_spec H hconn hcore C).1
  have ha_not : a ∉ C := by
    intro haC
    exact (C.notMem_of_mem haC)
      (degreeTwoAttachment_spec H hconn hcore C).2.1
  let emb : C ↪ Fin H.vertexCount := Function.Embedding.subtype (· ∈ C)
  have hmap : (C.coeGraph.neighborFinset xC).map emb ⊆
      (H.graph.neighborFinset x).erase a := by
    intro y hy
    rw [Finset.mem_map] at hy
    obtain ⟨z, hz, rfl⟩ := hy
    rw [Finset.mem_erase]
    constructor
    · intro heq
      apply ha_not
      exact heq ▸ z.2
    · rw [H.graph.mem_neighborFinset]
      rw [C.coeGraph.mem_neighborFinset] at hz
      exact hz
  have hcard := Finset.card_le_card hmap
  rw [Finset.card_map] at hcard
  change C.coeGraph.degree xC ≤ _ at hcard
  have ha_mem : a ∈ H.graph.neighborFinset x := by
    rw [H.graph.mem_neighborFinset]
    exact hxa
  rw [Finset.card_erase_of_mem ha_mem,
    H.graph.card_neighborFinset_eq_degree, hxdeg] at hcard
  simpa [xC] using hcard

/-- A degree-two component, preceded by its selected core attachment, is a
suspended path in the original graph. -/
theorem exists_suspendedPath_of_degreeTwoComponent
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty)
    (C : DegreeTwoComponent H) :
    ∃ t : ℕ, Fintype.card C = t + 1 ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount,
        IsSuspendedPath H.graph p := by
  classical
  let x := (degreeTwoAttachment H hconn hcore C).1
  let a := (degreeTwoAttachment H hconn hcore C).2
  let xC : C :=
    degreeTwoComponentVertex H C x
    (degreeTwoAttachment_spec H hconn hcore C).1
  obtain ⟨q, hqbij, hqpath, hqzero⟩ :=
    exists_bijective_indexedPath_start (degreeTwoComponent_connected H C) xC
      (degree_degreeTwoComponent_start_le_one H hconn hcore C)
      (degree_degreeTwoComponent_le_two H C)
  have hCpos : 0 < Fintype.card C := by
    rw [Fintype.card_pos_iff]
    exact ⟨degreeTwoComponentVertex H C x
      (degreeTwoAttachment_spec H hconn hcore C).1⟩
  let t := Fintype.card C - 1
  have hCt : Fintype.card C = t + 1 := by
    dsimp only [t]
    omega
  let q' : Fin (t + 1) → C :=
    fun i ↦ q (Fin.cast hCt.symm i)
  have hq'bij : Function.Bijective q' := by
    apply hqbij.comp
    constructor
    · exact Fin.cast_injective hCt.symm
    · intro j
      refine ⟨Fin.cast hCt j, ?_⟩
      apply Fin.ext
      rfl
  have hq'path : IsIndexedPath C.coeGraph q' := by
    constructor
    · exact hq'bij.1
    · intro i j hij
      apply hqpath.adj
      simpa [q'] using hij
  have hq'zero : ∀ i : Fin (t + 1), i.val = 0 → q' i = xC := by
    intro i hi
    apply hqzero
    simpa [q'] using hi
  let tail : Fin (t + 1) → Fin H.vertexCount := fun i ↦ (q' i).1
  let p : Fin (t + 2) → Fin H.vertexCount :=
    Fin.cases a tail
  refine ⟨t, hCt, p, ?_⟩
  constructor
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => rfl
        | succ j =>
            exfalso
            have hjcore : tail j ∉ sparseCoreVertices H := by
              change (q' j).1 ∉ sparseCoreVertices H
              exact C.notMem_of_mem (q' j).2
            have haj : a = (q' j).1 := by simpa [p, tail] using hij
            apply hjcore
            change (q' j).1 ∈ sparseCoreVertices H
            rw [← haj]
            exact (degreeTwoAttachment_spec H hconn hcore C).2.1
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            exfalso
            have hicore : tail i ∉ sparseCoreVertices H := by
              change (q' i).1 ∉ sparseCoreVertices H
              exact C.notMem_of_mem (q' i).2
            have hia : (q' i).1 = a := by simpa [p, tail] using hij
            apply hicore
            change (q' i).1 ∈ sparseCoreVertices H
            rw [hia]
            exact (degreeTwoAttachment_spec H hconn hcore C).2.1
        | succ j =>
            apply congrArg Fin.succ
            apply hq'bij.1
            apply Subtype.ext
            simpa [p, tail] using hij
  · intro i j hij
    cases i using Fin.cases with
    | zero =>
        cases j using Fin.cases with
        | zero => omega
        | succ j =>
            have hjzero : j.val = 0 := by simpa using hij
            have hqj : q' j = xC := hq'zero j hjzero
            simpa [p, tail, a, x, xC, hqj, degreeTwoComponentVertex] using
              (degreeTwoAttachment_spec H hconn hcore C).2.2.symm
    | succ i =>
        cases j using Fin.cases with
        | zero =>
            simp only [Fin.val_succ, Fin.val_zero] at hij
            omega
        | succ j =>
            exact hq'path.adj i j (by simpa using hij)
  · intro i
    change H.graph.degree (q' ⟨i.val, by omega⟩).1 = 2
    exact degreeTwoComponent_mem_degreeTwo H C _ (q' ⟨i.val, by omega⟩).2

/-- A core vertex together with one incident neighbor. -/
abbrev SparseCoreIncidence
    (H : GraphCode) [DecidableRel H.graph.Adj] :=
  Σ a : {a // a ∈ sparseCoreVertices H},
    {x // x ∈ H.graph.neighborFinset a.1}

def degreeTwoAttachmentIncidence
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty)
    (C : DegreeTwoComponent H) : SparseCoreIncidence H :=
  ⟨⟨(degreeTwoAttachment H hconn hcore C).2,
      (degreeTwoAttachment_spec H hconn hcore C).2.1⟩,
    ⟨(degreeTwoAttachment H hconn hcore C).1, by
      rw [H.graph.mem_neighborFinset]
      exact (degreeTwoAttachment_spec H hconn hcore C).2.2.symm⟩⟩

theorem degreeTwoAttachmentIncidence_injective
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty) :
    Function.Injective (degreeTwoAttachmentIncidence H hconn hcore) := by
  intro C D hCD
  have hx : (degreeTwoAttachment H hconn hcore C).1 =
      (degreeTwoAttachment H hconn hcore D).1 := by
    exact congrArg (fun z : SparseCoreIncidence H ↦ z.2.1) hCD
  have hxC := (degreeTwoAttachment_spec H hconn hcore C).1
  have hxD := (degreeTwoAttachment_spec H hconn hcore D).1
  rcases hxC with ⟨hxnotC, hxcompC⟩
  rcases hxD with ⟨hxnotD, hxcompD⟩
  let xC : {v : Fin H.vertexCount //
      v ∈ (sparseCoreVertices H : Set (Fin H.vertexCount))ᶜ} :=
    ⟨(degreeTwoAttachment H hconn hcore C).1, hxnotC⟩
  let xD : {v : Fin H.vertexCount //
      v ∈ (sparseCoreVertices H : Set (Fin H.vertexCount))ᶜ} :=
    ⟨(degreeTwoAttachment H hconn hcore D).1, hxnotD⟩
  have hsub : xC = xD := Subtype.ext hx
  have hmk : H.graph.componentComplMk hxnotC =
      H.graph.componentComplMk hxnotD := by
    exact congrArg
      (SimpleGraph.connectedComponentMk
        (H.graph.induce ((sparseCoreVertices H : Set _)ᶜ))) hsub
  exact hxcompC.symm.trans (hmk.trans hxcompD)

theorem card_sparseCoreIncidence
    (H : GraphCode) [DecidableRel H.graph.Adj] :
    Fintype.card (SparseCoreIncidence H) =
      ∑ v ∈ sparseCoreVertices H, H.graph.degree v := by
  classical
  rw [Fintype.card_sigma]
  simp only [Fintype.card_coe, H.graph.card_neighborFinset_eq_degree]
  exact (Finset.sum_subtype (sparseCoreVertices H)
    (fun _ ↦ Iff.rfl) (fun v ↦ H.graph.degree v)).symm

theorem degreeTwoComponent_card_le_sum_core_degree
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty) :
    Fintype.card (DegreeTwoComponent H) ≤
      ∑ v ∈ sparseCoreVertices H, H.graph.degree v := by
  rw [← card_sparseCoreIncidence H]
  exact Fintype.card_le_of_injective _
    (degreeTwoAttachmentIncidence_injective H hconn hcore)

/-- The degree-two vertices are the disjoint union of their components. -/
def degreeTwoVertexComponentEquiv
    (H : GraphCode) [DecidableRel H.graph.Adj] :
    {v // v ∈ degreeTwoVertices H} ≃
      Σ C : DegreeTwoComponent H, C := by
  classical
  let notCore (v : {v // v ∈ degreeTwoVertices H}) :
      v.1 ∉ (sparseCoreVertices H : Set (Fin H.vertexCount)) := by
    intro hvcore
    have hvne : H.graph.degree v.1 ≠ 2 :=
      (mem_sparseCoreVertices H v.1).mp hvcore
    exact hvne ((mem_degreeTwoVertices H v.1).mp v.2)
  let toComp (v : {v // v ∈ degreeTwoVertices H}) :
      DegreeTwoComponent H :=
    H.graph.componentComplMk (K := (sparseCoreVertices H : Set _))
      (notCore v)
  let toFun (v : {v // v ∈ degreeTwoVertices H}) :
      Σ C : DegreeTwoComponent H, C :=
    ⟨toComp v, ⟨v.1, H.graph.componentComplMk_mem (notCore v)⟩⟩
  let invFun (z : Σ C : DegreeTwoComponent H, C) :
      {v // v ∈ degreeTwoVertices H} :=
    ⟨z.2.1, by
      rw [mem_degreeTwoVertices]
      exact degreeTwoComponent_mem_degreeTwo H z.1 z.2.1 z.2.2⟩
  exact
    { toFun := toFun
      invFun := invFun
      left_inv := by intro v; apply Subtype.ext; rfl
      right_inv := by
        rintro ⟨C, ⟨v, hv⟩⟩
        rcases hv with ⟨hvnot, hvcomp⟩
        subst C
        rfl }

theorem degreeTwo_card_eq_sum_component_card
    (H : GraphCode) [DecidableRel H.graph.Adj] :
    (degreeTwoVertices H).card =
      ∑ C : DegreeTwoComponent H, Fintype.card C := by
  classical
  rw [← Fintype.card_coe]
  exact Fintype.card_congr (degreeTwoVertexComponentEquiv H) |>.trans
    Fintype.card_sigma

theorem degreeTwo_card_le_of_component_card_le
    (H : GraphCode) [DecidableRel H.graph.Adj] {L : ℕ}
    (hcard : ∀ C : DegreeTwoComponent H, Fintype.card C ≤ L) :
    (degreeTwoVertices H).card ≤
      L * Fintype.card (DegreeTwoComponent H) := by
  rw [degreeTwo_card_eq_sum_component_card H]
  calc
    ∑ C : DegreeTwoComponent H, Fintype.card C ≤
        ∑ _C : DegreeTwoComponent H, L :=
      Finset.sum_le_sum fun C _ ↦ hcard C
    _ = L * Fintype.card (DegreeTwoComponent H) := by simp [mul_comm]

/-- Quantitative contraction dichotomy when the sparse core is nonempty. -/
theorem long_suspendedPath_or_degreeTwo_card_le
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty) (L : ℕ) :
    (∃ t : ℕ, L ≤ t ∧ ∃ p : Fin (t + 2) → Fin H.vertexCount,
      IsSuspendedPath H.graph p) ∨
      (degreeTwoVertices H).card ≤
        L * (∑ v ∈ sparseCoreVertices H, H.graph.degree v) := by
  classical
  by_cases hlong : ∃ t : ℕ, L ≤ t ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount, IsSuspendedPath H.graph p
  · exact Or.inl hlong
  · right
    have hcomponent : ∀ C : DegreeTwoComponent H, Fintype.card C ≤ L := by
      intro C
      obtain ⟨t, hCt, p, hp⟩ :=
        exists_suspendedPath_of_degreeTwoComponent H hconn hcore C
      have ht : t < L := by
        by_contra hnot
        exact hlong ⟨t, Nat.le_of_not_gt hnot, p, hp⟩
      omega
    exact (degreeTwo_card_le_of_component_card_le H hcomponent).trans
      (Nat.mul_le_mul_left L
        (degreeTwoComponent_card_le_sum_core_degree H hconn hcore))

/-- The contraction estimate in a deliberately relaxed integral form. -/
theorem long_suspendedPath_or_sparse_vertex_bound_of_core
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hcore : (sparseCoreVertices H).Nonempty) (L : ℕ) :
    (∃ t : ℕ, L ≤ t ∧ ∃ p : Fin (t + 2) → Fin H.vertexCount,
      IsSuspendedPath H.graph p) ∨
      H.vertexCount ≤
        (4 * L + 2) * (leafVertices H).card +
          (6 * L + 2) * sparseExcess H := by
  rcases long_suspendedPath_or_degreeTwo_card_le H hconn hcore L with
    hlong | htwo
  · exact Or.inl hlong
  · right
    have hsum := sum_degree_sparseCore_le H hH hconn
    have hcoreCard := sparseCore_card_le H hH hconn
    have hsplit := degreeTwo_card_add_core_card H
    nlinarith

/-- If the sparse core is empty, every vertex has degree two.  A spanning
tree therefore has maximum degree two, hence is a Hamilton path; in the
ambient graph this is a spanning suspended path. -/
theorem exists_spanning_suspendedPath_of_core_empty
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected)
    (hcore : sparseCoreVertices H = ∅) :
    ∃ t : ℕ, H.vertexCount = t + 2 ∧
      ∃ p : Fin (t + 2) → Fin H.vertexCount,
        IsSuspendedPath H.graph p := by
  classical
  have hdeg : ∀ v : Fin H.vertexCount, H.graph.degree v = 2 := by
    intro v
    by_contra hv
    have hvcore : v ∈ sparseCoreVertices H :=
      (mem_sparseCoreVertices H v).mpr hv
    rw [hcore] at hvcore
    simp at hvcore
  let v : Fin H.vertexCount := Classical.choice hconn.nonempty
  obtain ⟨w, hvw⟩ := H.graph.exists_adj_iff_not_isIsolated.mpr (hH v)
  letI : Nontrivial (Fin H.vertexCount) := ⟨⟨v, w, hvw.ne⟩⟩
  obtain ⟨T, hTH, hTtree⟩ := hconn.exists_isTree_le
  letI : DecidableRel T.Adj := Classical.decRel _
  obtain ⟨s, hs⟩ := hTtree.exists_vert_degree_one_of_nontrivial
  have hTdeg : ∀ x : Fin H.vertexCount, T.degree x ≤ 2 := by
    intro x
    have hle : T.degree x ≤ H.graph.degree x := by
      change (T.neighborFinset x).card ≤ (H.graph.neighborFinset x).card
      apply Finset.card_le_card
      intro y hy
      rw [T.mem_neighborFinset] at hy
      rw [H.graph.mem_neighborFinset]
      exact hTH hy
    exact hle.trans_eq (hdeg x)
  obtain ⟨q, hqbij, hqpath, -⟩ :=
    exists_bijective_indexedPath_start hTtree.connected s hs.le hTdeg
  have hn : 2 ≤ H.vertexCount := by
    have := Fintype.one_lt_card (α := Fin H.vertexCount)
    simp only [Fintype.card_fin] at this
    omega
  let t := H.vertexCount - 2
  have hnt : H.vertexCount = t + 2 := by
    dsimp only [t]
    omega
  have hntCard : Fintype.card (Fin H.vertexCount) = t + 2 := by
    simpa using hnt
  let p : Fin (t + 2) → Fin H.vertexCount :=
    fun i ↦ q (Fin.cast hntCard.symm i)
  refine ⟨t, hnt, p, ?_⟩
  constructor
  · exact hqbij.1.comp (Fin.cast_injective hntCard.symm)
  · intro i j hij
    apply hTH
    apply hqpath.adj
    simpa [p] using hij
  · intro i
    exact hdeg (p (suspendedMidIndex i))

/-- Full degree-contraction dichotomy, including the cycle-like case in
which every vertex has degree two. -/
theorem long_suspendedPath_or_sparse_vertex_bound
    (H : GraphCode) [DecidableRel H.graph.Adj]
    (hH : NoIsolated H) (hconn : H.graph.Connected) (L : ℕ) :
    (∃ t : ℕ, L ≤ t ∧ ∃ p : Fin (t + 2) → Fin H.vertexCount,
      IsSuspendedPath H.graph p) ∨
      H.vertexCount ≤
        (4 * L + 2) * (leafVertices H).card +
          (6 * L + 2) * sparseExcess H := by
  classical
  by_cases hcore : (sparseCoreVertices H).Nonempty
  · exact long_suspendedPath_or_sparse_vertex_bound_of_core
      H hH hconn hcore L
  · have hcoreEmpty : sparseCoreVertices H = ∅ :=
      Finset.not_nonempty_iff_eq_empty.mp hcore
    obtain ⟨t, hnt, p, hp⟩ :=
      exists_spanning_suspendedPath_of_core_empty H hH hconn hcoreEmpty
    by_cases ht : L ≤ t
    · exact Or.inl ⟨t, ht, p, hp⟩
    · right
      have hn : H.vertexCount ≤ L + 1 := by omega
      have hexcess : sparseExcess H = 1 := by
        have hsum : ∑ v : Fin H.vertexCount, H.graph.degree v =
            2 * H.edgeCount := by
          simpa [GraphCode.edgeCount_eq_card_edgeFinset] using
            H.graph.sum_degrees_eq_twice_card_edges
        have hdegree : ∑ v : Fin H.vertexCount, H.graph.degree v =
            2 * H.vertexCount := by simp_rw [show ∀ v, H.graph.degree v = 2 from
              fun v ↦ by
                have hvnot : v ∉ sparseCoreVertices H := by simp [hcoreEmpty]
                exact not_not.mp (by simpa using hvnot)]; simp [mul_comm]
        have hem : H.edgeCount = H.vertexCount := by omega
        unfold sparseExcess
        omega
      rw [hexcess]
      omega

end Erdos570
