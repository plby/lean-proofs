/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos73.MinorModels
import ErdosProblems.Erdos73.RootedModels
import Mathlib.Data.Finset.Max

/-!
# Connected partitions retaining prescribed distinct roots

The finite maximization argument used to normalize connected grill columns.
-/

namespace Erdos73

noncomputable section
attribute [local instance] Classical.propDecidable Classical.decEq

variable {V I : Type*} [Fintype V] [Fintype I] {G : SimpleGraph V}

theorem connected_induce_insert_of_adj {S : Finset V} {u v : V}
    (hS : (G.induce (S : Set V)).Connected) (hu : u ∈ S) (huv : G.Adj u v) :
    (G.induce (↑(insert v S) : Set V)).Connected := by
  have hv : (G.induce ({v} : Set V)).Connected := SimpleGraph.Connected.of_subsingleton
  have h := SimpleGraph.connected_induce_union hS.preconnected hv.preconnected hu
    (Set.mem_singleton v) huv
  have heq : (S : Set V) ∪ {v} = ↑(insert v S) := by
    ext x
    simp only [Set.mem_union, Finset.mem_coe, Set.mem_singleton_iff, Finset.mem_insert]
    tauto
  rwa [heq] at h

/-- Any finite nonempty family of disjoint nonempty connected sets in a
connected graph extends to a connected partition, retaining every initial set. -/
theorem exists_connected_partition_extending [Nonempty I]
    (hconn : G.Connected) (initial : I → Finset V)
    (hinit : ∀ i, (initial i).Nonempty ∧ (G.induce (initial i : Set V)).Connected)
    (hinit_disj : Pairwise fun i j ↦ Disjoint (initial i) (initial j)) :
    ∃ B : I → Finset V,
      (∀ i, initial i ⊆ B i ∧ (G.induce (B i : Set V)).Connected) ∧
      (Pairwise fun i j ↦ Disjoint (B i) (B j)) ∧
      ∀ v : V, ∃ i, v ∈ B i := by
  let valid : (I → Finset V) → Prop := fun B ↦
    (∀ i, initial i ⊆ B i ∧ (G.induce (B i : Set V)).Connected) ∧
      Pairwise fun i j ↦ Disjoint (B i) (B j)
  let covered (B : I → Finset V) : Finset V := Finset.univ.biUnion B
  let candidates := Finset.univ.filter valid
  have hinitial : valid initial :=
    ⟨fun i ↦ ⟨Finset.Subset.refl _, (hinit i).2⟩, hinit_disj⟩
  have hcand : candidates.Nonempty :=
    ⟨initial, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hinitial⟩⟩
  obtain ⟨B, hBmem, hmax⟩ := candidates.exists_max_image (fun B ↦ (covered B).card) hcand
  obtain ⟨hBroot, hBdisj⟩ := (Finset.mem_filter.mp hBmem).2
  refine ⟨B, hBroot, hBdisj, ?_⟩
  intro v
  by_contra hv
  have hvoutside : v ∉ covered B := by
    intro h
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h
    exact hv ⟨i, hi⟩
  let i₀ : I := Classical.choice inferInstance
  obtain ⟨x₀, hx₀⟩ := (hinit i₀).1
  have hroot : x₀ ∈ covered B := Finset.mem_biUnion.mpr
    ⟨i₀, Finset.mem_univ _, (hBroot i₀).1 hx₀⟩
  obtain ⟨W⟩ := hconn.preconnected x₀ v
  obtain ⟨e, _, hein, heout⟩ := W.exists_boundary_dart (covered B : Set V) hroot hvoutside
  obtain ⟨i, _, hei⟩ := Finset.mem_biUnion.mp hein
  let B' : I → Finset V := Function.update B i (insert e.snd (B i))
  have hB'i : B' i = insert e.snd (B i) := Function.update_self _ _ _
  have hB'j (j : I) (hji : j ≠ i) : B' j = B j := Function.update_of_ne hji _ _
  have hnot (j : I) : e.snd ∉ B j := fun h ↦ heout
    (Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, h⟩)
  have hB'valid : valid B' := by
    constructor
    · intro j
      by_cases hji : j = i
      · subst j
        rw [hB'i]
        exact ⟨(hBroot i).1.trans (Finset.subset_insert _ _),
          connected_induce_insert_of_adj (hBroot i).2 hei e.adj⟩
      · rw [hB'j j hji]
        exact hBroot j
    · intro j k hjk
      by_cases hji : j = i
      · subst j
        have hki : k ≠ i := hjk.symm
        rw [hB'i, hB'j k hki]
        exact Finset.disjoint_insert_left.mpr ⟨hnot k, hBdisj hjk⟩
      · by_cases hki : k = i
        · subst k
          rw [hB'i, hB'j j hji]
          exact Finset.disjoint_insert_right.mpr ⟨hnot j, hBdisj hjk⟩
        · rw [hB'j j hji, hB'j k hki]
          exact hBdisj hjk
  have hB'mem : B' ∈ candidates := Finset.mem_filter.mpr ⟨Finset.mem_univ _, hB'valid⟩
  have hcover : covered B ⊆ covered B' := by
    intro x hx
    obtain ⟨j, _, hj⟩ := Finset.mem_biUnion.mp hx
    refine Finset.mem_biUnion.mpr ⟨j, Finset.mem_univ _, ?_⟩
    by_cases hji : j = i
    · subst j
      rw [hB'i]
      exact Finset.mem_insert_of_mem hj
    · rw [hB'j j hji]
      exact hj
  have hnew : e.snd ∈ covered B' := by
    refine Finset.mem_biUnion.mpr ⟨i, Finset.mem_univ _, ?_⟩
    rw [hB'i]
    exact Finset.mem_insert_self _ _
  have hstrict : covered B ⊂ covered B' := Finset.ssubset_iff_subset_ne.mpr
    ⟨hcover, fun h ↦ heout (h.symm ▸ hnew)⟩
  exact (Finset.card_lt_card hstrict).not_ge (hmax B' hB'mem)

/-- Any finite nonempty family of distinct roots in a connected graph
extends to a partition into connected sets, one for each root. -/
theorem exists_connected_rooted_partition [Nonempty I]
    (hconn : G.Connected) (root : I → V) (hinj : Function.Injective root) :
    ∃ B : I → Finset V,
      (∀ i, root i ∈ B i ∧ (G.induce (B i : Set V)).Connected) ∧
      (Pairwise fun i j ↦ Disjoint (B i) (B j)) ∧
      ∀ v : V, ∃ i, v ∈ B i := by
  have hinit (i : I) : ({root i} : Finset V).Nonempty ∧
      (G.induce (↑({root i} : Finset V))).Connected := by
    refine ⟨Finset.singleton_nonempty _, ?_⟩
    rw [Finset.coe_singleton]
    exact SimpleGraph.Connected.of_subsingleton
  have hdisj : Pairwise fun i j ↦ Disjoint ({root i} : Finset V) {root j} :=
    fun _ _ hij ↦ Finset.disjoint_singleton.mpr (hinj.ne hij)
  obtain ⟨B, hB, hd, hc⟩ := exists_connected_partition_extending hconn
    (fun i ↦ {root i}) hinit hdisj
  exact ⟨B, fun i ↦ ⟨(hB i).1 (Finset.mem_singleton_self _), (hB i).2⟩, hd, hc⟩

/-- Restricting the ambient vertex type to a larger finite set preserves
connectedness of an induced subgraph on a contained set. -/
theorem connected_subtypeFinset {S K : Finset V} (hSK : S ⊆ K)
    (hS : (G.induce (S : Set V)).Connected) :
    ((G.induce (K : Set V)).induce
      (↑(Erdos73Infrastructure.SimpleGraph.PathPacking.subtypeFinset S K hSK) :
        Set {v : V // v ∈ K})).Connected := by
  let f : G.induce (S : Set V) →g (G.induce (K : Set V)).induce
      (↑(Erdos73Infrastructure.SimpleGraph.PathPacking.subtypeFinset S K hSK) :
        Set {v : V // v ∈ K}) := {
    toFun := fun v ↦ ⟨⟨v.1, hSK v.2⟩,
      (Erdos73Infrastructure.SimpleGraph.PathPacking.mem_subtypeFinset hSK _).mpr v.2⟩
    map_rel' := fun {_ _} h ↦ h }
  have hf : Function.Surjective f := by
    rintro ⟨⟨v, hvK⟩, hvS⟩
    have hv : v ∈ S :=
      (Erdos73Infrastructure.SimpleGraph.PathPacking.mem_subtypeFinset hSK _).mp hvS
    exact ⟨⟨v, hv⟩, rfl⟩
  exact hS.map f hf

/-- The connected partition extension can be performed wholly within a
specified connected finite region of the host graph. -/
theorem exists_connected_partition_inside [Nonempty I]
    (K : Finset V) (hK : (G.induce (K : Set V)).Connected)
    (initial : I → Finset V)
    (hinit : ∀ i, (initial i).Nonempty ∧ (G.induce (initial i : Set V)).Connected)
    (hsub : ∀ i, initial i ⊆ K)
    (hdisj : Pairwise fun i j ↦ Disjoint (initial i) (initial j)) :
    ∃ B : I → Finset V,
      (∀ i, initial i ⊆ B i ∧ B i ⊆ K ∧ (G.induce (B i : Set V)).Connected) ∧
      (Pairwise fun i j ↦ Disjoint (B i) (B j)) ∧
      ∀ v ∈ K, ∃ i, v ∈ B i := by
  let S (i : I) : Finset {v : V // v ∈ K} :=
    Erdos73Infrastructure.SimpleGraph.PathPacking.subtypeFinset (initial i) K (hsub i)
  have hmem (i : I) (v : {v : V // v ∈ K}) : v ∈ S i ↔ v.1 ∈ initial i :=
    Erdos73Infrastructure.SimpleGraph.PathPacking.mem_subtypeFinset (hsub i) v
  have hS (i : I) : (S i).Nonempty ∧
      ((G.induce (K : Set V)).induce (S i : Set {v : V // v ∈ K})).Connected := by
    obtain ⟨v, hv⟩ := (hinit i).1
    exact ⟨⟨⟨v, hsub i hv⟩, (hmem i _).mpr hv⟩,
      connected_subtypeFinset (hsub i) (hinit i).2⟩
  have hSdisj : Pairwise fun i j ↦ Disjoint (S i) (S j) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    exact Finset.disjoint_left.mp (hdisj hij) ((hmem i v).mp hvi) ((hmem j v).mp hvj)
  obtain ⟨B, hB, hBd, hBc⟩ := exists_connected_partition_extending hK S hS hSdisj
  let e : (G.induce (K : Set V)).Copy G := (SimpleGraph.Embedding.induce (G := G) (K : Set V)).toCopy
  refine ⟨fun i ↦ (B i).map e.toEmbedding, ?_, ?_, ?_⟩
  · intro i
    refine ⟨?_, ?_, Erdos73Infrastructure.SimpleGraph.connected_induce_map_copy e (B i) (hB i).2⟩
    · intro v hv
      exact Finset.mem_map.mpr ⟨⟨v, hsub i hv⟩, (hB i).1 ((hmem i _).mpr hv), rfl⟩
    · intro v hv
      obtain ⟨w, _, hwv⟩ := Finset.mem_map.mp hv
      exact hwv ▸ w.2
  · intro i j hij
    apply Finset.disjoint_left.mpr
    intro v hvi hvj
    obtain ⟨x, hx, hxv⟩ := Finset.mem_map.mp hvi
    obtain ⟨y, hy, hyv⟩ := Finset.mem_map.mp hvj
    have hxy := e.injective (hxv.trans hyv.symm)
    exact Finset.disjoint_left.mp (hBd hij) hx (hxy ▸ hy)
  · intro v hv
    obtain ⟨i, hi⟩ := hBc ⟨v, hv⟩
    exact ⟨i, Finset.mem_map.mpr ⟨⟨v, hv⟩, hi, rfl⟩⟩

/-- The quotient graph records precisely the edges between distinct
parts of a vertex partition. Edges internal to one part disappear. -/
def connectedPartitionGraph (G : SimpleGraph V) (B : I → Finset V) : SimpleGraph I where
  Adj i j := i ≠ j ∧ ∃ x ∈ B i, ∃ y ∈ B j, G.Adj x y
  symm := ⟨by
    rintro i j ⟨hij, x, hx, y, hy, hxy⟩
    exact ⟨hij.symm, y, hy, x, hx, hxy.symm⟩⟩
  loopless := ⟨by rintro i ⟨hii, _⟩; exact hii rfl⟩

/-- A connected host induces a connected quotient by a connected rooted
partition. The walk argument explicitly permits consecutive vertices
to lie in the same part; it does not assert a loop-preserving homomorphism. -/
theorem connectedPartitionGraph_connected [Nonempty I]
    (hconn : G.Connected) (root : I → V) (B : I → Finset V)
    (hroot : ∀ i, root i ∈ B i)
    (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hcover : ∀ v, ∃ i, v ∈ B i) : (connectedPartitionGraph G B).Connected := by
  choose owner howner using hcover
  have howner_eq {v : V} {i : I} (hv : v ∈ B i) : owner v = i := by
    by_contra h
    exact Finset.disjoint_left.mp (hdisj h) (howner v) hv
  have hwalk {u v : V} (W : G.Walk u v) :
      (connectedPartitionGraph G B).Reachable (owner u) (owner v) := by
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u w v huw W ih =>
      by_cases heq : owner u = owner w
      · simpa only [heq] using ih
      · have hadj : (connectedPartitionGraph G B).Adj (owner u) (owner w) :=
          ⟨heq, u, howner u, w, howner w, huw⟩
        exact hadj.reachable.trans ih
  refine ⟨?_⟩
  intro i j
  obtain ⟨W⟩ := hconn.preconnected (root i) (root j)
  simpa only [howner_eq (hroot i), howner_eq (hroot j)] using hwalk W

/-- A connected finite region, rather than the whole host, is enough
for connectedness of its partition quotient. -/
theorem connectedPartitionGraph_connected_on [Nonempty I]
    (K : Finset V) (hK : (G.induce (K : Set V)).Connected)
    (root : I → V) (B : I → Finset V) (hroot : ∀ i, root i ∈ B i)
    (hsub : ∀ i, B i ⊆ K)
    (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j))
    (hcover : ∀ v ∈ K, ∃ i, v ∈ B i) : (connectedPartitionGraph G B).Connected := by
  have hcov : ∀ v : {v : V // v ∈ K}, ∃ i, v.1 ∈ B i := fun v ↦ hcover v v.2
  choose owner howner using hcov
  have howner_eq {v : {v : V // v ∈ K}} {i : I} (hv : v.1 ∈ B i) : owner v = i := by
    by_contra h
    exact Finset.disjoint_left.mp (hdisj h) (howner v) hv
  have hwalk {u v : {v : V // v ∈ K}} (W : (G.induce (K : Set V)).Walk u v) :
      (connectedPartitionGraph G B).Reachable (owner u) (owner v) := by
    induction W with
    | nil => exact SimpleGraph.Reachable.refl _
    | @cons u w v huw W ih =>
      by_cases heq : owner u = owner w
      · simpa only [heq] using ih
      · have hadj : (connectedPartitionGraph G B).Adj (owner u) (owner w) :=
          ⟨heq, u.1, howner u, w.1, howner w, huw⟩
        exact hadj.reachable.trans ih
  refine ⟨?_⟩
  intro i j
  let ri : {v : V // v ∈ K} := ⟨root i, hsub i (hroot i)⟩
  let rj : {v : V // v ∈ K} := ⟨root j, hsub j (hroot j)⟩
  obtain ⟨W⟩ := hK.preconnected ri rj
  have hi : owner ri = i := howner_eq (hroot i)
  have hj : owner rj = j := howner_eq (hroot j)
  simpa only [hi, hj] using hwalk W

/-- The quotient is an actual ordinary minor, with the given partition
as its branch sets. -/
def connectedPartitionGraph_minorModel (B : I → Finset V)
    (hB : ∀ i, (B i).Nonempty ∧ (G.induce (B i : Set V)).Connected)
    (hdisj : Pairwise fun i j ↦ Disjoint (B i) (B j)) :
    Erdos73Infrastructure.SimpleGraph.MinorModel (connectedPartitionGraph G B) G where
  branchSet := B
  branch_nonempty := fun i ↦ (hB i).1
  branch_connected := fun i ↦ (hB i).2
  branch_disjoint := fun _ _ hij ↦ hdisj hij
  adjacent := fun {_ _} h ↦ h.2

/-- The earlier boundary-rooted models use the same ordinary graph-minor
notion; forgetting boundary control gives this branch-set model. -/
def LeftRootedModel.toMinorModel {H : SimpleGraph I} {A B : Finset V}
    (M : LeftRootedModel H G A B) :
    Erdos73Infrastructure.SimpleGraph.MinorModel H G where
  branchSet := M.branch
  branch_nonempty := fun i ↦ ⟨M.root i, M.root_mem i⟩
  branch_connected := M.connected
  branch_disjoint := fun _ _ hij ↦ M.disjoint hij
  adjacent := M.edge

end
end Erdos73
