import ErdosProblems.Erdos745.Components
import Mathlib.Combinatorics.SimpleGraph.Acyclic

/-!
# Tree components as components and as vertex-set events
-/

namespace Erdos745

noncomputable section

attribute [local instance] Classical.propDecidable

variable {V : Type*} [Fintype V] [DecidableEq V]

/-- No edge leaves the vertex set. -/
def IsClosedVertexSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∀ u ∈ S, ∀ v, G.Adj u v → v ∈ S

theorem reachable_mem_of_closed {G : SimpleGraph V} {S : Finset V}
    (hS : IsClosedVertexSet G S) {u v : V} (hu : u ∈ S)
    (huv : G.Reachable u v) : v ∈ S := by
  obtain ⟨p⟩ := huv
  induction p with
  | nil => exact hu
  | @cons u w v huw p ih =>
      exact ih (hS u hu w huw)

/-- The finite vertex set is exactly one connected component. -/
def IsComponentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  ∃ C : G.ConnectedComponent, C.supp = (S : Set V)

theorem componentSets_disjoint_of_ne {G : SimpleGraph V} {S U : Finset V}
    (hS : IsComponentSet G S) (hU : IsComponentSet G U) (hne : S ≠ U) : Disjoint S U := by
  obtain ⟨C, hC⟩ := hS
  obtain ⟨D, hD⟩ := hU
  have hCD : C ≠ D := by
    intro h
    subst D
    exact hne (Finset.coe_injective (hC.symm.trans hD))
  rw [← Finset.disjoint_coe, ← hC, ← hD]
  exact G.pairwise_disjoint_supp_connectedComponent hCD

theorem isComponentSet_iff_connected_closed (G : SimpleGraph V) (S : Finset V) :
    IsComponentSet G S ↔ (G.induce (S : Set V)).Connected ∧ IsClosedVertexSet G S := by
  constructor
  · rintro ⟨C, hC⟩
    constructor
    · have hconn := SimpleGraph.ConnectedComponent.connected_toSimpleGraph C
      change (G.induce C.supp).Connected at hconn
      rw [hC] at hconn
      exact hconn
    · intro u hu v huv
      have huC : u ∈ C.supp := by simpa only [hC, Finset.mem_coe] using hu
      have hvC := C.mem_supp_of_adj_mem_supp huC huv
      simpa only [hC, Finset.mem_coe] using hvC
  · rintro ⟨hconn, hclosed⟩
    obtain ⟨v⟩ := hconn.nonempty
    refine ⟨G.connectedComponentMk v.val, ?_⟩
    ext u
    constructor
    · intro hu
      exact reachable_mem_of_closed hclosed v.property
        ((G.connectedComponentMk v.val).reachable_of_mem_supp
          SimpleGraph.ConnectedComponent.connectedComponentMk_mem hu)
    · intro hu
      have hreach := (hconn.preconnected ⟨u, hu⟩ v).map
        (SimpleGraph.Embedding.induce (S : Set V)).toHom
      exact SimpleGraph.ConnectedComponent.sound hreach

/-- A vertex-set event specifying an isolated tree component. -/
def IsTreeComponentSet (G : SimpleGraph V) (S : Finset V) : Prop :=
  IsComponentSet G S ∧ (G.induce (S : Set V)).IsTree

theorem isTreeComponentSet_iff (G : SimpleGraph V) (S : Finset V) :
    IsTreeComponentSet G S ↔
      (G.induce (S : Set V)).IsTree ∧ IsClosedVertexSet G S := by
  rw [IsTreeComponentSet, isComponentSet_iff_connected_closed]
  constructor
  · rintro ⟨⟨_, hclosed⟩, htree⟩
    exact ⟨htree, hclosed⟩
  · rintro ⟨htree, hclosed⟩
    exact ⟨⟨htree.connected, hclosed⟩, htree⟩

/-- Number of tree components whose orders belong to the finite window `I`. -/
def treeComponentCount (G : SimpleGraph V) (I : Finset ℕ) : ℕ :=
  (Finset.univ.filter fun C : G.ConnectedComponent ↦
    C.toSimpleGraph.IsTree ∧ C.supp.ncard ∈ I).card

theorem treeComponentCount_le_largeComponentCount (G : SimpleGraph V)
    (I : Finset ℕ) {k : ℕ} (hI : ∀ j ∈ I, k ≤ j) :
    treeComponentCount G I ≤ largeComponentCount G k := by
  apply Finset.card_le_card
  intro C hC
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hC ⊢
  exact hI _ hC.2

theorem le_secondLargestComponentOrder_of_two_trees (G : SimpleGraph V)
    (I : Finset ℕ) {k : ℕ} (hk : 0 < k) (hI : ∀ j ∈ I, k ≤ j)
    (hcount : 2 ≤ treeComponentCount G I) :
    k ≤ secondLargestComponentOrder G := by
  rw [le_secondLargestComponentOrder_iff_count G hk]
  exact hcount.trans (treeComponentCount_le_largeComponentCount G I hI)

theorem component_support_toFinset_injective (G : SimpleGraph V) :
    Function.Injective (fun C : G.ConnectedComponent ↦ C.supp.toFinset) := by
  intro C D hCD
  apply SimpleGraph.ConnectedComponent.supp_injective
  have h := congrArg (fun S : Finset V ↦ (S : Set V)) hCD
  simpa using h

/-- Exact conversion from quotient components to a finite sum over vertex sets. -/
theorem treeComponentCount_eq_vertexSet_count (G : SimpleGraph V) (I : Finset ℕ) :
    treeComponentCount G I =
      ((Finset.univ : Finset V).powerset.filter fun S ↦
        S.card ∈ I ∧ IsTreeComponentSet G S).card := by
  let Cset := (Finset.univ : Finset G.ConnectedComponent).filter fun C ↦
    C.toSimpleGraph.IsTree ∧ C.supp.ncard ∈ I
  have himage : Cset.image (fun C ↦ C.supp.toFinset) =
      (Finset.univ : Finset V).powerset.filter (fun S ↦
        S.card ∈ I ∧ IsTreeComponentSet G S) := by
    ext S
    constructor
    · intro hS
      obtain ⟨C, hC, rfl⟩ := Finset.mem_image.mp hS
      have hC' : C.toSimpleGraph.IsTree ∧ C.supp.ncard ∈ I := by
        simpa only [Cset, Finset.mem_filter, Finset.mem_univ, true_and] using hC
      refine Finset.mem_filter.mpr ⟨Finset.mem_powerset.mpr (Finset.subset_univ _), ?_⟩
      refine ⟨?_, ⟨C, by simp⟩, ?_⟩
      · simpa only [← Set.ncard_eq_toFinset_card'] using hC'.2
      · change (G.induce (↑C.supp.toFinset : Set V)).IsTree
        rw [Set.coe_toFinset]
        exact hC'.1
    · intro hS
      obtain ⟨_, hsize, ⟨C, hC⟩, htree⟩ := Finset.mem_filter.mp hS
      have heq : C.supp.toFinset = S := by
        apply Finset.coe_injective
        simpa using hC
      refine Finset.mem_image.mpr ⟨C, ?_, heq⟩
      simp only [Cset, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · change (G.induce C.supp).IsTree
        rw [hC]
        exact htree
      · simpa only [hC, Set.ncard_coe_finset] using hsize
  rw [← himage, Finset.card_image_of_injective _ (component_support_toFinset_injective G)]
  rfl

theorem treeComponentCount_singleton_eq (G : SimpleGraph V) (k : ℕ) :
    treeComponentCount G {k} =
      ((Finset.univ.powersetCard k).filter (IsTreeComponentSet G)).card := by
  rw [treeComponentCount_eq_vertexSet_count]
  congr 1
  ext S
  simp only [Finset.mem_filter, Finset.mem_powerset, Finset.mem_singleton,
    Finset.mem_powersetCard]
  tauto

end

end Erdos745
