import Wikipedia.NoExoticSixSphere.CurveCutBranchGeometry
import Wikipedia.NoExoticSixSphere.CutCurveComponents

/-!
# Local branches identify the actual incident global components

A preconnected subset avoiding the cuts lies in any cut component it meets.
If a component accumulates at the center of a small cut neighborhood, it meets
one of its nonempty branches and contains that entire branch. This compares
actual connected components rather than an assumed combinatorial edge set.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveDecomposition

variable {X : Type*} [TopologicalSpace X]

theorem cutComponent_eq_connectedComponentIn (S : Set X) (x : {x : X // x ∉ S}) :
    cutComponent S x = connectedComponentIn Sᶜ x.val :=
  (connectedComponentIn_eq_image x.property).symm

theorem preconnected_subset_cutComponent (S B : Set X) (hB : IsPreconnected B)
    (hBS : B ⊆ Sᶜ) (x : {x : X // x ∉ S}) (hx : x.val ∈ B) : B ⊆ cutComponent S x := by
  rw [cutComponent_eq_connectedComponentIn]
  exact hB.subset_connectedComponentIn hx hBS

theorem cutComponent_eq_of_mem (S : Set X) (x y : {x : X // x ∉ S})
    (hy : y.val ∈ cutComponent S x) : cutComponent S y = cutComponent S x := by
  rw [cutComponent_eq_connectedComponentIn] at hy ⊢
  rw [cutComponent_eq_connectedComponentIn]
  exact (connectedComponentIn_eq hy).symm

theorem preconnected_subset_cutComponent_of_meets (S B : Set X) (hB : IsPreconnected B)
    (hBS : B ⊆ Sᶜ) (x : {x : X // x ∉ S}) (hmeet : (B ∩ cutComponent S x).Nonempty) :
    B ⊆ cutComponent S x := by
  obtain ⟨y, hyB, hyC⟩ := hmeet
  let z : {x : X // x ∉ S} := ⟨y, hBS hyB⟩
  have hz := preconnected_subset_cutComponent S B hB hBS z hyB
  rwa [cutComponent_eq_of_mem S x z hyC] at hz

theorem cutComponent_eq_of_inter_nonempty (S : Set X) (x y : {x : X // x ∉ S})
    (h : (cutComponent S x ∩ cutComponent S y).Nonempty) :
    cutComponent S x = cutComponent S y := by
  obtain ⟨z, hzx, hzy⟩ := h
  let w : {x : X // x ∉ S} := ⟨z, cutComponent_subset_compl S x hzx⟩
  exact (cutComponent_eq_of_mem S x w hzx).symm.trans (cutComponent_eq_of_mem S y w hzy)

theorem IntervalNeighborhood.incident_component_contains_branch
    (d : IntervalNeighborhood X) (v : X) (hv : v ∈ d.openSet) (S : Set X) (hvS : v ∈ S)
    (hcut : ∀ y ∈ d.closedSet, y ∈ S → y = v)
    (hzero : ∀ y ∈ d.chart.source, (d.chart y).val = 0 → y ∈ S)
    (x : {x : X // x ∉ S}) (hcl : v ∈ closure (cutComponent S x)) :
    ((d.leftBranch v).Nonempty ∧ d.leftBranch v ⊆ cutComponent S x) ∨
      ((d.rightBranch v).Nonempty ∧ d.rightBranch v ⊆ cutComponent S x) := by
  obtain ⟨y, hyU, hyC⟩ := (mem_closure_iff.mp hcl) d.openSet d.isOpen_openSet hv
  have hyne : y ≠ v := by
    rintro rfl
    exact cutComponent_subset_compl S x hyC hvS
  have hyB : y ∈ d.leftBranch v ∪ d.rightBranch v := by
    rw [← d.punctured_eq_branches v hv S hcut hzero]
    exact ⟨hyU, hyne⟩
  rcases hyB with hyB | hyB
  · left
    refine ⟨⟨y, hyB⟩, ?_⟩
    exact preconnected_subset_cutComponent_of_meets S (d.leftBranch v)
      (d.isPreconnected_leftBranch v hv) (d.leftBranch_subset_compl v hv S hcut) x
      ⟨y, hyB, hyC⟩
  · right
    refine ⟨⟨y, hyB⟩, ?_⟩
    exact preconnected_subset_cutComponent_of_meets S (d.rightBranch v)
      (d.isConnected_rightBranch v hv).isPreconnected
      (d.rightBranch_subset_compl v hv S hcut) x ⟨y, hyB, hyC⟩

end NoExoticSixSphere.CurveDecomposition
