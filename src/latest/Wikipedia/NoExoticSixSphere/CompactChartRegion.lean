import Mathlib.Topology.OpenPartialHomeomorph.IsImage
import Mathlib.Topology.Separation.Hausdorff

/-!
# Closure and frontier of a relatively compact chart region

When the closure of a target region is compact and stays inside the actual
chart target, its inverse image has exactly the corresponding closure and
frontier. Compactness prevents additional frontier points outside the chart.
-/

open Set Function Topology

namespace NoExoticSixSphere.CurveChart

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

def region (e : OpenPartialHomeomorph X Y) (V : Set Y) : Set X :=
  e.source ∩ e ⁻¹' V

theorem isImage_region (e : OpenPartialHomeomorph X Y) (V : Set Y) :
    e.IsImage (region e V) V := fun _ hx ↦ ⟨fun hy ↦ ⟨hx, hy⟩, fun h ↦ h.2⟩

theorem isOpen_region (e : OpenPartialHomeomorph X Y) {V : Set Y} (hV : IsOpen V) :
    IsOpen (region e V) := e.isOpen_inter_preimage hV

theorem region_eq_image (e : OpenPartialHomeomorph X Y) {V : Set Y}
    (hV : V ⊆ e.target) : region e V = e.symm '' V := by
  ext x
  constructor
  · rintro ⟨hx, hxV⟩
    exact ⟨e x, hxV, e.left_inv hx⟩
  · rintro ⟨y, hy, rfl⟩
    refine ⟨e.map_target (hV hy), ?_⟩
    change e (e.symm y) ∈ V
    simpa only [e.right_inv (hV hy)] using hy

theorem closure_region [T2Space X] (e : OpenPartialHomeomorph X Y) {V : Set Y}
    (hcomp : IsCompact (closure V)) (ht : closure V ⊆ e.target) :
    closure (region e V) = e.symm '' closure V := by
  have hk : IsCompact (e.symm '' closure V) :=
    hcomp.image_of_continuousOn (e.continuousOn_symm.mono ht)
  have hsub : region e V ⊆ e.symm '' closure V := by
    rw [region_eq_image e (subset_closure.trans ht)]
    exact image_mono subset_closure
  apply subset_antisymm (closure_minimal hsub hk.isClosed)
  rintro x ⟨y, hy, rfl⟩
  apply ((isImage_region e V).closure (e.map_target (ht hy))).mp
  simpa only [e.right_inv (ht hy)] using hy

theorem isCompact_closure_region [T2Space X] (e : OpenPartialHomeomorph X Y)
    {V : Set Y} (hcomp : IsCompact (closure V)) (ht : closure V ⊆ e.target) :
    IsCompact (closure (region e V)) := by
  rw [closure_region e hcomp ht]
  exact hcomp.image_of_continuousOn (e.continuousOn_symm.mono ht)

theorem closure_region_subset_source [T2Space X] (e : OpenPartialHomeomorph X Y)
    {V : Set Y} (hcomp : IsCompact (closure V)) (ht : closure V ⊆ e.target) :
    closure (region e V) ⊆ e.source := by
  rw [closure_region e hcomp ht]
  rintro x ⟨y, hy, rfl⟩
  exact e.map_target (ht hy)

theorem frontier_region [T2Space X] (e : OpenPartialHomeomorph X Y) {V : Set Y}
    (hcomp : IsCompact (closure V)) (ht : closure V ⊆ e.target) :
    frontier (region e V) = e.symm '' frontier V := by
  ext x
  constructor
  · intro hx
    have hs := closure_region_subset_source e hcomp ht (frontier_subset_closure hx)
    exact ⟨e x, ((isImage_region e V).frontier hs).mpr hx, e.left_inv hs⟩
  · rintro ⟨y, hy, rfl⟩
    have hyt := ht (frontier_subset_closure hy)
    apply ((isImage_region e V).frontier (e.map_target hyt)).mp
    simpa only [e.right_inv hyt] using hy

theorem finite_frontier_region [T2Space X] (e : OpenPartialHomeomorph X Y) {V : Set Y}
    (hcomp : IsCompact (closure V)) (ht : closure V ⊆ e.target)
    (hfin : (frontier V).Finite) : (frontier (region e V)).Finite := by
  rw [frontier_region e hcomp ht]
  exact hfin.image e.symm

end NoExoticSixSphere.CurveChart
