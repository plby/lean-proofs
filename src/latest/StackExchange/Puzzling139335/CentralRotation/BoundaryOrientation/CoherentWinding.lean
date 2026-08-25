import StackExchange.Puzzling139335.CentralRotation.BoundaryOrientation.PathWinding

/-!
# Coherent winding on the two sides of a Jordan cut

The two piece boundaries use opposite traversals of the shared path.  Their
winding values about their respective interior points are equal.  This is
proved by actual path cancellation and Jordan-region contraction; opposite
boundary orientation is not an assumption.
-/

open Set unitInterval

namespace Puzzling139335.CentralRotation.BoundaryOrientation

noncomputable section

theorem boundaryPath_avoids {P : Set Plane} (f : C(I, Plane))
    (hf : range f ⊆ frontier P) {x : Plane} (hx : x ∈ interior P) :
    ∀ t, f t ≠ x := by
  intro t ht
  have hmem := hf (mem_range_self t)
  rw [ht] at hmem
  exact hmem.2 hx

private theorem avoids_of_range_subset (f g : C(I, Plane))
    (hfg : range f ⊆ range g) {x : Plane} (hg : ∀ t, g t ≠ x) :
    ∀ t, f t ≠ x := by
  intro t ht
  obtain ⟨s, hs⟩ := hfg (mem_range_self t)
  exact hg s (hs.trans ht)

private theorem path_left_range_subset {p q r : Plane} (M : Path p q) (N : Path q r) :
    range M ⊆ range (M.trans N) := by
  rw [Path.trans_range]
  exact subset_union_left

private theorem path_right_range_subset {p q r : Plane} (M : Path p q) (N : Path q r) :
    range N ⊆ range (M.trans N) := by
  rw [Path.trans_range]
  exact subset_union_right

private theorem closed_path {p : Plane} (L : Path p p) : L 0 = L 1 :=
  L.source.trans L.target.symm

/-- Boundaries formed by gluing the same actual cut in opposite directions
have the same winding about interior points of the two Jordan pieces. -/
theorem winding_boundary_pieces_eq {p q : Plane} (M : Path p q) (Γ N : Path q p)
    {A B U : Set Plane} (hA : IsJordanRegion A) (hB : IsJordanRegion B)
    (hU : IsJordanRegion U) (hunion : A ∪ B = U)
    (hdis : Disjoint (interior A) (interior B))
    (hFA : range (M.trans Γ) = frontier A)
    (hFB : range (Γ.symm.trans N) = frontier B)
    (hFU : range (M.trans N) = frontier U)
    {x y : Plane} (hx : x ∈ interior A) (hy : y ∈ interior B)
    (hAx : ∀ t, (M.trans Γ) t ≠ x)
    (hBy : ∀ t, (Γ.symm.trans N) t ≠ y) :
    winding (M.trans Γ) x hAx = winding (Γ.symm.trans N) y hBy := by
  have hAsub : A ⊆ U := by rw [← hunion]; exact subset_union_left
  have hBsub : B ⊆ U := by rw [← hunion]; exact subset_union_right
  have hxU : x ∈ interior U := interior_mono hAsub hx
  have hyU : y ∈ interior U := interior_mono hBsub hy
  have hxB : x ∉ B := fun h => Set.disjoint_left.mp
    (hB.disjoint_interior_left hdis) hx h
  have hyA : y ∉ A := fun h => Set.disjoint_left.mp
    (hA.disjoint_interior_left hdis.symm) hy h
  have hLA : ∀ t, (M.trans Γ) t ∈ A := by
    intro t
    have hmem : (M.trans Γ) t ∈ frontier A := hFA ▸ mem_range_self t
    exact hA.isClosed.closure_eq ▸ frontier_subset_closure hmem
  have hLB : ∀ t, (Γ.symm.trans N) t ∈ B := by
    intro t
    have hmem : (Γ.symm.trans N) t ∈ frontier B := hFB ▸ mem_range_self t
    exact hB.isClosed.closure_eq ▸ frontier_subset_closure hmem
  have hBx : ∀ t, (Γ.symm.trans N) t ≠ x := by
    intro t ht
    exact hxB (ht ▸ hLB t)
  have hAy : ∀ t, (M.trans Γ) t ≠ y := by
    intro t ht
    exact hyA (ht ▸ hLA t)
  have hUx : ∀ t, (M.trans N) t ≠ x :=
    boundaryPath_avoids _ hFU.le hxU
  have hUy : ∀ t, (M.trans N) t ≠ y :=
    boundaryPath_avoids _ hFU.le hyU
  have hMx := avoids_of_range_subset M (M.trans Γ) (path_left_range_subset M Γ) hAx
  have hΓx := avoids_of_range_subset Γ (M.trans Γ) (path_right_range_subset M Γ) hAx
  have hNx := avoids_of_range_subset N (Γ.symm.trans N)
    (path_right_range_subset Γ.symm N) hBx
  have hMy := avoids_of_range_subset M (M.trans Γ) (path_left_range_subset M Γ) hAy
  have hΓy := avoids_of_range_subset Γ (M.trans Γ) (path_right_range_subset M Γ) hAy
  have hNy := avoids_of_range_subset N (Γ.symm.trans N)
    (path_right_range_subset Γ.symm N) hBy
  have hgluex := winding_boundary_gluing M Γ N x hMx hΓx hNx hAx hBx hUx
  have hgluey := winding_boundary_gluing M Γ N y hMy hΓy hNy hAy hBy hUy
  have hzeroB := winding_eq_zero_of_jordan_container hB (Γ.symm.trans N) hLB
    (closed_path _) hxB hBx
  have hzeroA := winding_eq_zero_of_jordan_container hA (M.trans Γ) hLA
    (closed_path _) hyA hAy
  have hUxy := winding_eq_inside_jordan hU (M.trans N) hFU.le (closed_path _)
    hxU hyU hUx hUy
  rw [hzeroB, add_zero] at hgluex
  rw [hzeroA, zero_add] at hgluey
  exact hgluex.trans (hUxy.trans hgluey.symm)

end

end Puzzling139335.CentralRotation.BoundaryOrientation
