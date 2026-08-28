import Wikipedia.HopfProblem.SpecialPeriodsTriangleTiling

/-!
# The locally finite closed edges of the reflection triangles

Each edge is the portion of one of the three side carriers inside the
closed half-Ford triangle, followed by an actual reflected triangle map.
These portions are closed in the upper half-plane and locally finite,
because each is contained in its indexed closed triangle. They cover
the complement of the open triangles.

The complex-plane statements are relative to the open upper half-plane.
Only the actual edge portions, not all their extended geodesics, are
asserted to form a locally finite family.
-/

noncomputable section

open Set UpperHalfPlane
open scoped Topology

namespace Wikipedia.HopfProblem.SpecialPeriods.Triangle

/-- The three geodesic carriers, ordered left, right, circular. -/
def halfEdgeCarrier : Fin 3 → Set ℍ :=
  ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖(z : ℂ) + 1‖ = 1}]

/-- An actual closed side of the half-Ford triangle. -/
def halfFordEdge (k : Fin 3) : Set ℍ := halfFordRegion ∩ halfEdgeCarrier k

theorem halfEdgeCarrier_isClosed (k : Fin 3) : IsClosed (halfEdgeCarrier k) := by
  fin_cases k
  · exact isClosed_eq continuous_re continuous_const
  · exact isClosed_eq continuous_re continuous_const
  · exact isClosed_eq (continuous_coe.add continuous_const).norm continuous_const

theorem halfFordEdge_isClosed (k : Fin 3) : IsClosed (halfFordEdge k) :=
  halfFordRegion_isClosed.inter (halfEdgeCarrier_isClosed k)

theorem halfFordEdge_subset_region (k : Fin 3) : halfFordEdge k ⊆ halfFordRegion :=
  inter_subset_left

theorem halfFordEdge_subset_boundary (k : Fin 3) :
    halfFordEdge k ⊆ halfFordRegion \ halfFordInterior := by
  intro z hz
  refine ⟨hz.1, ?_⟩
  intro hi
  have hc := hz.2
  fin_cases k
  · change z.re = stripLeft at hc
    exact (ne_of_gt hi.1.1) hc
  · change z.re = -(1 / 2) at hc
    exact (ne_of_lt hi.2) hc
  · change ‖(z : ℂ) + 1‖ = 1 at hc
    exact (ne_of_gt hi.1.2.2.1) hc

/-- The three closed sides are exactly the closed triangle minus its
topological interior, including all finite vertices. -/
theorem halfFordEdges_eq_boundary :
    (⋃ k : Fin 3, halfFordEdge k) = halfFordRegion \ halfFordInterior := by
  apply Subset.antisymm
  · exact iUnion_subset halfFordEdge_subset_boundary
  · rintro z ⟨hz, hnot⟩
    by_cases hl : z.re = stripLeft
    · exact mem_iUnion.mpr ⟨0, hz, hl⟩
    by_cases hr : z.re = -(1 / 2)
    · exact mem_iUnion.mpr ⟨1, hz, hr⟩
    by_cases hn : ‖(z : ℂ) + 1‖ = 1
    · exact mem_iUnion.mpr ⟨2, hz, hn⟩
    have hl' : stripLeft < z.re := lt_of_le_of_ne hz.1.1 (Ne.symm hl)
    have hr' : z.re < -(1 / 2) := lt_of_le_of_ne hz.2 hr
    have hn' : 1 < ‖(z : ℂ) + 1‖ := lt_of_le_of_ne hz.1.2.2.1 (Ne.symm hn)
    apply (hnot ?_).elim
    refine ⟨⟨hl', ?_, hn', one_lt_norm_of_re_lt_neg_half z hr' hn'⟩, hr'⟩
    linarith [stripRight_pos]

theorem halfFordEdges_eq_frontier :
    (⋃ k : Fin 3, halfFordEdge k) = frontier halfFordRegion := by
  rw [halfFordEdges_eq_boundary, frontier, halfFordRegion_isClosed.closure_eq,
    interior_halfFordRegion]

/-- The image of an actual side under the indexed reflection triangle map. -/
def halfTriangleEdge (i : TriangleGroup × Bool) (k : Fin 3) : Set ℍ :=
  halfTriangleMap i '' halfFordEdge k

/-- An edge is indexed by its triangle and its one of three side labels. -/
abbrev TriangleEdgeIndex := (TriangleGroup × Bool) × Fin 3

theorem halfTriangleEdge_eq (i : TriangleGroup × Bool) (k : Fin 3) :
    halfTriangleEdge i k =
      triangleGeometricRepresentation i.1 '' (halfFold i.2 '' halfFordEdge k) := by
  rw [Set.image_image]
  rfl

theorem halfTriangleEdge_isClosed (i : TriangleGroup × Bool) (k : Fin 3) :
    IsClosed (halfTriangleEdge i k) :=
  (halfTriangleMap i).isClosedMap _ (halfFordEdge_isClosed k)

theorem halfTriangleEdge_subset_tile (i : TriangleGroup × Bool) (k : Fin 3) :
    halfTriangleEdge i k ⊆ halfTriangleTile i :=
  image_mono (halfFordEdge_subset_region k)

theorem halfTriangleEdges_eq_boundary (i : TriangleGroup × Bool) :
    (⋃ k : Fin 3, halfTriangleEdge i k) =
      halfTriangleTile i \ halfTriangleOpenTile i := by
  unfold halfTriangleEdge halfTriangleTile halfTriangleOpenTile
  rw [← image_iUnion, halfFordEdges_eq_boundary,
    image_sdiff (halfTriangleMap i).injective]

theorem halfTriangleEdge_subset_boundary (i : TriangleGroup × Bool) (k : Fin 3) :
    halfTriangleEdge i k ⊆ halfTriangleTile i \ halfTriangleOpenTile i := by
  rw [← halfTriangleEdges_eq_boundary]
  exact subset_iUnion _ k

/-- Every point outside all open triangles lies on one of the actual edges. -/
theorem triangleEdges_cover_openTile_complement :
    (⋃ i : TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ ⊆
      ⋃ j : TriangleEdgeIndex, halfTriangleEdge j.1 j.2 := by
  intro z hz
  have hcover : z ∈ ⋃ i : TriangleGroup × Bool, halfTriangleTile i := by
    rw [halfTriangleTiles_cover]
    exact mem_univ z
  obtain ⟨i, hi⟩ := mem_iUnion.mp hcover
  have hb : z ∈ ⋃ k : Fin 3, halfTriangleEdge i k := by
    rw [halfTriangleEdges_eq_boundary]
    exact ⟨hi, fun h => hz (mem_iUnion.mpr ⟨i, h⟩)⟩
  obtain ⟨k, hk⟩ := mem_iUnion.mp hb
  exact mem_iUnion.mpr ⟨(i, k), hk⟩

/-- Three edge portions per locally finite closed triangle give a
locally finite family; no extended geodesic is used here. -/
theorem halfTriangleEdges_locallyFinite :
    LocallyFinite (fun j : TriangleEdgeIndex => halfTriangleEdge j.1 j.2) := by
  intro z
  obtain ⟨U, hU, hfin⟩ := halfTriangleTiles_locallyFinite z
  refine ⟨U, hU, (hfin.prod (Set.finite_univ : (univ : Set (Fin 3)).Finite)).subset ?_⟩
  rintro j ⟨w, hw, hwU⟩
  exact ⟨⟨w, halfTriangleEdge_subset_tile j.1 j.2 hw, hwU⟩, mem_univ _⟩

/-- The actual indexed edge, viewed as a subset of the complex plane. -/
def triangleEdgeComplex (j : TriangleEdgeIndex) : Set ℂ :=
  ((↑) : ℍ → ℂ) '' halfTriangleEdge j.1 j.2

theorem triangleEdgeComplex_subset_upperHalfPlaneSet (j : TriangleEdgeIndex) :
    triangleEdgeComplex j ⊆ UpperHalfPlane.upperHalfPlaneSet := by
  rintro z ⟨w, _, rfl⟩
  exact w.im_pos

/-- Closedness of an edge relative to the upper half-plane, expressed
by its open complement in the complex plane. -/
theorem triangleEdgeComplex_relative_compl_isOpen (j : TriangleEdgeIndex) :
    IsOpen (UpperHalfPlane.upperHalfPlaneSet \ triangleEdgeComplex j) := by
  have h := UpperHalfPlane.isOpenEmbedding_coe.isOpenMap
    (halfTriangleEdge j.1 j.2)ᶜ (halfTriangleEdge_isClosed j.1 j.2).isOpen_compl
  simpa only [triangleEdgeComplex,
    Set.image_compl_eq_range_sdiff_image UpperHalfPlane.coe_injective,
    UpperHalfPlane.range_coe] using h

/-- Local finiteness in the open upper half-plane, not at its real boundary. -/
theorem triangleEdgeComplex_locallyFinite :
    LocallyFinite (fun j : TriangleEdgeIndex =>
      ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j) := by
  let g : UpperHalfPlane.upperHalfPlaneSet → ℍ := fun z => ⟨z.1, z.2⟩
  have hg : Continuous g :=
    UpperHalfPlane.isEmbedding_coe.continuous_iff.mpr continuous_subtype_val
  have hpre : ∀ j : TriangleEdgeIndex,
      ((↑) : UpperHalfPlane.upperHalfPlaneSet → ℂ) ⁻¹' triangleEdgeComplex j =
        g ⁻¹' halfTriangleEdge j.1 j.2 := by
    intro j
    ext z
    simp only [triangleEdgeComplex, Set.mem_preimage, Set.mem_image]
    constructor
    · rintro ⟨w, hw, hwz⟩
      have hwg : w = g z := UpperHalfPlane.coe_injective hwz
      simpa only [hwg] using hw
    · intro h
      exact ⟨g z, h, rfl⟩
  simp_rw [hpre]
  exact halfTriangleEdges_locallyFinite.preimage_continuous hg

theorem triangleEdgeComplex_cover_openTile_complement :
    UpperHalfPlane.upperHalfPlaneSet \
        (⋃ i : TriangleGroup × Bool, ((↑) : ℍ → ℂ) '' halfTriangleOpenTile i) ⊆
      ⋃ j : TriangleEdgeIndex, triangleEdgeComplex j := by
  rintro z ⟨hz, hnot⟩
  let w : ℍ := ⟨z, hz⟩
  have hw : w ∈ (⋃ i : TriangleGroup × Bool, halfTriangleOpenTile i)ᶜ := by
    intro hi
    obtain ⟨i, hi⟩ := mem_iUnion.mp hi
    exact hnot (mem_iUnion.mpr ⟨i, w, hi, rfl⟩)
  obtain ⟨j, hj⟩ := mem_iUnion.mp (triangleEdges_cover_openTile_complement hw)
  exact mem_iUnion.mpr ⟨j, w, hj, rfl⟩

/-- The simple analytic curve containing a folded base edge. These full
carriers are used only for containment, not for local finiteness. -/
def foldedEdgeComplexCarrier (b : Bool) : Fin 3 → Set ℂ :=
  if b then
    ![{z | z.re = stripRight}, {z | z.re = -(1 / 2)}, {z | ‖z‖ = 1}]
  else
    ![{z | z.re = stripLeft}, {z | z.re = -(1 / 2)}, {z | ‖z + 1‖ = 1}]

theorem foldedEdgeComplex_subset_carrier (b : Bool) (k : Fin 3) :
    ((↑) : ℍ → ℂ) '' (halfFold b '' halfFordEdge k) ⊆
      foldedEdgeComplexCarrier b k := by
  rintro z ⟨w, ⟨u, hu, rfl⟩, rfl⟩
  have hc := hu.2
  cases b <;> fin_cases k
  · exact hc
  · exact hc
  · exact hc
  · change u.re = stripLeft at hc
    change (rightReflection u).re = stripRight
    rw [rightReflection_re, hc]
    linarith [stripLeft_add_stripRight]
  · change u.re = -(1 / 2) at hc
    change (rightReflection u).re = -(1 / 2)
    rw [rightReflection_re, hc]
    norm_num
  · change ‖(u : ℂ) + 1‖ = 1 at hc
    change ‖(rightReflection u : ℂ)‖ = 1
    rw [rightReflection_norm]
    exact hc

end Wikipedia.HopfProblem.SpecialPeriods.Triangle
