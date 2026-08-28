import Wikipedia.SmoothSixDPoincare.SeparatedDegreeNeighborhoods

/-!
# The actual open cover associated with separated regular-zero neighborhoods

The complement of the original finite point set and the union of the
constructed chart neighborhoods cover the original manifold. Disjointness
proves that each overlap removes exactly its own center. Its sphere
equivalence therefore uses the already-constructed original inner boundary.
-/

noncomputable section

open Set Metric Topology ContinuousMap Function
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods

variable {E F M : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  {P : Set M} {f : M → F} {W : Set M} (D : SeparatedNeighborhoods E P f W)

def neighborhood (x : P) : Set M := NativeNeighborhood.openSet (x : M) (D.data x)

theorem isOpen_neighborhood (x : P) : IsOpen (D.neighborhood x) :=
  NativeNeighborhood.isOpen_openSet (x : M) (D.data x)

theorem center_mem_neighborhood (x : P) : (x : M) ∈ D.neighborhood x :=
  NativeNeighborhood.center_mem_openSet (x : M) (D.data x)

theorem neighborhood_subset (x : P) : D.neighborhood x ⊆ W :=
  NativeNeighborhood.openSet_subset (x : M) (D.data x)

theorem pairwise_disjoint : Pairwise (Disjoint on D.neighborhood) := D.disjoint

theorem points_inter_neighborhood (x : P) : P ∩ D.neighborhood x = {(x : M)} := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    change y = (x : M)
    by_contra hne
    let z : P := ⟨y, hyP⟩
    have hxz : x ≠ z := fun h => hne (congrArg Subtype.val h).symm
    exact Set.disjoint_left.mp (D.pairwise_disjoint hxz) hy (D.center_mem_neighborhood z)
  · rintro rfl
    exact ⟨x.property, D.center_mem_neighborhood x⟩

/-- The global point-complement overlap is precisely the original one-center puncture. -/
theorem overlap_eq (x : P) : Pᶜ ∩ D.neighborhood x = {(x : M)}ᶜ ∩ D.neighborhood x := by
  ext y
  constructor
  · rintro ⟨hyP, hy⟩
    refine ⟨?_, hy⟩
    rintro rfl
    exact hyP x.property
  · rintro ⟨hyx, hy⟩
    refine ⟨?_, hy⟩
    intro hyP
    have h : y ∈ P ∩ D.neighborhood x := ⟨hyP, hy⟩
    rw [D.points_inter_neighborhood x] at h
    exact hyx h

theorem open_cover : Pᶜ ∪ (⋃ x : P, D.neighborhood x) = univ := by
  apply eq_univ_of_forall
  intro y
  by_cases hy : y ∈ P
  · exact Or.inr (mem_iUnion.mpr ⟨⟨y, hy⟩, D.center_mem_neighborhood ⟨y, hy⟩⟩)
  · exact Or.inl hy

theorem isOpen_union : IsOpen (⋃ x : P, D.neighborhood x) :=
  isOpen_iUnion D.isOpen_neighborhood

def overlapSphereEquiv (x : P) : sphere (0 : E) 1 ≃ₕ ↥(Pᶜ ∩ D.neighborhood x) :=
  (NativeNeighborhood.overlapSphereEquiv (x : M) (D.data x)).trans
    (Homeomorph.setCongr (D.overlap_eq x).symm).toHomotopyEquiv

/-- The actual global overlap class is parametrized by this original local boundary. -/
theorem overlapSphereEquiv_apply (x : P) (u : sphere (0 : E) 1) :
    (D.overlapSphereEquiv x u).val =
      NativeParametrization.centered (x : M) ((D.data x).innerBoundary.radius • (u : E)) := rfl

theorem image_eq_zero_iff (x : P) {y : M} (hy : y ∈ D.neighborhood x) :
    f y = 0 ↔ y = (x : M) := NativeNeighborhood.image_eq_zero_iff (x : M) (D.data x) hy

end Wikipedia.SmoothSixDPoincare.LocalDegree.SeparatedNeighborhoods
