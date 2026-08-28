import Wikipedia.SmoothSixDPoincare.ChartDiskBoundary

/-!
# Removing the interiors of two coordinate disks

The remaining space is a genuine closed subspace of the original manifold.
The two boundary spheres embed in it. Proving that this space is an
h-cobordism, and then a product, remains a separate geometric obligation.
-/

noncomputable section

open Set Metric Topology

namespace Wikipedia.SmoothSixDPoincare

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]

def diskCutout (d₁ d₂ : ChartDisk E M) : Set M := (d₁.core ∪ d₂.core)ᶜ

omit [NormedSpace ℝ E] in
theorem diskCutout_comm (d₁ d₂ : ChartDisk E M) :
    diskCutout d₁ d₂ = diskCutout d₂ d₁ := by
  simp only [diskCutout, union_comm]

omit [NormedSpace ℝ E] in
theorem isClosed_diskCutout (d₁ d₂ : ChartDisk E M) : IsClosed (diskCutout d₁ d₂) :=
  (d₁.isOpen_core.union d₂.isOpen_core).isClosed_compl

instance diskCutout_compactSpace [CompactSpace M] (d₁ d₂ : ChartDisk E M) :
    CompactSpace (diskCutout d₁ d₂) :=
  isCompact_iff_compactSpace.mp (isClosed_diskCutout d₁ d₂).isCompact

theorem boundaryMap_mem_diskCutout (d₁ d₂ : ChartDisk E M)
    (hd : Disjoint (range d₁.map) (range d₂.map)) (x : sphere (0 : E) 1) :
    d₁.boundaryMap x ∈ diskCutout d₁ d₂ := by
  rintro (hx | hx)
  · exact d₁.boundaryMap_not_mem_core x hx
  · exact Set.disjoint_left.mp hd (d₁.boundaryMap_mem_range x) (d₂.core_subset_range hx)

/-- The first actual boundary sphere, embedded in the disk complement. -/
def cutoutBoundaryMap (d₁ d₂ : ChartDisk E M)
    (hd : Disjoint (range d₁.map) (range d₂.map)) :
    C(sphere (0 : E) 1, diskCutout d₁ d₂) :=
  ⟨fun x => ⟨d₁.boundaryMap x, boundaryMap_mem_diskCutout d₁ d₂ hd x⟩,
    d₁.boundaryMap.continuous.subtype_mk _⟩

theorem cutoutBoundaryMap_injective (d₁ d₂ : ChartDisk E M)
    (hd : Disjoint (range d₁.map) (range d₂.map)) :
    Function.Injective (cutoutBoundaryMap d₁ d₂ hd) := by
  intro x y h
  exact d₁.boundaryMap_injective (congrArg Subtype.val h)

theorem cutoutBoundaryMap_isClosedEmbedding [FiniteDimensional ℝ E] [T2Space M]
    (d₁ d₂ : ChartDisk E M) (hd : Disjoint (range d₁.map) (range d₂.map)) :
    IsClosedEmbedding (cutoutBoundaryMap d₁ d₂ hd) :=
  (cutoutBoundaryMap d₁ d₂ hd).continuous.isClosedEmbedding
    (cutoutBoundaryMap_injective d₁ d₂ hd)

end Wikipedia.SmoothSixDPoincare
