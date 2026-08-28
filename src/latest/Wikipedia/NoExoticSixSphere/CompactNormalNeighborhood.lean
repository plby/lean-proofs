import Wikipedia.NoExoticSixSphere.LocalNormalNeighborhood
import Mathlib.Topology.Separation.Hausdorff

/-!
# An injective normal neighborhood for a compact embedded manifold

Compactness extends injectivity from the zero section to an open neighborhood.
Intersecting with the local-diffeomorphism locus gives a single neighborhood
where normal displacement is both injective and a smooth local diffeomorphism.
-/

open scoped Manifold ContDiff Topology Bundle
open Bundle Filter Set

namespace NoExoticSixSphere.EuclideanEmbedding

universe u

variable {n : ℕ} {M : Type u} [TopologicalSpace M]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M] [IsManifold (𝓡 n) ∞ M]
  (e : EuclideanEmbedding n M)

/-- The locus where normal displacement has a smooth local inverse. -/
def regularNormalLocus : Set e.NormalBundle :=
  {v | IsLocalDiffeomorphAt ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
    e.normalDisplacement v}

/-- Having a smooth local inverse is an open condition. -/
theorem isOpen_regularNormalLocus : IsOpen e.regularNormalLocus := by
  rw [isOpen_iff_mem_nhds]
  rintro v ⟨φ, hv, heq⟩
  exact mem_of_superset (φ.open_source.mem_nhds hv) (fun w hw ↦ ⟨φ, hw, heq⟩)

omit [IsManifold (𝓡 n) ∞ M] in
/-- Normal displacement is injective on the entire zero section. -/
theorem normalDisplacement_injOn_zeroSection :
    InjOn e.normalDisplacement (range (zeroSection e.NormalModel e.NormalSpace)) := by
  rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩ h
  have hxy : e.toFun x = e.toFun y := by
    simpa only [e.normalDisplacement_zero] using h
  exact congrArg (zeroSection e.NormalModel e.NormalSpace) (e.closedEmbedding.injective hxy)

/-- Each zero-section point has an open neighborhood where normal displacement is injective. -/
theorem normalDisplacement_locally_injective_zero (x : M) :
    ∃ U ∈ 𝓝 (zeroSection e.NormalModel e.NormalSpace x), InjOn e.normalDisplacement U := by
  obtain ⟨φ, hx, heq⟩ := e.isLocalDiffeomorphAt_normalDisplacement_zero x
  exact ⟨φ.source, φ.open_source.mem_nhds hx, heq.injOn_iff.mpr φ.toPartialEquiv.injOn⟩

/-- For a compact embedding, one open normal neighborhood is injective and locally diffeomorphic. -/
theorem exists_injective_normalNeighborhood [CompactSpace M] :
    ∃ U : Set e.NormalBundle, IsOpen U ∧
      range (zeroSection e.NormalModel e.NormalSpace) ⊆ U ∧
      InjOn e.normalDisplacement U ∧
      IsLocalDiffeomorphOn ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
        e.normalDisplacement U := by
  have hc : IsCompact (range (zeroSection e.NormalModel e.NormalSpace)) :=
    isCompact_range (Bundle.Trivialization.continuous_zeroSection ℝ)
  obtain ⟨V, hV, hsV, hInj⟩ := e.normalDisplacement_injOn_zeroSection.exists_isOpen_superset hc
    (fun v _ ↦ e.contMDiff_normalDisplacement.continuous.continuousAt)
    (by rintro _ ⟨x, rfl⟩; exact e.normalDisplacement_locally_injective_zero x)
  refine ⟨V ∩ e.regularNormalLocus, hV.inter e.isOpen_regularNormalLocus, ?_,
    hInj.mono inter_subset_left, ?_⟩
  · intro v hv
    refine ⟨hsV hv, ?_⟩
    obtain ⟨x, rfl⟩ := hv
    exact e.isLocalDiffeomorphAt_normalDisplacement_zero x
  · intro v
    exact v.property.2

/-- The image of an open local-normal neighborhood is open in the ambient Euclidean space. -/
theorem isOpen_normalNeighborhood_image {U : Set e.NormalBundle} (hU : IsOpen U)
    (hloc : IsLocalDiffeomorphOn ((𝓡 n).prod 𝓘(ℝ, e.NormalModel)) (𝓡 e.ambientDimension) ∞
      e.normalDisplacement U) : IsOpen (e.normalDisplacement '' U) := by
  rw [isOpen_iff_mem_nhds]
  rintro _ ⟨v, hv, rfl⟩
  rw [← hloc.isLocalHomeomorphOn.map_nhds_eq hv]
  exact image_mem_map (hU.mem_nhds hv)

end NoExoticSixSphere.EuclideanEmbedding
