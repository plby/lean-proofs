import Wikipedia.SmoothSixDPoincare.FinitePlaneImmersion
import Wikipedia.SmoothSixDPoincare.RelativeImmersionPatch

/-!
# Relative immersion improvement on any compact planar region

All charts, cutoffs, compact plateaus, and finite covers are constructed from
the original smooth map. The new compact region must be disjoint from the
fixed closed set. An already immersive compact region is retained. This does
not assert global injectivity of the resulting map or an embedded filling.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open PlaneImmersion (Plane)
open ManifoldSmoothing (MapSmoothingPatch)

variable {G H N : Type*}
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] {J : ModelWithCorners ℝ G H} [J.Boundaryless]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold J ∞ N] [T2Space N]

/-- Improve a compact region away from a fixed closed set, retaining the native injective
derivatives on a previously immersive compact region. -/
theorem exists_immersion_on_compact_rel (f : C(Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {K L C : Set Plane} (hK : IsCompact K) (hL : IsCompact L)
    (hinj : ∀ x ∈ K, Function.Injective (mfderiv 𝓘(ℝ, Plane) J f x))
    (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧ f.HomotopicRel g C ∧
      ∀ x ∈ K ∪ L, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  classical
  have hp (x : L) := exists_relative_immersion_patch_at (J := J) f hC
    (show (x : Plane) ∉ C from fun hx => Set.disjoint_left.mp hdis x.property hx)
  choose p T hcompatible hT hn hsub hfixed using hp
  have hcover : L ⊆ ⋃ x : L, interior (T x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hL.elim_finite_subcover (fun x : L => interior (T x))
    (fun _ => isOpen_interior) hcover
  obtain ⟨g, hg, -, hhom, hderiv⟩ := exists_finite_patch_immersion
    (fun i : s => p i.1) (fun i : s => T i.1) (fun i => hT i.1) (fun i => hsub i.1)
    f hf (fun i => hcompatible i.1) hdim hK hinj (fun i => hfixed i.1) Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro x hx
  apply hderiv x
  rcases hx with hx | hx
  · exact Or.inl hx
  · obtain ⟨i, his, hxi⟩ := mem_iUnion₂.mp (hs hx)
    exact Or.inr (mem_iUnion₂.mpr ⟨⟨i, his⟩, Finset.mem_univ _, interior_subset hxi⟩)

/-- In particular a smooth map can be made immersive on any compact region away from the
prescribed fixed set, without supplying chart or perturbation data. -/
theorem exists_immersion_on_compact (f : C(Plane, N))
    (hf : ContMDiff 𝓘(ℝ, Plane) J ∞ f) (hdim : 5 ≤ Module.finrank ℝ G)
    {L C : Set Plane} (hL : IsCompact L) (hC : IsClosed C) (hdis : Disjoint L C) :
    ∃ g : C(Plane, N), ContMDiff 𝓘(ℝ, Plane) J ∞ g ∧ f.HomotopicRel g C ∧
      ∀ x ∈ L, Function.Injective (mfderiv 𝓘(ℝ, Plane) J g x) := by
  obtain ⟨g, hg, hhom, hderiv⟩ := exists_immersion_on_compact_rel f hf hdim
    isCompact_empty hL (fun _ hx => False.elim hx) hC hdis
  exact ⟨g, hg, hhom, fun x hx => hderiv x (Or.inr hx)⟩

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
