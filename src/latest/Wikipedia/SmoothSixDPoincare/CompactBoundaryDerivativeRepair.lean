import Wikipedia.SmoothSixDPoincare.FiniteBoundaryDerivativeRepair
import Wikipedia.SmoothSixDPoincare.GlobalMapSmoothing

/-!
# Constructed boundary derivative repair on a compact smooth locus

All target charts, cutoffs, compact patch sets, and finite covers are chosen
from the original smooth map. Only the tangent common-kernel condition on
the defining zero set is assumed. The repaired map is immersive along the
entire compact locus and is homotopic to the old map with that zero set fixed.
-/

noncomputable section

open Set Filter ContinuousMap
open scoped ContDiff Manifold Topology

namespace Wikipedia.SmoothSixDPoincare.ManifoldImmersion

open ManifoldSmoothing (MapSmoothingPatch)

variable {B E G H H' X N : Type*}
  [NormedAddCommGroup B] [NormedSpace ℝ B] [FiniteDimensional ℝ B]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G] [FiniteDimensional ℝ G]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ B H} {J : ModelWithCorners ℝ G H'} [J.Boundaryless]
  [TopologicalSpace X] [ChartedSpace H X] [IsManifold I ∞ X]
  [CompactSpace X] [LindelofSpace (X × E)]
  [TopologicalSpace N] [ChartedSpace H' N] [IsManifold J ∞ N]

/-- A compact smooth locus in the defining zero set can be made immersive without moving
any value on that zero set. No chart, perturbation, or collar data are assumed. -/
theorem exists_compact_boundary_derivative_repair (f : C(E, N))
    (hf : ContMDiff 𝓘(ℝ, E) J ∞ f) {b : X → E} (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    {ρ : E → ℝ} (hρ : ContDiff ℝ ∞ ρ) (hzero : ∀ x, ρ (b x) = 0)
    (hdim : Module.finrank ℝ B + Module.finrank ℝ E < Module.finrank ℝ G)
    (hcommon : ∀ y, ρ y = 0 → ∀ v, mfderiv 𝓘(ℝ, E) J f y v = 0 →
      fderiv ℝ ρ y v = 0 → v = 0) :
    ∃ g : C(E, N), ContMDiff 𝓘(ℝ, E) J ∞ g ∧ f.HomotopicRel g {y | ρ y = 0} ∧
      ∀ y ∈ range b, Function.Injective (mfderiv 𝓘(ℝ, E) J g y) := by
  classical
  have hboundary : IsCompact (range b) := isCompact_range hb.continuous
  have hp (x : range b) :
      ∃ p : MapSmoothingPatch 𝓘(ℝ, E) J (X := E) (N := N), ∃ D : Set E,
        p.Compatible f ∧ IsCompact D ∧ D ∈ 𝓝 x.1 ∧ D ⊆ p.plateau := by
    obtain ⟨p, hcompatible, hplateau⟩ :=
      ManifoldSmoothing.exists_smoothing_patch_at (I := 𝓘(ℝ, E)) (J := J) f x.1
    obtain ⟨D, hDx, hDsub, hD⟩ := local_compact_nhds (isOpen_interior.mem_nhds hplateau)
    exact ⟨p, D, hcompatible, hD, hDx, hDsub⟩
  choose p D hcompatible hD hn hsub using hp
  have hcover : range b ⊆ ⋃ x : range b, interior (D x) := by
    intro x hx
    exact mem_iUnion.mpr ⟨⟨x, hx⟩, mem_interior_iff_mem_nhds.mpr (hn ⟨x, hx⟩)⟩
  obtain ⟨s, hs⟩ := hboundary.elim_finite_subcover (fun x : range b => interior (D x))
    (fun _ => isOpen_interior) hcover
  let L (i : s) := range b ∩ D i.1
  have hL (i : s) : IsCompact (L i) := hboundary.inter_right (hD i.1).isClosed
  have hLsub (i : s) : L i ⊆ (p i.1).plateau := fun _ hx => hsub i.1 hx.2
  have hLrange (i : s) : L i ⊆ range b := inter_subset_left
  obtain ⟨g, hg, -, hhom, -, hinj⟩ := exists_finite_boundary_derivative_repair
    (fun i : s => p i.1) L hL hLsub f hf (fun i => hcompatible i.1) hb hLrange hρ hzero hdim
    isCompact_empty (fun _ hx => False.elim hx) hcommon Finset.univ
  refine ⟨g, hg, hhom, ?_⟩
  intro y hy
  obtain ⟨i, hi, hyD⟩ := mem_iUnion₂.mp (hs hy)
  apply hinj y
  exact Or.inr (mem_iUnion₂.mpr ⟨⟨i, hi⟩, Finset.mem_univ _, hy, interior_subset hyD⟩)

end Wikipedia.SmoothSixDPoincare.ManifoldImmersion
