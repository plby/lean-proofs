import Wikipedia.SmoothSixDPoincare.InnerBigonCollar
import Wikipedia.SmoothSixDPoincare.ConstructedCleanBigonBoundary

/-!
# An actual inner boundary neighborhood avoiding both full sheets

The inward affine diffeomorphism pulls the already constructed clean bigon
neighborhood back to a neighborhood of the standard bigon frontier. Its
entire image avoids both sheets, and its native embedding and immersion
properties follow from those of the original neighborhood.
-/

noncomputable section

open Set Function Topology
open scoped ContDiff Manifold

namespace Wikipedia.SmoothSixDPoincare

open WhitneyPairModel

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace M] [ChartedSpace E M]

/-- The full clean boundary yields an embedded immersive inner boundary neighborhood
whose entire image lies in the complement of both original sheets. -/
theorem CleanBigonBoundary.exists_inner_clean_neighborhood
    {S T : Set M} {a b : ℝ → M} {k l : (ℝ × ℝ) → M} {h : ℝ}
    (d : CleanBigonBoundary (E := E) S T a b k l h) :
    ∃ r : ℝ, r ∈ Ioo (0 : ℝ) 1 ∧ innerBigonCollar h r ⊆ d.domain ∧
      ∃ V : Set (ℝ × ℝ),
      IsOpen V ∧ frontier (bigon h) ⊆ V ∧
      ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞ (d.map ∘ innerBigonMap h r) V ∧
      InjOn (d.map ∘ innerBigonMap h r) V ∧
      (∀ p ∈ V, Injective
        (mfderiv 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) (d.map ∘ innerBigonMap h r) p)) ∧
      MapsTo (innerBigonMap h r) V (d.domain ∩ interior (bigon h)) ∧
      ∀ p ∈ V, d.map (innerBigonMap h r p) ∉ S ∪ T := by
  have hfrontD : frontier (bigon h) ⊆ d.domain :=
    d.boundary_covered.trans (interior_subset.trans d.neighborhood_subset)
  obtain ⟨r, hr, hcollar, hfront⟩ :=
    exists_inner_bigon_collar_in_open d.height_pos d.open_domain hfrontD
  let c := innerBigonDiffeomorph h r hr.1.ne'
  let V : Set (ℝ × ℝ) := innerBigonMap h r ⁻¹' (d.domain ∩ interior (bigon h))
  have hc : ContMDiff 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, ℝ × ℝ) ∞ (innerBigonMap h r) :=
    c.contMDiff
  have hV : IsOpen V := (d.open_domain.inter isOpen_interior).preimage hc.continuous
  have hsmooth : ContMDiffOn 𝓘(ℝ, ℝ × ℝ) 𝓘(ℝ, E) ∞
      (d.map ∘ innerBigonMap h r) V :=
    d.smooth.comp hc.contMDiffOn (fun _ hp => hp.1)
  have hinj : InjOn (d.map ∘ innerBigonMap h r) V := by
    intro p hp q hq hpq
    exact c.injective (d.injective hp.1 hq.1 hpq)
  refine ⟨r, hr, hcollar, V, hV, hfront, hsmooth, hinj, ?_, fun _ hp => hp, ?_⟩
  · intro p hp
    have hdf := (d.smooth.contMDiffAt (d.open_domain.mem_nhds hp.1)).mdifferentiableAt
      (by simp)
    rw [mfderiv_comp p hdf (hc.mdifferentiableAt (by simp))]
    exact (d.derivative_injective _ hp.1).comp
      (bijective_mfderiv_innerBigonMap h r hr.1.ne' p).injective
  · intro p hp
    exact d.interior_avoids _ hp

end Wikipedia.SmoothSixDPoincare
