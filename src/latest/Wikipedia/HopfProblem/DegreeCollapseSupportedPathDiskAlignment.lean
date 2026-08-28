import Wikipedia.HopfProblem.DegreeCollapseSupportedEmbeddedDiskAlignment
import Wikipedia.HopfProblem.DegreeCollapseSupportedPathPointMotion

/-!
# Entire embedded disks can be aligned with support in an open path region

Supported point motion aligns the centers without leaving the prescribed
region. Whole disk alignment then uses tubular charts contained in that
same region. All slices fix the complement of one compact subset of it.
-/

noncomputable section

open Set Function Metric
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D E M : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_supported_embedded_disk_alignment_of_path {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) {U : Set M} (hU : IsOpen U)
    (hfU : MapsTo f (closedBall (0 : D) 1) U)
    (hgU : MapsTo g (closedBall (0 : D) 1) U)
    (γ : Path (f 0) (g 0)) (hγ : ∀ t, γ t ∈ U) :
    ∃ (P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ U ∧ Nonempty (SupportedRelativeIsotopy P K ∅) ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, K, hK, hKU, ⟨A⟩, hP0⟩ :=
    MorseCancellation.exists_compactly_supported_point_motion_of_path
      (J := 𝓘(ℝ, E)) hU γ hγ
  have hPf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ (P ∘ f) := P.contMDiff.comp hf
  have hPfi : InjOn (P ∘ f) (closedBall (0 : D) 1) := by
    intro x hx y hy hh
    exact hfi hx hy (P.injective hh)
  have hPfd : ∀ x ∈ closedBall (0 : D) 1,
      Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) (P ∘ f) x) := by
    intro x hx
    rw [mfderiv_comp x (P.contMDiff.mdifferentiableAt (by simp))
      (hf.mdifferentiableAt (by simp))]
    have hi : Bijective (mfderiv 𝓘(ℝ, E) 𝓘(ℝ, E) P (f x) : E →L[ℝ] E) :=
      PartialChart.bijective_mfderiv P.toPartialDiffeomorph (mem_univ _)
    exact hi.1.comp (hfd x hx)
  have hPfU : MapsTo (P ∘ f) (closedBall (0 : D) 1) U :=
    (SupportedGerms.supported_isotopy_endpoint_mapsTo A hKU).comp hfU
  obtain ⟨Q, L, hL, hLU, ⟨B⟩, hformula⟩ := exists_supported_embedded_disk_alignment
    hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0 hU hPfU hgU
  exact ⟨P.trans Q, K ∪ L, hK.union hL, union_subset hKU hLU,
    ⟨SupportedGerms.compose_supported_relative_isotopies A
      (SupportedGerms.weaken_supported_relative_isotopy B Subset.rfl (empty_subset _))⟩,
    hformula⟩

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
