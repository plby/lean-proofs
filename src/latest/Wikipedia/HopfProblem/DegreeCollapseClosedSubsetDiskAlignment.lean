import Wikipedia.HopfProblem.DegreeCollapseClosedSubsetPointMotion

/-!
# Disk alignment fixing an arbitrary closed part of a smooth image

The protected set may be the complement of a selected patch in an actual
attaching sphere. Only that closed subset is fixed; the disks themselves
may lie on the containing sphere. All support stays away from the protected
set for the entire real-time isotopy.
-/

noncomputable section

open Set Function Metric ContinuousMap
open scoped Topology ContDiff Manifold
open Wikipedia.SmoothSixDPoincare SupportedDiffeomorph

namespace Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking

variable {D E V H M Y : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
  [TopologicalSpace H] {I : ModelWithCorners ℝ V H}
  [TopologicalSpace Y] [ChartedSpace H Y] [IsManifold I ∞ Y] [SecondCountableTopology Y]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]
  [T2Space M] [CompactSpace M]

theorem exists_supported_disk_alignment_fixing_closed_subset {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0))
    (b : C(Y, M)) (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    (hclosed : IsClosed (range b)) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ E)
    {C : Set M} (hC : IsClosed C) (hCb : C ⊆ range b)
    (hfavoid : ∀ x ∈ closedBall (0 : D) 1, f x ∉ C)
    (hgavoid : ∀ x ∈ closedBall (0 : D) 1, g x ∉ C) :
    ∃ (P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ Cᶜ ∧ Nonempty (SupportedRelativeIsotopy P K C) ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, K, hK, hKC, ⟨A⟩, hP0⟩ :=
    MorseCancellation.exists_supported_point_motion_avoiding_closed_subset b hb hclosed hobdim
      hC hCb γ (hfavoid 0 (mem_closedBall_self zero_le_one))
      (hgavoid 0 (mem_closedBall_self zero_le_one))
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
  have hPfC : MapsTo (P ∘ f) (closedBall (0 : D) 1) Cᶜ :=
    (SupportedGerms.supported_isotopy_endpoint_mapsTo A hKC).comp hfavoid
  obtain ⟨Q, L, hL, hLC, ⟨B⟩, hformula⟩ := exists_supported_embedded_disk_alignment
    hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0 hC.isOpen_compl hPfC hgavoid
  let B' := MorseCancellation.supported_isotopy_fixing_set_disjoint_from_support B
    (fun z (hz : z ∈ C) hzL => hLC hzL hz)
  exact ⟨P.trans Q, K ∪ L, hK.union hL, union_subset hKC hLC,
    ⟨SupportedGerms.compose_supported_relative_isotopies A B'⟩, hformula⟩

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
