import Wikipedia.HopfProblem.DegreeCollapseSupportedPathDiskAlignment
import Wikipedia.HopfProblem.DegreeCollapseClosedImagePathAvoidance

/-!
# Whole disk alignment fixing a closed smooth obstacle

Relative general position first makes the center path avoid the entire
closed smooth obstacle. The compact support then stays in its complement,
so every real-time slice fixes every point of the original obstacle.
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

theorem exists_supported_disk_alignment_avoiding_closed_image {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0))
    (b : C(Y, M)) (hb : ContMDiff I 𝓘(ℝ, E) ∞ b)
    (hclosed : IsClosed (range b)) (hobdim : 1 + Module.finrank ℝ V < Module.finrank ℝ E)
    (hfavoid : ∀ x ∈ closedBall (0 : D) 1, f x ∉ range b)
    (hgavoid : ∀ x ∈ closedBall (0 : D) 1, g x ∉ range b) :
    ∃ (P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞) (K : Set M),
      IsCompact K ∧ K ⊆ (range b)ᶜ ∧
      Nonempty (SupportedRelativeIsotopy P K (range b)) ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨η, -, hη⟩ := MorseCancellation.exists_smooth_path_avoiding_closed_image γ b hb
    hclosed hobdim (hfavoid 0 (mem_closedBall_self zero_le_one))
    (hgavoid 0 (mem_closedBall_self zero_le_one))
  obtain ⟨P, K, hK, hKavoid, ⟨A⟩, hformula⟩ :=
    exists_supported_embedded_disk_alignment_of_path hf hg hfi hgi hfd hgd n hn hdim hE
      hclosed.isOpen_compl hfavoid hgavoid η hη
  refine ⟨P, K, hK, hKavoid, ⟨{
    family := A.family
    smooth := A.smooth
    zero := A.zero
    one := A.one
    slices := A.slices
    fixedOutside := A.fixedOutside
    fixedOn := ?_ }⟩, hformula⟩
  intro t z hz
  exact A.fixedOutside t z (fun h => hKavoid h hz)

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
