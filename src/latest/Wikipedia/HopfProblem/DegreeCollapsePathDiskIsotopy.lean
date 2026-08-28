import Wikipedia.HopfProblem.DegreeCollapseEmbeddedDiskAlignment
import Wikipedia.HopfProblem.DegreeCollapsePathPointIsotopy

/-!
# Ambient isotopy of embedded disks whose centers are joined by a path

An actual native point-moving isotopy first aligns the centers. Constructed
tubular neighborhoods, normal determinant correction, and disk compression
then identify the entire parametrized closed disks by an ambient isotopy.
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

theorem exists_embedded_disk_isotopy_of_path {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) (γ : Path (f 0) (g 0)) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, IsotopicToIdentity P ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x := by
  obtain ⟨P, hP, hP0, -⟩ := MorseCancellation.exists_isotopic_pointMoving_of_path
    (J := 𝓘(ℝ, E)) isOpen_univ γ (fun _ => mem_univ _)
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
  obtain ⟨Q, hQ, hformula⟩ := exists_embedded_disk_isotopy_of_same_center
    hPf hg hPfi hgi hPfd hgd n hn hdim hE hP0
  exact ⟨P.trans Q, hP.trans hQ, hformula⟩

theorem exists_embedded_disk_isotopy [PathConnectedSpace M] {f g : D → M}
    (hf : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ f)
    (hg : ContMDiff 𝓘(ℝ, D) 𝓘(ℝ, E) ∞ g)
    (hfi : InjOn f (closedBall (0 : D) 1)) (hgi : InjOn g (closedBall (0 : D) 1))
    (hfd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) f x))
    (hgd : ∀ x ∈ closedBall (0 : D) 1, Injective (mfderiv 𝓘(ℝ, D) 𝓘(ℝ, E) g x))
    (n : ℕ) (hn : 0 < n) (hdim : Module.finrank ℝ D + n = Module.finrank ℝ E)
    (hE : 2 ≤ Module.finrank ℝ E) :
    ∃ P : Diffeomorph 𝓘(ℝ, E) 𝓘(ℝ, E) M M ∞, IsotopicToIdentity P ∧
      ∀ x ∈ closedBall (0 : D) 1, P (f x) = g x :=
  exists_embedded_disk_isotopy_of_path hf hg hfi hgi hfd hgd n hn hdim hE
    (Joined.somePath (PathConnectedSpace.joined (f 0) (g 0)))

end Wikipedia.HopfProblem.DegreeCollapse.DiskShrinking
