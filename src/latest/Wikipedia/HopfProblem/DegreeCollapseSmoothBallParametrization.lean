import Wikipedia.HopfProblem.DegreeCollapseBasinSmoothImages
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Global smooth parametrizations of open coordinate balls

A continuous linear projection from a sufficiently large Euclidean model
is surjective onto the given finite-dimensional space. The standard smooth
ball diffeomorphism then parametrizes the entire positive-radius ball.
Consequently a map smooth only on that ball has the same image as an actual
globally smooth map from the chosen common Euclidean model.
-/

noncomputable section

open Set Function Filter Metric Manifold
open scoped ContDiff Topology

namespace Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [FiniteDimensional ℝ V]

theorem exists_smooth_ball_parametrization {d : ℕ} (hd : Module.finrank ℝ V ≤ d)
    {r : ℝ} (hr : 0 < r) :
    ∃ ψ : EuclideanSpace ℝ (Fin d) → V, ContDiff ℝ ∞ ψ ∧ range ψ = ball 0 r := by
  let W := EuclideanSpace ℝ (Fin (d - Module.finrank ℝ V))
  let L : EuclideanSpace ℝ (Fin d) ≃L[ℝ] (V × W) :=
    ContinuousLinearEquiv.ofFinrankEq (by
      simp only [Module.finrank_prod, finrank_euclideanSpace_fin, W]
      omega)
  let π : EuclideanSpace ℝ (Fin d) →L[ℝ] V :=
    (ContinuousLinearMap.fst ℝ V W).comp L.toContinuousLinearMap
  have hπ : Surjective π := by
    intro v
    refine ⟨L.symm (v, 0), ?_⟩
    change (L (L.symm (v, 0))).1 = v
    rw [L.apply_symm_apply]
  let B := OpenPartialHomeomorph.univBall (0 : V) r
  let ψ : EuclideanSpace ℝ (Fin d) → V := B ∘ π
  have hψ : ContDiff ℝ ∞ ψ := OpenPartialHomeomorph.contDiff_univBall.comp π.contDiff
  refine ⟨ψ, hψ, ?_⟩
  ext v
  constructor
  · rintro ⟨z, rfl⟩
    have hm : π z ∈ B.source := by rw [OpenPartialHomeomorph.univBall_source]; trivial
    have hh := B.map_source hm
    rwa [OpenPartialHomeomorph.univBall_target _ hr] at hh
  · intro hv
    have hvt : v ∈ B.target := by rw [OpenPartialHomeomorph.univBall_target _ hr]; exact hv
    obtain ⟨z, hz⟩ := hπ (B.symm v)
    refine ⟨z, ?_⟩
    change B (π z) = v
    rw [hz]
    exact B.right_inv hvt

theorem exists_global_smooth_image_of_ball
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M]
    {d : ℕ} (hd : Module.finrank ℝ V ≤ d) {r : ℝ} (hr : 0 < r)
    {f : V → M} (hf : ContMDiffOn 𝓘(ℝ, V) I ∞ f (ball 0 r)) :
    ∃ g : EuclideanSpace ℝ (Fin d) → M, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) I ∞ g ∧
      range g = f '' ball 0 r := by
  obtain ⟨ψ, hψ, hrange⟩ := exists_smooth_ball_parametrization hd hr
  refine ⟨f ∘ ψ, ?_, ?_⟩
  · intro x
    have hx : ψ x ∈ ball (0 : V) r := hrange ▸ mem_range_self x
    exact (hf.contMDiffAt (isOpen_ball.mem_nhds hx)).comp x hψ.contMDiff.contMDiffAt
  · rw [range_comp, hrange]

end Wikipedia.HopfProblem.DegreeCollapse.MorseCancellation
