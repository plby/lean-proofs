import Wikipedia.NoExoticSixSphere.DiskCollarAmbientExtension
import Wikipedia.NoExoticSixSphere.CompactRelativeManifoldSmoothing
import Mathlib.Analysis.Calculus.TangentCone.Real

/-!
# Smooth disk extensions preserving an actual collar and interior avoidance

The target can be noncompact. Smoothing fixes the outer quarter-annulus
of the original disk and keeps every interior point in a specified open
target region. The ambient boundary derivative is exactly that of the
prescribed collar, by uniqueness of derivatives within the closed ball.
No interior immersion is inferred from this approximation.
-/

noncomputable section

open Set Metric Filter
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization
open Wikipedia.HopfProblem.DegreeCollapse.DiskCylinder

variable {n p : ℕ} {M : Type*} [TopologicalSpace M]
  [ChartedSpace (Vector n) M] [IsManifold (𝓡 n) ∞ M] [Nonempty M]
  (e : EuclideanEmbedding n M)

theorem exists_smooth_disk_with_collar (G : C(Disk (E := Vector (p + 1)), M))
    (H : C(Vector (p + 1), Vector e.ambientDimension)) (hH : ContDiff ℝ ∞ H)
    (hHG : ∀ x : Disk (E := Vector (p + 1)), 1 / 2 ≤ ‖x.val‖ → H x.val = e.toFun (G x))
    (V : Set M) (hV : IsOpen V) (hGV : ∀ x, ‖x.val‖ < 1 → G x ∈ V) :
    ∃ g : Vector (p + 1) → M,
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ g x) ∧
      (∀ x : Disk (E := Vector (p + 1)), 3 / 4 ≤ ‖x.val‖ → g x.val = G x) ∧
      ∀ x ∈ ball 0 1, g x ∈ V := by
  let A : C(Disk (E := Vector (p + 1)), Vector e.ambientDimension) :=
    ⟨e.toFun ∘ G, e.smooth.continuous.comp G.continuous⟩
  obtain ⟨B, hBG, hBH⟩ := DiskCollarAmbientExtension.exists_extension A H hHG
  let S : Set (Vector (p + 1)) := {x | 3 / 4 ≤ ‖x‖}
  let U : Set (Vector (p + 1)) := {x | 2 / 3 < ‖x‖}
  have hS : IsClosed S := isClosed_le continuous_const continuous_norm
  have hU : IsOpen U := isOpen_lt continuous_const continuous_norm
  have hSU : S ⊆ U := by
    intro x hx
    change 3 / 4 ≤ ‖x‖ at hx
    change 2 / 3 < ‖x‖
    linarith
  have hBs : ContDiffOn ℝ ∞ B U :=
    hH.contDiffOn.congr (fun x hx ↦ hBH x hx.le)
  obtain ⟨g, hgs, hgeq, hgV⟩ := e.exists_smooth_near_compact_relative
    (isCompact_closedBall (0 : Vector (p + 1)) 1)
    (isCompact_closedBall (0 : Vector (p + 1)) (3 / 4))
    (closedBall_subset_closedBall (by norm_num : (3 / 4 : ℝ) ≤ 1))
    G B hBG hS (hU.mem_nhdsSet.mpr hSU) hBs V hV (fun x hx ↦
      hGV x ((mem_closedBall_zero_iff.mp hx).trans_lt (by norm_num)))
  refine ⟨g, hgs, hgeq, ?_⟩
  intro x hx
  have hx' : ‖x‖ < 1 := mem_ball_zero_iff.mp hx
  by_cases hinner : ‖x‖ ≤ 3 / 4
  · exact hgV x (mem_closedBall_zero_iff.mpr hinner)
  · have hxe : g x = G ⟨x, mem_closedBall_zero_iff.mpr hx'.le⟩ :=
      hgeq ⟨x, mem_closedBall_zero_iff.mpr hx'.le⟩ (le_of_not_ge hinner)
    rw [hxe]
    exact hGV _ hx'

omit [IsManifold (𝓡 n) ∞ M] [Nonempty M] in
theorem fderiv_eq_disk_collar (G : C(Disk (E := Vector (p + 1)), M))
    (H : Vector (p + 1) → Vector e.ambientDimension) (hH : ContDiff ℝ ∞ H)
    (hHG : ∀ x : Disk (E := Vector (p + 1)), 1 / 2 ≤ ‖x.val‖ → H x.val = e.toFun (G x))
    (g : Vector (p + 1) → M)
    (hgs : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 (p + 1)) (𝓡 n) ∞ g x)
    (hgeq : ∀ x : Disk (E := Vector (p + 1)), 3 / 4 ≤ ‖x.val‖ → g x.val = G x)
    (q : NoExoticSixSphere.Sphere p) :
    fderiv ℝ (e.toFun ∘ g) q.val = fderiv ℝ H q.val := by
  have hq : q.val ∈ closedBall (0 : Vector (p + 1)) 1 := sphere_subset_closedBall q.property
  have he : (e.toFun ∘ g) =ᶠ[𝓝[closedBall 0 1] q.val] H := by
    have hnorm : (3 / 4 : ℝ) < ‖q.val‖ := by rw [ClosedHemisphere.unit_norm]; norm_num
    filter_upwards [self_mem_nhdsWithin,
      nhdsWithin_le_nhds ((isOpen_lt continuous_const continuous_norm).mem_nhds hnorm)]
      with x hx hn
    change e.toFun (g x) = H x
    rw [hgeq ⟨x, hx⟩ hn.le]
    exact (hHG ⟨x, hx⟩ (by change 1 / 2 ≤ ‖x‖; linarith)).symm
  have hdiff : DifferentiableAt ℝ (e.toFun ∘ g) q.val :=
    ((e.smooth.contMDiffAt.comp q.val (hgs q.val hq)).contDiffAt).differentiableAt (by simp)
  have hother := ((hH.differentiable (by simp) q.val).hasFDerivAt.hasFDerivWithinAt
    (s := closedBall (0 : Vector (p + 1)) 1)).congr_of_eventuallyEq he
      (he.eq_of_nhdsWithin hq)
  have hu : UniqueDiffOn ℝ (closedBall (0 : Vector (p + 1)) 1) := by
    apply uniqueDiffOn_convex (convex_closedBall _ _)
    exact ⟨0, interior_maximal ball_subset_closedBall isOpen_ball (mem_ball_self zero_lt_one)⟩
  exact (hu q.val hq).eq hdiff.hasFDerivAt.hasFDerivWithinAt hother

end NoExoticSixSphere.EuclideanEmbedding
