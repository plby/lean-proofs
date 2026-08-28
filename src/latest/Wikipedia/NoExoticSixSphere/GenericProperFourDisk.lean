import Wikipedia.NoExoticSixSphere.CompactRetractionInteriorControl
import Wikipedia.NoExoticSixSphere.CompactRetractionProtectedDerivative
import Mathlib.Analysis.Calculus.BumpFunction.Basic

/-!
# Generic four-disks retaining the original collar and strict interior

The actual source cutoff is supported in a smaller ball. One small parameter
both preserves the open target condition on the whole disk interior and has
generic jets in every chart of the original seven-manifold. The compact-image
submersive retraction is constructed, not assumed, and no global compactness
of the target is required. The same map has regular off-diagonal double
points when at least one source point is inside the cutoff support.
No double-point parity is asserted.
-/

noncomputable section

open Set Function Filter Metric
open scoped Manifold ContDiff Topology

namespace NoExoticSixSphere.GenericFourDisk

open GLOrthonormalization EuclideanEmbedding CompactRetractionAffineFamily

def cutoff (ρ : ℝ) (hρ : 0 < ρ) : ContDiffBump (0 : Vector 4) where
  rIn := ρ / 2
  rOut := ρ
  rIn_pos := by linarith
  rIn_lt_rOut := by linarith

theorem cutoff_ne_zero_iff (ρ : ℝ) (hρ : 0 < ρ) (x : Vector 4) :
    cutoff ρ hρ x ≠ 0 ↔ ‖x‖ < ρ := by
  change x ∈ support (cutoff ρ hρ) ↔ _
  rw [(cutoff ρ hρ).support_eq]
  exact mem_ball_zero_iff

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 7) M]
  [IsManifold (𝓡 7) ∞ M] (e : EuclideanEmbedding 7 M)

include e in
theorem exists_relative (f : Vector 4 → M)
    (hf : ∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ f x)
    (ρ : ℝ) (hρ : 0 < ρ) (hρ1 : ρ < 1)
    (V : Set M) (hV : IsOpen V) (hfV : ∀ x ∈ ball 0 1, f x ∈ V) :
    ∃ g : Vector 4 → M,
      (∀ x ∈ closedBall 0 1, ContMDiffAt (𝓡 4) (𝓡 7) ∞ g x) ∧
      (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ → g x = f x) ∧
      (∀ x ∈ closedBall 0 1, ρ ≤ ‖x‖ →
        fderiv ℝ (e.toFun ∘ g) x = fderiv ℝ (e.toFun ∘ f) x) ∧
      (∀ x ∈ ball 0 1, g x ∈ V) ∧
      ∃ C : Set (PartialDiffeomorph (𝓡 7) (𝓡 7) M (Vector 7) ∞),
        C.Countable ∧ (∀ y : M, ∃ c ∈ C, y ∈ c.source) ∧
        (∀ c ∈ C, OperatorRank.RegularFourSevenOn
          (fun x ↦ fderiv ℝ (c ∘ g) x) {x | ‖x‖ < ρ ∧ g x ∈ c.source}) ∧
        RegularDoublePointsOn g (ball 0 1) (ball 0 ρ) C := by
  let : Nonempty M := ⟨f 0⟩
  have hcont : ContinuousOn f (closedBall (0 : Vector 4) 1) :=
    fun x hx ↦ (hf x hx).continuousAt.continuousWithinAt
  obtain ⟨r⟩ := e.nonempty_retractionNear
    ((isCompact_closedBall (0 : Vector 4) 1).image_of_continuousOn hcont)
  have hb : ∀ x ∈ closedBall (0 : Vector 4) 1, f x ∈ r.base :=
    fun x hx ↦ r.covers ⟨x, hx, rfl⟩
  let χ := cutoff ρ hρ
  have hχ : ContDiff ℝ ∞ (χ : Vector 4 → ℝ) := χ.contDiff
  have hzero (x : Vector 4) (hx : ρ ≤ ‖x‖) : χ x = 0 :=
    χ.zero_of_le_dist (by simpa only [χ, cutoff, dist_zero_right] using hx)
  let U : TopologicalSpace.Opens (Vector 4) := ⟨ball 0 1, isOpen_ball⟩
  let A : Set (Parameters 4 e) := {p | ∀ x ∈ ball 0 1, map e r f χ p x ∈ V}
  have hA : A ∈ 𝓝 (0 : Parameters 4 e) :=
    eventually_map_disk_interior e r f χ ρ hρ1 hf hχ hzero hb V hV hfV
  obtain ⟨C, p, hC, hcov, -, hpV, hpdom, hps, hpeq, hgen⟩ :=
    exists_small_regular_on_compact_mem e r f χ (isCompact_closedBall (0 : Vector 4) 1)
      hf hχ hb U ball_subset_closedBall rfl rfl A hA (by norm_num : (0 : ℝ) < 1)
  let g := map e r f χ p
  refine ⟨g, hps, ?_, ?_, hpV, C, hC, hcov, ?_, ?_⟩
  · intro x hx hxρ
    exact hpeq x hx (hzero x hxρ)
  · intro x hx hxρ
    exact fderiv_embedded_map_of_zero_cutoff e r f χ p x (hf x hx)
      hχ.contDiffAt χ.nonneg' (hzero x hxρ) (hb x hx)
  · intro c hc
    have he : {x | (p, x) ∈ activeChartDomain e r f χ U
        (fun x hx ↦ (hf x (ball_subset_closedBall hx)).contMDiffWithinAt) hχ c} =
        {x | ‖x‖ < ρ ∧ g x ∈ c.source} := by
      ext x
      constructor
      · rintro ⟨⟨⟨hxU, hxdom⟩, hxc⟩, hχx⟩
        exact ⟨(cutoff_ne_zero_iff ρ hρ x).mp hχx, hxc⟩
      · rintro ⟨hxρ, hxc⟩
        have hx : x ∈ ball (0 : Vector 4) 1 := mem_ball_zero_iff.mpr (hxρ.trans hρ1)
        exact ⟨⟨⟨hx, hpdom x (ball_subset_closedBall hx)⟩, hxc⟩,
          (cutoff_ne_zero_iff ρ hρ x).mpr hxρ⟩
    have hg := hgen.1 c hc
    rw [he] at hg
    exact hg
  · have ha : {x : Vector 4 | χ x ≠ 0} = ball 0 ρ := by
      ext x
      exact (cutoff_ne_zero_iff ρ hρ x).trans mem_ball_zero_iff.symm
    change RegularDoublePointsOn (map e r f χ p) U (ball 0 ρ) C
    rw [← ha]
    exact hgen.2

end NoExoticSixSphere.GenericFourDisk
