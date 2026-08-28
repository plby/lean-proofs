import Wikipedia.NoExoticSixSphere.WhitneySphereFrameValue

/-!
# The Whitney reference fits in any prescribed positive chart product

An actual linear dilation rescales the chart. The previously computed frame
obstruction therefore applies to the original map `x ↦ Φ (ε • W x)` at every
positive scale for which the closed product lies in the retained chart.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.WhitneySphere

open GLOrthonormalization

def dilation (ε : ℝ) (hε : 0 < ε) :
    (Vector 3 × Vector 3) ≃L[ℝ] (Vector 3 × Vector 3) :=
  ContinuousLinearEquiv.smulLeft (R₁ := ℝ) (M₁ := Vector 3 × Vector 3) (Units.mk0 ε hε.ne')

theorem dilation_apply (ε : ℝ) (hε : 0 < ε) (z : Vector 3 × Vector 3) :
    dilation ε hε z = ε • z := rfl

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

def scaledChart (ε : ℝ) (hε : 0 < ε) :
    PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6) (Vector 3 × Vector 3) M ∞ :=
  (dilation ε hε).toDiffeomorph.toPartialDiffeomorph.trans Φ

theorem scaledChart_apply (ε : ℝ) (hε : 0 < ε) (z : Vector 3 × Vector 3) :
    scaledChart Φ ε hε z = Φ (ε • z) := rfl

theorem unitProduct_subset_scaledChart_source {ε : ℝ} (hε : 0 < ε)
    (hprod : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source) :
    closedBall (0 : Vector 3) 1 ×ˢ closedBall (0 : Vector 3) 1 ⊆
      (scaledChart Φ ε hε).source := by
  intro z hz
  refine ⟨mem_univ _, hprod ⟨?_, ?_⟩⟩
  · change ε • z.1 ∈ closedBall (0 : Vector 3) ε
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hz1 : ‖z.1‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz.1
    nlinarith
  · change ε • z.2 ∈ closedBall (0 : Vector 3) ε
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hε]
    have hz2 : ‖z.2‖ ≤ 1 := by simpa only [mem_closedBall, dist_zero_right] using hz.2
    nlinarith

theorem chartMap_scaledChart (ε : ℝ) (hε : 0 < ε) :
    chartMap (scaledChart Φ ε hε) = fun x ↦ Φ (ε • map x) := rfl

end NoExoticSixSphere.WhitneySphere

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization WhitneySphere

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (a : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)

include r in
theorem immersedSphereFrameParity_scaledWhitney {ε : ℝ} (hε : 0 < ε)
    (hprod : closedBall (0 : Vector 3) ε ×ˢ closedBall (0 : Vector 3) ε ⊆ Φ.source) :
    e.immersedSphereFrameParity a (fun x ↦ Φ (ε • WhitneySphere.map x))
      (contMDiff_chartMap (scaledChart Φ ε hε)
        (unitProduct_subset_scaledChart_source Φ hε hprod))
      (injective_mfderiv_chartMap (scaledChart Φ ε hε)
        (unitProduct_subset_scaledChart_source Φ hε hprod)) = 1 :=
  e.immersedSphereFrameParity_whitney a r (scaledChart Φ ε hε)
    (unitProduct_subset_scaledChart_source Φ hε hprod)

end NoExoticSixSphere.EuclideanEmbedding
