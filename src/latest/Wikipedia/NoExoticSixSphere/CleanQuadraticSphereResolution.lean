import Wikipedia.NoExoticSixSphere.SmallResolutionFrameSum

/-!
# A constructed clean resolution with the corrected quadratic parity formula

The geometric chart radius and the proved frame-comparison threshold have
a common positive scale. At that scale, the frame formula and the actual
double-point count have matching extra ones, which cancel in corrected
parity. The result retains the original pinch homotopy. Preparation of
arbitrary sphere classes with the unique-center-fiber hypotheses remains
a separate requirement.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.EuclideanEmbedding

open GLOrthonormalization SphereSumNeck

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (e : EuclideanEmbedding 6 M)
  (ν : SmoothRangeFrame (𝓡 6) e.normalProjection e.NormalModel) (r : TubularRetraction e)
  (F G : C(Sphere 3, M))
  (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
  (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
  (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
  (htF : NativeSphereSelfTransverse F) (htG : NativeSphereSelfTransverse G)
  (htFG : NativeSpherePairTransverse F G)
  (hzero : F (sourceChart 0) = G (sourceChart 0))
  (hFu : ∀ x, F x = F (sourceChart 0) → x = sourceChart 0)
  (hGu : ∀ x, G x = G (sourceChart 0) → x = sourceChart 0)

include r htF htG htFG hFu hGu in
theorem exists_clean_quadratic_resolution {τ : ℝ} (hτ : 0 < τ) :
    ∃ (K : C(Sphere 3, M)) (hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K)
      (hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)),
      NativeSphereSelfTransverse K ∧
      K.Homotopic (comparisonPinch F G τ hτ.ne' hzero) ∧
      e.immersedSphereCorrectedParity ν K hK hKi =
        e.immersedSphereCorrectedParity ν F hF hFi +
          e.immersedSphereCorrectedParity ν G hG hGi + MapIntersections.parity F G := by
  obtain ⟨b, hb, Θ, hbΘ, _, hleft, hright, hclean⟩ :=
    exists_globally_clean_sphere_sheetChart F G hF hG hzero hFu hGu
      (htFG (sourceChart 0) (sourceChart 0) hzero) isOpen_univ (mem_univ _)
  have h0 : (0 : Vector 3 × Vector 3) ∈ Θ.source :=
    hbΘ ⟨mem_closedBall_self hb.le, mem_closedBall_self hb.le⟩
  obtain ⟨δ, hδ, hframe⟩ :=
    e.exists_small_resolution_frame_sum ν r Θ F G hF hG hFi hGi hleft hright h0
  let ε := min (b / 4) δ
  have hε : 0 < ε := lt_min (div_pos hb (by norm_num)) hδ
  have hεb : ε * 4 ≤ b := by
    have h := min_le_left (b / 4) δ
    dsimp only [ε]
    linarith
  have hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4) ⊆ Θ.source := by
    intro p hp
    exact hbΘ ⟨closedBall_subset_closedBall hεb hp.1, closedBall_subset_closedBall hεb hp.2⟩
  have h1 : (1 : ℝ) ∈ Ioc 0 1 := by norm_num
  let K := gluedSphereMap Θ F G hε ⟨h1.1.le, h1.2⟩ hprod hleft hright hF hG
  have hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K :=
    contMDiff_gluedSphere Θ F G hε ⟨h1.1.le, h1.2⟩ hprod hleft hright hF hG
  have hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x) :=
    injective_mfderiv_gluedSphere Θ F G hε hprod h1 hleft hright hF hG hFi hGi
  have hKt : NativeSphereSelfTransverse K :=
    selfTransverse_gluedSphere Θ F G hε h1 hprod hleft hright hclean hF hG htF htG htFG
  have H : K.Homotopic (comparisonPinch F G τ hτ.ne' hzero) :=
    (show K.Homotopic (comparisonPinch F G ε hε.ne' hzero) from
      ⟨immersedToPinchHomotopy F G Θ hε hprod hleft hright hF hG hzero⟩).trans
        (comparisonPinch_scale_homotopic F G hε hτ hzero)
  have hKF : e.immersedSphereFrameParity ν K hK hKi =
      e.immersedSphereFrameParity ν F hF hFi + e.immersedSphereFrameParity ν G hG hGi + 1 :=
    hframe ε hε (min_le_right _ _) 1 h1 hprod
  have hfinF := SphereSelfIntersections.finite_pairs hF
    ((nativeSphereSelfTransverse_iff F).mp htF) hFi
  have hfinG := SphereSelfIntersections.finite_pairs hG
    ((nativeSphereSelfTransverse_iff G).mp htG) hGi
  have hfinFG := MapIntersections.finite_pairs_of_nativeTransverse hF hG htFG
  have hcount : SphereSelfIntersections.unorderedParity K =
      SphereSelfIntersections.unorderedParity F + SphereSelfIntersections.unorderedParity G +
        MapIntersections.parity F G + 1 :=
    gluedSphere_unorderedParity F G Θ hε h1.1 hprod hclean hfinF hfinG hfinFG
  refine ⟨K, hK, hKi, hKt, H, ?_⟩
  unfold immersedSphereCorrectedParity
  rw [hKF, hcount]
  calc
    _ = (e.immersedSphereFrameParity ν F hF hFi + SphereSelfIntersections.unorderedParity F) +
        (e.immersedSphereFrameParity ν G hG hGi + SphereSelfIntersections.unorderedParity G) +
          MapIntersections.parity F G + ((1 : ZMod 2) + 1) := by abel
    _ = _ := by rw [ZModModule.add_self, add_zero]

include hF hG hFi hGi htF htG htFG hFu hGu in
theorem geometricSphereParity_comparisonPinch {τ : ℝ} (hτ : 0 < τ) :
    e.geometricSphereParity ν r (comparisonPinch F G τ hτ.ne' hzero) =
      e.geometricSphereParity ν r F + e.geometricSphereParity ν r G +
        MapIntersections.parity F G := by
  obtain ⟨K, hK, hKi, hKt, H, hq⟩ :=
    e.exists_clean_quadratic_resolution ν r F G hF hG hFi hGi htF htG htFG hzero hFu hGu hτ
  have hpinch := e.geometricSphereParity_eq_representative ν r
    (comparisonPinch F G τ hτ.ne' hzero) K hK hKi
    ((nativeSphereSelfTransverse_iff K).mp hKt) H.symm
  have hrepF := e.geometricSphereParity_eq_representative ν r F F hF hFi
    ((nativeSphereSelfTransverse_iff F).mp htF) (ContinuousMap.Homotopic.refl F)
  have hrepG := e.geometricSphereParity_eq_representative ν r G G hG hGi
    ((nativeSphereSelfTransverse_iff G).mp htG) (ContinuousMap.Homotopic.refl G)
  rw [hpinch, hq, hrepF, hrepG]

end NoExoticSixSphere.EuclideanEmbedding
