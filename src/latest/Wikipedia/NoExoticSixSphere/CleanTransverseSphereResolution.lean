import Wikipedia.NoExoticSixSphere.GloballyCleanSphereSheetChart
import Wikipedia.NoExoticSixSphere.SphereGluedSelfTransversality
import Wikipedia.NoExoticSixSphere.SphereResolutionPinchScaleHomotopy
import Wikipedia.NoExoticSixSphere.SphereGluedDoublePointCount
import Wikipedia.NoExoticSixSphere.NativeTransverseSpherePairFiniteness

/-!
# A constructed self-transverse immersed resolution at a clean common value

The globally clean chart, positive scale, smooth immersion, self-transversality,
whole-sphere pinch homotopy, and actual double-point parity formula are
constructed from the original input maps. Uniqueness of their fibers over
the chosen common value is explicit. The frame-sum formula is not asserted.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (F G : C(Sphere 3, M))

theorem exists_clean_selfTransverse_pinch {δ : ℝ} (hδ : 0 < δ)
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    (htF : NativeSphereSelfTransverse F) (htG : NativeSphereSelfTransverse G)
    (htFG : NativeSpherePairTransverse F G)
    (hzero : F (sourceChart 0) = G (sourceChart 0))
    (hFu : ∀ x, F x = F (sourceChart 0) → x = sourceChart 0)
    (hGu : ∀ x, G x = G (sourceChart 0) → x = sourceChart 0) :
    ∃ (ε : ℝ) (hε : 0 < ε) (K : C(Sphere 3, M)),
      ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) ∧
      NativeSphereSelfTransverse K ∧
      K.Homotopic (comparisonPinch F G δ hδ.ne' hzero) ∧
      (∀ x ∈ northRegion, K x = F (sphereCap ε x)) ∧
      (∀ x ∈ southRegion, K x = G (sphereCap ε (reflectHead x))) ∧
      (∀ x y, x ≠ y → K x = K y → x ∉ neckRegion ∧ y ∉ neckRegion) ∧
      SphereSelfIntersections.unorderedParity K =
        SphereSelfIntersections.unorderedParity F + SphereSelfIntersections.unorderedParity G +
          MapIntersections.parity F G + 1 := by
  obtain ⟨b, hb, Φ, hprod, _, hleft, hright, hclean⟩ :=
    exists_globally_clean_sphere_sheetChart F G hF hG hzero hFu hGu
      (htFG (sourceChart 0) (sourceChart 0) hzero) isOpen_univ (mem_univ _)
  let ε := b / 4
  have hε : 0 < ε := div_pos hb (by norm_num)
  have he : ε * 4 = b := by dsimp [ε]; ring
  have hp : closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source := by rwa [he]
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  let K := gluedSphereMap Φ F G hε h1 hp hleft hright hF hG
  have hK : ContMDiff (𝓡 3) (𝓡 6) ∞ K :=
    contMDiff_gluedSphere Φ F G hε h1 hp hleft hright hF hG
  have hKi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x) :=
    injective_mfderiv_gluedSphere Φ F G hε hp (by norm_num : (1 : ℝ) ∈ Ioc 0 1)
      hleft hright hF hG hFi hGi
  have hKt : NativeSphereSelfTransverse K :=
    selfTransverse_gluedSphere Φ F G hε (by norm_num : (1 : ℝ) ∈ Ioc 0 1)
      hp hleft hright hclean hF hG htF htG htFG
  have H : K.Homotopic (comparisonPinch F G ε hε.ne' hzero) :=
    ⟨immersedToPinchHomotopy F G Φ hε hp hleft hright hF hG hzero⟩
  refine ⟨ε, hε, K, hK, hKi, hKt,
    H.trans (comparisonPinch_scale_homotopic F G hε hδ hzero), ?_, ?_, ?_, ?_⟩
  · exact fun x hx ↦ gluedSphere_north Φ F G hε h1 hp hleft hx
  · exact fun x hx ↦ gluedSphere_south Φ F G hε h1 hp hright hx
  · exact fun x y hne heq ↦
      gluedSphere_doublePoints_outside_neck Φ hε (by norm_num : (0 : ℝ) < 1)
        hp F G hclean hne heq
  · have hfinF := SphereSelfIntersections.finite_pairs hF
      ((nativeSphereSelfTransverse_iff F).mp htF) hFi
    have hfinG := SphereSelfIntersections.finite_pairs hG
      ((nativeSphereSelfTransverse_iff G).mp htG) hGi
    have hfinFG := MapIntersections.finite_pairs_of_nativeTransverse hF hG htFG
    exact gluedSphere_unorderedParity F G Φ hε (by norm_num : (0 : ℝ) < 1)
      hp hclean hfinF hfinG hfinFG

end NoExoticSixSphere.SphereSumNeck
