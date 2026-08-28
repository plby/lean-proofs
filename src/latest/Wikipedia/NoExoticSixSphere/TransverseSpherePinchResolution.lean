import Wikipedia.NoExoticSixSphere.SphereResolutionPinchComparison
import Wikipedia.NoExoticSixSphere.TransverseSphereResolution

/-!
# A constructed immersive representative of the explicit reparametrized pinch

The native transverse sphere maps supply the simultaneous target chart,
scale, global immersion, and whole-sphere pinch homotopy. Both input
reparametrizations, including the southern reflection, remain explicit.
This does not assume global branch separation or a double-point formula.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]
  (F G : C(Sphere 3, M))

theorem exists_immersed_reparametrized_pinch
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    (hzero : F (sourceChart 0) = G (sourceChart 0))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    ∃ (ε : ℝ) (hε : 0 < ε) (K : C(Sphere 3, M)),
      ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) ∧
      K.Homotopic (comparisonPinch F G ε hε.ne' hzero) ∧
      (∀ x ∈ northRegion, K x = F (sphereCap ε x)) ∧
      (∀ x ∈ southRegion, K x = G (sphereCap ε (reflectHead x))) := by
  have hf := hF.comp contMDiff_sourceChart
  have hg := hG.comp contMDiff_sourceChart
  have hdim : Module.finrank ℝ (Vector 3) + Module.finrank ℝ (Vector 3) =
      Module.finrank ℝ (Vector 6) := by simp
  obtain ⟨b, hb, Φ, hprod, _, _, hleft, hright⟩ :=
    Wikipedia.SmoothSixDPoincare.exists_simultaneous_sheetChart isOpen_univ isOpen_univ
      (mem_univ (0 : Vector 3)) (mem_univ (0 : Vector 3)) hf.contMDiffOn hg.contMDiffOn
      hzero.symm hdim (sourceChart_transversality F G hF hG ht) isOpen_univ (mem_univ _)
  let ε := b / 4
  have hε : 0 < ε := div_pos hb (by norm_num)
  have he : ε * 4 = b := by dsimp [ε]; ring
  have hp : closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source := by rwa [he]
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  let K := gluedSphereMap Φ F G hε h1 hp hleft hright hF hG
  refine ⟨ε, hε, K, contMDiff_gluedSphere Φ F G hε h1 hp hleft hright hF hG,
    injective_mfderiv_gluedSphere Φ F G hε hp (by norm_num : (1 : ℝ) ∈ Ioc 0 1)
      hleft hright hF hG hFi hGi,
    ⟨immersedToPinchHomotopy F G Φ hε hp hleft hright hF hG hzero⟩, ?_, ?_⟩
  · exact fun x hx ↦ gluedSphere_north Φ F G hε h1 hp hleft hx
  · exact fun x hx ↦ gluedSphere_south Φ F G hε h1 hp hright hx

end NoExoticSixSphere.SphereSumNeck
