import Wikipedia.NoExoticSixSphere.SphereSumOpeningHomotopy
import Wikipedia.SmoothSixDPoincare.TransverseSheetChart

/-!
# A global immersed resolution constructed from actual transverse sphere maps

Native transversality at the common source-chart center constructs the
simultaneous target chart and a sufficient radius. No target straightening
chart is assumed. The resulting globally smooth immersed sphere has the
specified original cap maps and is homotopic to a map collapsing the original
equator to the common value.

Identifying that collapsed map with sphere addition, and comparing actual
double points and frame parity, are still required for the quadratic identity.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem contMDiff_sourceChart : ContMDiff (𝓡 3) (𝓡 3) ∞ sourceChart := by
  rw [← contMDiffOn_univ, ← sourceChart_source]
  exact sourceChart.contMDiffOn_toFun

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (F G : Sphere 3 → M)

theorem sourceChart_transversality (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    Surjective ((mfderiv (𝓡 3) (𝓡 6) (F ∘ sourceChart) 0).coprod
      (mfderiv (𝓡 3) (𝓡 6) (G ∘ sourceChart) 0)) := by
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ sourceChart 0 :=
    ⟨sourceChart, by rw [sourceChart_source]; trivial, fun _ _ ↦ rfl⟩
  have hs := (hlocal.mfderivToContinuousLinearEquiv (by simp)).surjective
  change Surjective (mfderiv (𝓡 3) (𝓡 3) sourceChart 0) at hs
  rw [mfderiv_comp 0 (hF.mdifferentiableAt (by simp)) (hlocal.mdifferentiableAt (by simp)),
    mfderiv_comp 0 (hG.mdifferentiableAt (by simp)) (hlocal.mdifferentiableAt (by simp))]
  intro z
  obtain ⟨⟨u, v⟩, huv⟩ := ht z
  obtain ⟨u', hu⟩ := hs u
  obtain ⟨v', hv⟩ := hs v
  refine ⟨(u', v'), ?_⟩
  change ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
    (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))
      (mfderiv (𝓡 3) (𝓡 3) sourceChart 0 u', mfderiv (𝓡 3) (𝓡 3) sourceChart 0 v') = z
  rw [hu, hv]
  exact huv

variable [IsManifold (𝓡 6) ∞ M] [T2Space M] [CompactSpace M]

theorem exists_smooth_immersed_resolution
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    (hzero : G (sourceChart 0) = F (sourceChart 0))
    (ht : Surjective ((mfderiv (𝓡 3) (𝓡 6) F (sourceChart 0)).coprod
      (mfderiv (𝓡 3) (𝓡 6) G (sourceChart 0)))) :
    ∃ ε : ℝ, 0 < ε ∧ ∃ K P : C(Sphere 3, M),
      ContMDiff (𝓡 3) (𝓡 6) ∞ K ∧
      (∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) K x)) ∧
      P.Homotopic K ∧
      (∀ x, x.val 0 = 0 → P x = F (sourceChart 0)) ∧
      (∀ x ∈ northRegion, K x = F (sphereCap ε x)) ∧
      (∀ x ∈ southRegion, K x = G (sphereCap ε (reflectHead x))) := by
  have hf := hF.comp contMDiff_sourceChart
  have hg := hG.comp contMDiff_sourceChart
  have hdim : Module.finrank ℝ (Vector 3) + Module.finrank ℝ (Vector 3) =
      Module.finrank ℝ (Vector 6) := by simp
  obtain ⟨b, hb, Φ, hprod, _, _, hleft, hright⟩ :=
    Wikipedia.SmoothSixDPoincare.exists_simultaneous_sheetChart isOpen_univ isOpen_univ
      (mem_univ (0 : Vector 3)) (mem_univ (0 : Vector 3)) hf.contMDiffOn hg.contMDiffOn
      hzero hdim (sourceChart_transversality F G hF hG ht) isOpen_univ (mem_univ _)
  let ε := b / 4
  have hε : 0 < ε := div_pos hb (by norm_num)
  have he : ε * 4 = b := by dsimp [ε]; ring
  have hp : closedBall (0 : Vector 3) (ε * 4) ×ˢ
      closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source := by rwa [he]
  have h0 : (0 : ℝ) ∈ Icc 0 1 := by norm_num
  have h1 : (1 : ℝ) ∈ Icc 0 1 := by norm_num
  let K := gluedSphereMap Φ F G hε h1 hp hleft hright hF hG
  let P := gluedSphereMap Φ F G hε h0 hp hleft hright hF hG
  refine ⟨ε, hε, K, P, contMDiff_gluedSphere Φ F G hε h1 hp hleft hright hF hG,
    injective_mfderiv_gluedSphere Φ F G hε hp (by norm_num : (1 : ℝ) ∈ Ioc 0 1)
      hleft hright hF hG hFi hGi,
    ⟨gluedOpeningHomotopy Φ F G hε hp hleft hright hF hG⟩, ?_, ?_, ?_⟩
  · intro x hx
    change gluedSphere Φ ε 0 F G x = F (sourceChart 0)
    rw [gluedSphere_zero_equator Φ F G hx]
    exact hleft 0 (hp ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩)
  · exact fun x hx ↦ gluedSphere_north Φ F G hε h1 hp hleft hx
  · exact fun x hx ↦ gluedSphere_south Φ F G hε h1 hp hright hx

end NoExoticSixSphere.SphereSumNeck
