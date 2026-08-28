import Wikipedia.NoExoticSixSphere.SphereSumGluing
import Wikipedia.NoExoticSixSphere.SphereSumCappedNeckImmersion

/-!
# The globally glued sphere has injective native derivative

A positive opening makes the entire neck immersive. Its source cylinder
coordinates are a native partial diffeomorphism. The two cap coordinates
are native local diffeomorphisms, including the poles, so immersion of the
original sphere maps is preserved there. Exact open-overlap agreement then
proves immersion of the actual glued map everywhere on the original sphere.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ}
  (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε hprod in
theorem injective_mfderiv_middlePiece (ha : 0 < a) {x : Sphere 3} (hx : x ∈ neckRegion) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (middlePiece Φ ε a) x) := by
  let q := SphereCylinder.inverse 2 x
  have ht : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hx
  have hq : q.1 ∈ Icc (-4 : ℝ) 4 := ⟨ht.1.le, ht.2.le⟩
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) Model ∞ (SphereCylinder.inverse 2) x :=
    ⟨(SphereCylinder.chart 2).symm, neckRegion_mem_band hx, fun _ _ ↦ rfl⟩
  have hc : ContMDiffAt Model (𝓡 6) ∞ (fun w ↦ chartCapNeck Φ ε (a, w)) q :=
    (contMDiffAt_chartCapNeck Φ hε (by norm_num : (1 : ℝ) ≤ 4) hprod (a, q) hq).comp q
      (contMDiffAt_const.prodMk contMDiffAt_id)
  change Injective (mfderiv (𝓡 3) (𝓡 6)
    ((fun w ↦ chartCapNeck Φ ε (a, w)) ∘ SphereCylinder.inverse 2) x)
  rw [mfderiv_comp x (hc.mdifferentiableAt (by simp)) (hlocal.mdifferentiableAt (by simp))]
  exact (injective_mfderiv_chartCapNeck_slice Φ hε ha (by norm_num : (1 : ℝ) ≤ 4)
    hprod q hq).comp (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective

include hε in
theorem injective_mfderiv_northPiece (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    {x : Sphere 3} (hx : x ∈ northRegion) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (northPiece ε F) x) := by
  have hcap := contMDiffAt_sphereCap hε.ne' (northRegion_head_pos hx)
  change Injective (mfderiv (𝓡 3) (𝓡 6) (F ∘ sphereCap ε) x)
  rw [mfderiv_comp x (hF.mdifferentiableAt (by simp)) (hcap.mdifferentiableAt (by simp))]
  exact (hFi _).comp (bijective_mfderiv_sphereCap hε.ne' (northRegion_head_pos hx)).injective

include hε in
theorem injective_mfderiv_southPiece (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x))
    {x : Sphere 3} (hx : x ∈ southRegion) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (southPiece ε G) x) := by
  have hn : reflectHead x ∈ northRegion := by
    change 2 * ‖SphereCylinder.tail 2 (reflectHead x).val‖ < (reflectHead x).val 0
    rw [reflectHead_tail, reflectHead_head]
    exact hx
  have hlocal : IsLocalDiffeomorphAt (𝓡 3) (𝓡 3) ∞ reflectHead x :=
    ⟨reflectHeadDiffeomorph.toPartialDiffeomorph, mem_univ _, fun _ _ ↦ rfl⟩
  change Injective (mfderiv (𝓡 3) (𝓡 6) (northPiece ε G ∘ reflectHead) x)
  rw [mfderiv_comp x ((contMDiffAt_northPiece G hε hG hn).mdifferentiableAt (by simp))
    (hlocal.mdifferentiableAt (by simp))]
  exact (injective_mfderiv_northPiece G hε hG hGi hn).comp
    (hlocal.mfderivToContinuousLinearEquiv (by simp)).injective

include hε hprod in
theorem injective_mfderiv_gluedSphere (ha : a ∈ Ioc (0 : ℝ) 1)
    (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
    (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (hFi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) F x))
    (hGi : ∀ x, Injective (mfderiv (𝓡 3) (𝓡 6) G x)) (x : Sphere 3) :
    Injective (mfderiv (𝓡 3) (𝓡 6) (gluedSphere Φ ε a F G) x) := by
  have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2⟩
  rcases sourceRegion_cover x with hb | hn | hs
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] middlePiece Φ ε a := by
      filter_upwards [isOpen_neckRegion.mem_nhds hb] with y hy
      exact gluedSphere_middle Φ F G hy
    rw [he.mfderiv_eq]
    exact injective_mfderiv_middlePiece Φ hε hprod ha.1 hb
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] northPiece ε F := by
      filter_upwards [isOpen_northRegion.mem_nhds hn] with y hy
      exact gluedSphere_north Φ F G hε ha' hprod hleft hy
    rw [he.mfderiv_eq]
    exact injective_mfderiv_northPiece F hε hF hFi hn
  · have he : gluedSphere Φ ε a F G =ᶠ[𝓝 x] southPiece ε G := by
      filter_upwards [isOpen_southRegion.mem_nhds hs] with y hy
      exact gluedSphere_south Φ F G hε ha' hprod hright hy
    rw [he.mfderiv_eq]
    exact injective_mfderiv_southPiece G hε hG hGi hs

end NoExoticSixSphere.SphereSumNeck
