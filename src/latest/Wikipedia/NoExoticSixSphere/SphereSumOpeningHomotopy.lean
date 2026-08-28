import Wikipedia.NoExoticSixSphere.SphereSumGluingImmersion

/-!
# The opening homotopy on the whole original sphere

The middle formula is jointly smooth in its real opening parameter. Both
caps are independent of that parameter, and the overlap identities hold
throughout the unit interval. Thus the actual glued sphere deforms
continuously from its collapsed crossing to the immersed positive opening.
The collapse at opening zero is constant on the original equator.
-/

noncomputable section

open Set Function Filter Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε : ℝ}
  (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

def sphereOpening (ε : ℝ) (p : unitInterval × Sphere 3) : M :=
  gluedSphere Φ ε p.1.val F G p.2

include hε hprod hleft hright in
theorem continuous_sphereOpening (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) : Continuous (sphereOpening Φ F G ε) := by
  apply continuous_iff_continuousAt.mpr
  intro p
  rcases sourceRegion_cover p.2 with hb | hn | hs
  · have ht := neckRegion_time hb
    have hp : ContinuousAt (fun w : unitInterval × Sphere 3 ↦
        (w.1.val, SphereCylinder.inverse 2 w.2)) p :=
      (continuous_subtype_val.comp continuous_fst).continuousAt.prodMk
        ((SphereCylinder.contMDiffAt_inverse 2 (neckRegion_mem_band hb)).continuousAt.comp
          continuous_snd.continuousAt)
    have hc : ContinuousAt (fun w : unitInterval × Sphere 3 ↦
        chartCapNeck Φ ε (w.1.val, SphereCylinder.inverse 2 w.2)) p :=
      (contMDiffAt_chartCapNeck Φ hε (by norm_num : (1 : ℝ) ≤ 4) hprod
        (p.1.val, SphereCylinder.inverse 2 p.2) ⟨ht.1.le, ht.2.le⟩).continuousAt.comp
        (f := fun w : unitInterval × Sphere 3 ↦ (w.1.val, SphereCylinder.inverse 2 w.2)) hp
    have he : sphereOpening Φ F G ε =ᶠ[𝓝 p]
        (fun w : unitInterval × Sphere 3 ↦ chartCapNeck Φ ε
          (w.1.val, SphereCylinder.inverse 2 w.2)) := by
      filter_upwards [(isOpen_neckRegion.preimage continuous_snd).mem_nhds hb] with w hw
      exact gluedSphere_middle Φ F G hw
    exact hc.congr_of_eventuallyEq he
  · have hc := (contMDiffAt_northPiece F hε hF hn).continuousAt.comp
      (continuous_snd.continuousAt (x := p))
    have he : sphereOpening Φ F G ε =ᶠ[𝓝 p]
        (fun w : unitInterval × Sphere 3 ↦ northPiece ε F w.2) := by
      filter_upwards [(isOpen_northRegion.preimage continuous_snd).mem_nhds hn] with w hw
      exact gluedSphere_north Φ F G hε w.1.property hprod hleft hw
    exact hc.congr_of_eventuallyEq he
  · have hc := (contMDiffAt_southPiece G hε hG hs).continuousAt.comp
      (continuous_snd.continuousAt (x := p))
    have he : sphereOpening Φ F G ε =ᶠ[𝓝 p]
        (fun w : unitInterval × Sphere 3 ↦ southPiece ε G w.2) := by
      filter_upwards [(isOpen_southRegion.preimage continuous_snd).mem_nhds hs] with w hw
      exact gluedSphere_south Φ F G hε w.1.property hprod hright hw
    exact hc.congr_of_eventuallyEq he

def gluedOpeningHomotopy (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F)
    (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G) :
    (gluedSphereMap Φ F G hε (show (0 : ℝ) ∈ Icc 0 1 by norm_num)
      hprod hleft hright hF hG).Homotopy
    (gluedSphereMap Φ F G hε (show (1 : ℝ) ∈ Icc 0 1 by norm_num)
      hprod hleft hright hF hG) where
  toFun := sphereOpening Φ F G ε
  continuous_toFun := continuous_sphereOpening Φ F G hε hprod hleft hright hF hG
  map_zero_left _ := rfl
  map_one_left _ := rfl

theorem gluedSphere_zero_equator {x : Sphere 3} (hx : x.val 0 = 0) :
    gluedSphere Φ ε 0 F G x = Φ 0 := by
  have hn : SphereCylinder.tail 2 x.val ≠ 0 := by
    intro hz
    have h := join_head_tail x.val
    rw [hx, hz] at h
    have he : SphereCylinder.join 2 (0, (0 : Vector 3)) = 0 :=
      (SphereCylinder.join 2).map_zero
    exact ne_zero_of_mem_unit_sphere x (h.symm.trans he)
  have hb : x ∈ neckRegion := by
    change |x.val 0| < 4 * ‖SphereCylinder.tail 2 x.val‖
    rw [hx, abs_zero]
    positivity
  rw [gluedSphere_middle Φ F G hb]
  have ht : (SphereCylinder.inverse 2 x).1 = 0 := by
    change x.val 0 / ‖SphereCylinder.tail 2 x.val‖ = 0
    rw [hx, zero_div]
  change Φ (ε • capPair 0 (SphereCylinder.inverse 2 x)) = Φ 0
  have he : capPair 0 (SphereCylinder.inverse 2 x) = 0 := by
    rw [show SphereCylinder.inverse 2 x = (0, (SphereCylinder.inverse 2 x).2) from
      Prod.ext ht rfl, capPair_zero_middle]
  rw [he, smul_zero]

end NoExoticSixSphere.SphereSumNeck
