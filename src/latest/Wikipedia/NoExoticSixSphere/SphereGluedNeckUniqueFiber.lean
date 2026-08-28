import Wikipedia.NoExoticSixSphere.SphereCappedNeckGlobalFibers
import Wikipedia.NoExoticSixSphere.SphereNeckCapSeparation
import Wikipedia.NoExoticSixSphere.SphereSumGluing

/-!
# No global double point of the glued sphere involves its neck region

The neck is injective on its whole source region. Any coincidence with an
exterior cap would, by the full-fiber chart property, force that exterior
source point back into the neck region. This rules out coincidences with
all global branches, including both cap poles.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)

include hε ha hprod in
theorem middlePiece_injOn : InjOn (middlePiece Φ ε a) neckRegion := by
  intro x hx y hy he
  have hxt := neckRegion_time hx
  have hyt := neckRegion_time hy
  have hq := chartCapNeck_injOn Φ hε ha (by norm_num : (1 : ℝ) ≤ 4) hprod
    ⟨hxt.1.le, hxt.2.le⟩ ⟨hyt.1.le, hyt.2.le⟩ he
  exact (SphereCylinder.point_inverse 2 x (neckRegion_mem_band hx)).symm.trans
    ((congrArg (SphereCylinder.point 2) hq).trans
      (SphereCylinder.point_inverse 2 y (neckRegion_mem_band hy)))

variable (F G : Sphere 3 → M)
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))

include hε ha hprod hclean

theorem gluedSphere_unique_fiber_neck {x : Sphere 3} (hx : x ∈ neckRegion)
    (y : Sphere 3) (he : gluedSphere Φ ε a F G x = gluedSphere Φ ε a F G y) : x = y := by
  by_cases hy : y ∈ neckRegion
  · apply middlePiece_injOn Φ hε ha hprod hx hy
    exact (gluedSphere_middle Φ F G hx).symm.trans (he.trans (gluedSphere_middle Φ F G hy))
  · have htime := neckRegion_time hx
    let q := SphereCylinder.inverse 2 x
    have hq : q.1 ∈ Icc (-4 : ℝ) 4 := ⟨htime.1.le, htime.2.le⟩
    rcases sourceRegion_cover y with hy' | hn | hs
    · exact (hy hy').elim
    · have hky : gluedSphere Φ ε a F G y = F (sphereCap ε y) := by
        simp only [gluedSphere, if_neg hy, if_pos hn, northPiece]
      have hf : F (sphereCap ε y) = chartCapNeck Φ ε (a, q) :=
        hky.symm.trans (he.symm.trans (gluedSphere_middle Φ F G hx))
      obtain ⟨ht, hc⟩ := (chartCapNeck_fiber_left Φ F G hε ha.le
        (by norm_num : (1 : ℝ) ≤ 4) hprod hclean q hq (sphereCap ε y)).mp hf
      have hp : 0 < capProfile a q.1 := capProfile_pos (by linarith)
      have hlt : capProfile a q.1 < 4 := capProfile_lt_four a htime.2
      exact (hy (sphereCap_ray_implies_neckRegion hε hp hlt q.2
        (northRegion_head_pos hn) hc)).elim
    · have hn : y ∉ northRegion := fun hn ↦
        (not_lt_of_gt (northRegion_head_pos hn)) (southRegion_head_neg hs)
      have hky : gluedSphere Φ ε a F G y = G (sphereCap ε (reflectHead y)) := by
        simp only [gluedSphere, if_neg hy, if_neg hn, southPiece]
      have hg : G (sphereCap ε (reflectHead y)) = chartCapNeck Φ ε (a, q) :=
        hky.symm.trans (he.symm.trans (gluedSphere_middle Φ F G hx))
      obtain ⟨ht, hc⟩ := (chartCapNeck_fiber_right Φ F G hε ha.le
        (by norm_num : (1 : ℝ) ≤ 4) hprod hclean q hq (sphereCap ε (reflectHead y))).mp hg
      have hp : 0 < capProfile a (-q.1) := capProfile_pos (by linarith)
      have hlt : capProfile a (-q.1) < 4 := capProfile_lt_four a (by linarith [htime.1])
      have hh : 0 < (reflectHead y).val 0 := by
        rw [reflectHead_head]
        exact neg_pos.mpr (southRegion_head_neg hs)
      have hyn := sphereCap_ray_implies_neckRegion hε hp hlt q.2 hh hc
      exact (hy ((reflectHead_mem_neckRegion_iff y).mp hyn)).elim

theorem gluedSphere_doublePoints_outside_neck {x y : Sphere 3} (hne : x ≠ y)
    (he : gluedSphere Φ ε a F G x = gluedSphere Φ ε a F G y) :
    x ∉ neckRegion ∧ y ∉ neckRegion := by
  constructor
  · intro hx
    exact hne (gluedSphere_unique_fiber_neck Φ hε ha hprod F G hclean hx y he)
  · intro hy
    exact hne (gluedSphere_unique_fiber_neck Φ hε ha hprod F G hclean hy x he.symm).symm

end NoExoticSixSphere.SphereSumNeck
