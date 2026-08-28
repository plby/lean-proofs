import Wikipedia.NoExoticSixSphere.SphereCollapsedLinearization

/-!
# Exact formulas for the linear collapse on both original hemispheres

The open northern and southern hemispheres use the prescribed cap maps.
On the actual equator both radial components vanish and the map equals
the common reference-chart center value. These formulas also hold on the
part of either hemisphere inside the middle source region.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

theorem linearPair_of_nonneg (q : Parameter) (hq : 0 ≤ q.1) :
    linearPair q = (q.1 • q.2.val, 0) := by
  simp only [linearPair, max_eq_left hq, max_eq_right (neg_nonpos.mpr hq), zero_smul]

theorem linearPair_of_nonpos (q : Parameter) (hq : q.1 ≤ 0) :
    linearPair q = (0, (-q.1) • q.2.val) := by
  simp only [linearPair, max_eq_right hq, max_eq_left (neg_nonneg.mpr hq), zero_smul]

theorem head_zero_mem_neckRegion {x : Sphere 3} (hx : x.val 0 = 0) : x ∈ neckRegion := by
  rcases sourceRegion_cover x with hb | hn | hs
  · exact hb
  · exact False.elim (by linarith [northRegion_head_pos hn])
  · exact False.elim (by linarith [southRegion_head_neg hs])

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε : ℝ}
  (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))

include hε hprod hleft in
theorem linearSphere_north {x : Sphere 3} (hx : 0 < x.val 0) :
    linearSphere Φ F G ε x = F (sphereCap ε x) := by
  by_cases hb : x ∈ neckRegion
  · let q := SphereCylinder.inverse 2 x
    have hband := neckRegion_mem_band hb
    have ht : 0 < q.1 := div_pos hx (norm_pos_iff.mpr hband)
    have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
    have hs := hprod (scaled_linearizingPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
      1 q ⟨htime.1.le, htime.2.le⟩)
    rw [linearizingPair_one] at hs
    have he : ε • linearPair q = ((ε * q.1) • q.2.val, 0) := by
      rw [linearPair_of_nonneg q ht.le]
      simp [smul_smul]
    rw [he] at hs
    have hcap := sphereCap_cylinder hε q.1 q.2 ht
    rw [SphereCylinder.point_inverse 2 x hband] at hcap
    rw [linearSphere, if_pos hb]
    change Φ (ε • linearPair q) = F (sphereCap ε x)
    rw [he, hleft _ hs, hcap]
  · rcases sourceRegion_cover x with hb' | hn | hs
    · exact (hb hb').elim
    · simp only [linearSphere, if_neg hb, if_pos hn, northPiece]
    · exact False.elim (by linarith [southRegion_head_neg hs])

include hε hprod hright in
theorem linearSphere_south {x : Sphere 3} (hx : x.val 0 < 0) :
    linearSphere Φ F G ε x = G (sphereCap ε (reflectHead x)) := by
  by_cases hb : x ∈ neckRegion
  · let q := SphereCylinder.inverse 2 x
    have hband := neckRegion_mem_band hb
    have ht : q.1 < 0 := div_neg_of_neg_of_pos hx (norm_pos_iff.mpr hband)
    have htime : q.1 ∈ Ioo (-4 : ℝ) 4 := neckRegion_time hb
    have hs := hprod (scaled_linearizingPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
      1 q ⟨htime.1.le, htime.2.le⟩)
    rw [linearizingPair_one] at hs
    have he : ε • linearPair q = (0, (ε * (-q.1)) • q.2.val) := by
      rw [linearPair_of_nonpos q ht.le]
      simp [smul_smul]
    rw [he] at hs
    have href : reflectHead x = SphereCylinder.point 2 (-q.1, q.2) := by
      have h := reflectHead_cylinder q.1 q.2
      rw [SphereCylinder.point_inverse 2 x hband] at h
      exact h
    have hcap : sphereCap ε (reflectHead x) = sourceChart ((ε * (-q.1)) • q.2.val) := by
      rw [href]
      exact sphereCap_cylinder hε (-q.1) q.2 (neg_pos.mpr ht)
    rw [linearSphere, if_pos hb]
    change Φ (ε • linearPair q) = G (sphereCap ε (reflectHead x))
    rw [he, hright _ hs, hcap]
  · have hn : x ∉ northRegion := fun hn ↦ (not_lt_of_gt (northRegion_head_pos hn)) hx
    simp only [linearSphere, if_neg hb, if_neg hn, southPiece]

theorem linearSphere_equator {x : Sphere 3} (hx : x.val 0 = 0) :
    linearSphere Φ F G ε x = Φ 0 := by
  have hb := head_zero_mem_neckRegion hx
  have ht : (SphereCylinder.inverse 2 x).1 = 0 := by
    change x.val 0 / ‖SphereCylinder.tail 2 x.val‖ = 0
    rw [hx, zero_div]
  rw [linearSphere, if_pos hb]
  simp only [linearPair, ht, neg_zero, max_self, zero_smul, Prod.mk_zero_zero, smul_zero]

include hε hprod hleft hright in
theorem reference_center_agreement : F (sourceChart 0) = G (sourceChart 0) := by
  have hz : ((0, 0) : Vector 3 × Vector 3) ∈ Φ.source :=
    hprod ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  exact (hleft 0 hz).symm.trans (hright 0 hz)

include hε hprod hleft in
theorem linearSphere_equator_value {x : Sphere 3} (hx : x.val 0 = 0) :
    linearSphere Φ F G ε x = F (sourceChart 0) := by
  rw [linearSphere_equator Φ F G hx]
  exact hleft 0 (hprod ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩)

end NoExoticSixSphere.SphereSumNeck
