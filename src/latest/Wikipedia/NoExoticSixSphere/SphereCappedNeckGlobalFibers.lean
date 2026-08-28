import Wikipedia.NoExoticSixSphere.SphereCappedNeckInjectivity
import Wikipedia.NoExoticSixSphere.SphereSumCapCoordinates

/-!
# Exact global input-map fibers along a clean capped neck

The full-fiber chart property determines both the axis condition and the
unique original source point of any coincidence with either sphere map.
The open middle therefore avoids both complete sphere images.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a R : ℝ} (hε : 0 < ε) (ha : 0 ≤ a) (hR : 1 ≤ R)
  (hprod : closedBall (0 : Vector 3) (ε * R) ×ˢ
    closedBall (0 : Vector 3) (ε * R) ⊆ Φ.source)
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))

include hε ha hR hprod hclean

theorem chartCapNeck_fiber_left (q : Parameter) (hq : q.1 ∈ Icc (-R) R) (x : Sphere 3) :
    F x = chartCapNeck Φ ε (a, q) ↔
      a ≤ q.1 ∧ x = sourceChart ((ε * capProfile a q.1) • q.2.val) := by
  have hs := hprod (scaled_capPair_mem_product hε hR a q hq)
  change F x = Φ (ε • capPair a q) ↔ _
  rw [(hclean _ hs).1 x]
  change (ε • (capPair a q).2 = 0 ∧ x = sourceChart (ε • (capPair a q).1)) ↔ _
  rw [smul_eq_zero, or_iff_right hε.ne', capPair_snd_eq_zero_iff ha]
  simp only [capPair, smul_smul]

theorem chartCapNeck_fiber_right (q : Parameter) (hq : q.1 ∈ Icc (-R) R) (x : Sphere 3) :
    G x = chartCapNeck Φ ε (a, q) ↔
      q.1 ≤ -a ∧ x = sourceChart ((ε * capProfile a (-q.1)) • q.2.val) := by
  have hs := hprod (scaled_capPair_mem_product hε hR a q hq)
  change G x = Φ (ε • capPair a q) ↔ _
  rw [(hclean _ hs).2 x]
  change (ε • (capPair a q).1 = 0 ∧ x = sourceChart (ε • (capPair a q).2)) ↔ _
  rw [smul_eq_zero, or_iff_right hε.ne', capPair_fst_eq_zero_iff ha]
  simp only [capPair, smul_smul]

theorem chartCapNeck_middle_avoids (q : Parameter) (hq : q.1 ∈ Icc (-R) R)
    (hm : q.1 ∈ Ioo (-a) a) : chartCapNeck Φ ε (a, q) ∉ range F ∪ range G := by
  rintro (⟨x, hx⟩ | ⟨x, hx⟩)
  · exact (not_le_of_gt hm.2)
      ((chartCapNeck_fiber_left Φ F G hε ha hR hprod hclean q hq x).mp hx).1
  · exact (not_le_of_gt hm.1)
      ((chartCapNeck_fiber_right Φ F G hε ha hR hprod hclean q hq x).mp hx).1

end NoExoticSixSphere.SphereSumNeck
