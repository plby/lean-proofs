import Wikipedia.NoExoticSixSphere.SphereSumGluing

/-!
# Retained target containment of the actual glued sphere

If both entire input maps and the whole neck chart target lie in a given
set, every piece of the actual glued sphere lies there. The middle piece
uses the proved capped-neck bound and retained chart-source inclusion.
-/

noncomputable section

open Set Function Metric
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Γ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Γ.source)

include hε hprod in
theorem gluedSphere_mem_of_ranges {O : Set M} (hΓ : Γ.target ⊆ O)
    (hF : ∀ x, F x ∈ O) (hG : ∀ x, G x ∈ O) (x : Sphere 3) :
    gluedSphere Γ ε a F G x ∈ O := by
  classical
  by_cases hx : x ∈ neckRegion
  · rw [gluedSphere_middle Γ F G hx]
    have ht := neckRegion_time hx
    have hs := hprod (scaled_capPair_mem_product hε (by norm_num : (1 : ℝ) ≤ 4)
      a (SphereCylinder.inverse 2 x) ⟨ht.1.le, ht.2.le⟩)
    exact hΓ (Γ.map_source hs)
  · by_cases hn : x ∈ northRegion
    · simpa only [gluedSphere, if_neg hx, if_pos hn, northPiece] using hF (sphereCap ε x)
    · simpa only [gluedSphere, if_neg hx, if_neg hn, southPiece] using
        hG (sphereCap ε (reflectHead x))

end NoExoticSixSphere.SphereSumNeck
