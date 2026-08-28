import Wikipedia.NoExoticSixSphere.SphereGluedNeckUniqueFiber
import Wikipedia.NoExoticSixSphere.SphereGluedCapPairTransversality

/-!
# The globally clean glued sphere is self-transverse

All double points lie in the two exterior caps. Exact open cap germs and
actual local diffeomorphisms transport the original self- and mutual
transversality conditions at those surviving pairs.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : a ∈ Ioc (0 : ℝ) 1)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hleft : ∀ v, (v, 0) ∈ Φ.source → Φ (v, 0) = F (sourceChart v))
  (hright : ∀ v, (0, v) ∈ Φ.source → Φ (0, v) = G (sourceChart v))
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))

include hε ha hprod hleft hright hclean

theorem selfTransverse_gluedSphere
    (hF : ContMDiff (𝓡 3) (𝓡 6) ∞ F) (hG : ContMDiff (𝓡 3) (𝓡 6) ∞ G)
    (htF : NativeSphereSelfTransverse F) (htG : NativeSphereSelfTransverse G)
    (htFG : NativeSpherePairTransverse F G) :
    NativeSphereSelfTransverse (gluedSphere Φ ε a F G) := by
  have ha' : a ∈ Icc (0 : ℝ) 1 := ⟨ha.1.le, ha.2⟩
  intro x y hne he
  obtain ⟨hx, hy⟩ := gluedSphere_doublePoints_outside_neck Φ hε ha.1 hprod F G hclean hne he
  have cx : x ∈ northRegion ∨ x ∈ southRegion :=
    (sourceRegion_cover x).resolve_left hx
  have cy : y ∈ northRegion ∨ y ∈ southRegion :=
    (sourceRegion_cover y).resolve_left hy
  rcases cx with hx | hx <;> rcases cy with hy | hy
  · exact transverse_glued_north_pair Φ F G hε ha' hprod hleft hF htF hx hy hne he
  · exact transverse_glued_mixed_pair Φ F G hε ha' hprod hleft hright hF hG htFG hx hy he
  · exact nativeSphereTransverseAt_swap
      (transverse_glued_mixed_pair Φ F G hε ha' hprod hleft hright hF hG htFG hy hx he.symm)
  · exact transverse_glued_south_pair Φ F G hε ha' hprod hright hG htG hx hy hne he

end NoExoticSixSphere.SphereSumNeck
