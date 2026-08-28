import Wikipedia.NoExoticSixSphere.SphereCapPairTransport
import Wikipedia.NoExoticSixSphere.SphereGluedNeckUniqueFiber
import Wikipedia.NoExoticSixSphere.SphereRemovedDiskFibers

/-!
# Exact ordered double-point correspondence for the clean glued sphere

The northern and southern self-pairs are exactly the old self-pairs.
Each old mutual pair except the chosen crossing occurs in both orders.
The neck contributes no additional double points. This is a bijection of
the actual source-pair types, before making any finiteness assumption.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  (F G : Sphere 3 → M) {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))

def gluedSpherePairEquiv :
    SphereSelfIntersections.pairs (gluedSphere Φ ε a F G) ≃
      (SphereSelfIntersections.pairs F ⊕
        mutualPairsExcept F G (sourceChart 0, sourceChart 0)) ⊕
      (mutualPairsExcept F G (sourceChart 0, sourceChart 0) ⊕
        SphereSelfIntersections.pairs G) := by
  let K := gluedSphere Φ ε a F G
  let e := northExteriorEquiv ε hε
  let d := southExteriorEquiv ε hε
  have hleft : ∀ x : northExterior, K x.val = F (e x).val := by
    intro x
    change gluedSphere Φ ε a F G x.val = F (sphereCap ε x.val)
    simp only [gluedSphere, if_neg x.property.2,
      if_pos (northExterior_mem_northRegion x.property), northPiece]
  have hright : ∀ y : southExterior, K y.val = G (d y).val := by
    intro y
    have hn : y.val ∉ northRegion := fun h ↦
      (not_lt_of_gt (northRegion_head_pos h)) y.property.1
    change gluedSphere Φ ε a F G y.val = G (sphereCap ε (reflectHead y.val))
    simp only [gluedSphere, if_neg y.property.2, if_neg hn, southPiece]
  have houtF : ∀ p : SphereSelfIntersections.pairs F,
      p.val.1 ∈ (removedSourceDisk ε)ᶜ ∧ p.val.2 ∈ (removedSourceDisk ε)ᶜ := by
    intro p
    exact doublePoints_left_outside_removed Φ F G hε hprod hclean
      p.property.1 p.property.2
  have houtG : ∀ p : SphereSelfIntersections.pairs G,
      p.val.1 ∈ (removedSourceDisk ε)ᶜ ∧ p.val.2 ∈ (removedSourceDisk ε)ᶜ := by
    intro p
    exact doublePoints_right_outside_removed Φ F G hε hprod hclean
      p.property.1 p.property.2
  have houtFG : ∀ p : mutualPairsExcept F G (sourceChart 0, sourceChart 0),
      p.val.val.1 ∈ (removedSourceDisk ε)ᶜ ∧
        p.val.val.2 ∈ (removedSourceDisk ε)ᶜ := by
    intro p
    exact mutualPairs_outside_removed Φ F G hε hprod hclean p.val.property
      (fun h ↦ p.property (Prod.ext h.1 h.2))
  have hc : (sourceChart 0, sourceChart 0).1 ∉ (removedSourceDisk ε)ᶜ := by
    exact fun h ↦ h (sourceChart_zero_mem_removed hε)
  let eF := sameCapPairEquiv K F e hleft houtF
  let eG := sameCapPairEquiv K G d hright houtG
  let eFG := mixedCapPairEquiv K F G e d hleft hright
    (sourceChart 0, sourceChart 0) hc disjoint_exterior houtFG
  let eGF := (capPairSwapEquiv K southExterior northExterior).trans eFG
  exact (exteriorPairPartition K (fun p ↦
    gluedSphere_doublePoints_outside_neck Φ hε ha hprod F G hclean
      p.property.1 p.property.2)).trans
    (Equiv.sumCongr (Equiv.sumCongr eF eFG) (Equiv.sumCongr eGF eG))

end NoExoticSixSphere.SphereSumNeck
