import Wikipedia.NoExoticSixSphere.SphereGluedPairEquiv
import Wikipedia.NoExoticSixSphere.UnorderedSphereDoublePoints

/-!
# The actual double-point count after clean sphere resolution

The ordered-pair bijection implies the exact unordered count. Removing the
chosen mutual pair accounts for the constant one in the mod-two formula.
Finiteness is stated for the original pair sets, not supplied by a counting
axiom. This module does not assert the separate frame-obstruction formula.
-/

noncomputable section

open Set Function Metric Topology
open scoped Manifold ContDiff

namespace NoExoticSixSphere.SphereSumNeck

open GLOrthonormalization

variable {M : Type*} (F G : Sphere 3 → M)

def mutualPairsExceptEquivSdiff (c : Sphere 3 × Sphere 3) :
    mutualPairsExcept F G c ≃ ↥(MapIntersections.pairs F G \ {c}) where
  toFun p := ⟨p.val.val, p.val.property, p.property⟩
  invFun p := ⟨⟨p.val, p.property.1⟩, p.property.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem mutualPairsExcept_card_add_one (c : Sphere 3 × Sphere 3)
    (hc : F c.1 = G c.2) (hfin : (MapIntersections.pairs F G).Finite) :
    Nat.card (mutualPairsExcept F G c) + 1 = (MapIntersections.pairs F G).ncard := by
  rw [Nat.card_congr (mutualPairsExceptEquivSdiff F G c)]
  exact ncard_sdiff_singleton_add_one hc hfin

variable [TopologicalSpace M] [ChartedSpace (Vector 6) M]
  (Φ : PartialDiffeomorph 𝓘(ℝ, Vector 3 × Vector 3) (𝓡 6)
    (Vector 3 × Vector 3) M ∞)
  {ε a : ℝ} (hε : 0 < ε) (ha : 0 < a)
  (hprod : closedBall (0 : Vector 3) (ε * 4) ×ˢ
    closedBall (0 : Vector 3) (ε * 4) ⊆ Φ.source)
  (hclean : ∀ z ∈ Φ.source,
    (∀ x, F x = Φ z ↔ z.2 = 0 ∧ x = sourceChart z.1) ∧
    (∀ x, G x = Φ z ↔ z.1 = 0 ∧ x = sourceChart z.2))
  (hfinF : (SphereSelfIntersections.pairs F).Finite)
  (hfinG : (SphereSelfIntersections.pairs G).Finite)
  (hfinFG : (MapIntersections.pairs F G).Finite)

include hε ha hprod hclean hfinF hfinG hfinFG

theorem finite_gluedSphere_pairs :
    (SphereSelfIntersections.pairs (gluedSphere Φ ε a F G)).Finite := by
  let := hfinF.to_subtype
  let := hfinG.to_subtype
  let := hfinFG.to_subtype
  let : Finite (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) := by
    unfold mutualPairsExcept
    infer_instance
  exact finite_coe_iff.mp (Finite.of_equiv _
    (gluedSpherePairEquiv Φ F G hε ha hprod hclean).symm)

theorem gluedSphere_ordered_ncard :
    (SphereSelfIntersections.pairs (gluedSphere Φ ε a F G)).ncard =
      (SphereSelfIntersections.pairs F).ncard + (SphereSelfIntersections.pairs G).ncard +
        2 * Nat.card (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) := by
  let := hfinF.to_subtype
  let := hfinG.to_subtype
  let := hfinFG.to_subtype
  let : Finite (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) := by
    unfold mutualPairsExcept
    infer_instance
  change Nat.card (SphereSelfIntersections.pairs (gluedSphere Φ ε a F G)) = _
  rw [Nat.card_congr (gluedSpherePairEquiv Φ F G hε ha hprod hclean)]
  simp only [Nat.card_sum]
  change Nat.card (SphereSelfIntersections.pairs F) +
      Nat.card (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) +
      (Nat.card (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) +
        Nat.card (SphereSelfIntersections.pairs G)) =
    Nat.card (SphereSelfIntersections.pairs F) + Nat.card (SphereSelfIntersections.pairs G) +
      2 * Nat.card (mutualPairsExcept F G (sourceChart 0, sourceChart 0))
  omega

theorem gluedSphere_unordered_ncard :
    Nat.card (SphereSelfIntersections.Unordered (gluedSphere Φ ε a F G)) =
      Nat.card (SphereSelfIntersections.Unordered F) +
      Nat.card (SphereSelfIntersections.Unordered G) +
      Nat.card (mutualPairsExcept F G (sourceChart 0, sourceChart 0)) := by
  have hk := finite_gluedSphere_pairs F G Φ hε ha hprod hclean hfinF hfinG hfinFG
  have h := gluedSphere_ordered_ncard F G Φ hε ha hprod hclean hfinF hfinG hfinFG
  rw [SphereSelfIntersections.ordered_ncard_eq_twice_unordered _ hk,
    SphereSelfIntersections.ordered_ncard_eq_twice_unordered _ hfinF,
    SphereSelfIntersections.ordered_ncard_eq_twice_unordered _ hfinG] at h
  omega

theorem gluedSphere_unorderedParity :
    SphereSelfIntersections.unorderedParity (gluedSphere Φ ε a F G) =
      SphereSelfIntersections.unorderedParity F + SphereSelfIntersections.unorderedParity G +
        MapIntersections.parity F G + 1 := by
  have hs : ((0 : Vector 3), (0 : Vector 3)) ∈ Φ.source :=
    hprod ⟨mem_closedBall_self (by positivity), mem_closedBall_self (by positivity)⟩
  have hc : F (sourceChart 0) = G (sourceChart 0) :=
    (((hclean _ hs).1 _).mpr ⟨rfl, rfl⟩).trans
      (((hclean _ hs).2 _).mpr ⟨rfl, rfl⟩).symm
  have hcard := mutualPairsExcept_card_add_one F G (sourceChart 0, sourceChart 0) hc hfinFG
  have hcast := congrArg (fun n : ℕ ↦ (n : ZMod 2)) hcard
  simp only [Nat.cast_add, Nat.cast_one] at hcast
  unfold SphereSelfIntersections.unorderedParity MapIntersections.parity
  rw [gluedSphere_unordered_ncard F G Φ hε ha hprod hclean hfinF hfinG hfinFG]
  simp only [Nat.cast_add]
  rw [← hcast]
  have htwo : (1 : ZMod 2) + 1 = 0 := by decide
  simp only [add_assoc, htwo, add_zero]

end NoExoticSixSphere.SphereSumNeck
