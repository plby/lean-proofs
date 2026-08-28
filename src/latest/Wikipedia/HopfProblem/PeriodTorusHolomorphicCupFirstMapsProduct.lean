import Wikipedia.HopfProblem.PeriodTorusHolomorphicCupFirstMapsNative

/-!
# The original holomorphic cup product is the actual total cup product

The native Godement comparison, the genuine first-column quotient
map, and the actual total-resolution comparison give the product
identity on the original Ext-defined holomorphic cohomology groups.
-/

noncomputable section

open scoped Manifold

namespace Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps

open SheafCupProduct

private theorem compose_product_comparison
    {A B C D E F : Type*}
    (p : A → A → B) (q : C → C → D) (r : E → E → F)
    (e1 : A → C) (e2 : B → D) (m1 : C → E) (m2 : D → F)
    (t1 : A → E) (t2 : B → F)
    (hp : ∀ a b, e2 (p a b) = q (e1 a) (e1 b))
    (hm : ∀ a b, m2 (q a b) = r (m1 a) (m1 b))
    (h1 : ∀ a, m1 (e1 a) = t1 a)
    (h2 : ∀ b, m2 (e2 b) = t2 b) (a b : A) :
    t2 (p a b) = r (t1 a) (t1 b) := by
  rw [← h2, hp, hm, h1, h1]

private theorem source_cup_comparison (p : PeriodDomain)
    (a b : PeriodTorusHolomorphicCohomology.H p 1) :
    h2CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p)
        (SheafCupProduct.holomorphicCup
          (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus a b) =
      (sourceData p).cup
        (h1CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p) a)
        (h1CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p) b) := by
  simpa only [SheafCupProduct.holomorphicCup, Derivation.holomorphicRingSheaf,
    sourceScalarEnd, sourceData] using
    SheafCupProduct.cup_comparison (Derivation.holomorphicRingSheaf p)
      (sourceScalarEnd p) a b

/-- Genuine native holomorphic cup preservation under the actual total comparison. -/
theorem native_cup (p : PeriodDomain) (a b : PeriodTorusHolomorphicCohomology.H p 1) :
    totalNativeTwoEquiv p (SheafCupProduct.holomorphicCup
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus a b) =
      (totalData p).cup (totalNativeOneEquiv p a) (totalNativeOneEquiv p b) :=
  compose_product_comparison
    (fun x y => SheafCupProduct.holomorphicCup
      (modelWithCornersSelf ℂ ComplexPlane₂) p.Torus x y)
    (fun x y => (sourceData p).cup x y) (fun x y => (totalData p).cup x y)
    (h1CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p))
    (h2CofaceEquiv (Derivation.holomorphicRingSheaf p) (sourceScalarEnd p))
    (firstH1 p) (firstH2 p) (totalNativeOneEquiv p) (totalNativeTwoEquiv p)
    (source_cup_comparison p) (firstH_cup p)
    (firstOne_native_apply p) (firstTwo_native_apply p) a b

end Wikipedia.HopfProblem.PeriodTorusHolomorphicCup.FirstMaps
