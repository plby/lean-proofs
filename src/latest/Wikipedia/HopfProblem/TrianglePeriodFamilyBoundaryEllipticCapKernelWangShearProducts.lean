import Wikipedia.HopfProblem.PeriodTorusHigherHomologyWedgeThree

/-!
# Repeated-head cancellation for actual singular Pontryagin products

These identities use the genuine singular cross product, its naturality,
and the proved alternating laws. They do not assume an exterior-algebra
description of the homology of the space.
-/

noncomputable section

namespace Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear

open SingularMayerVietoris PeriodTorusHigherHomology PeriodTorusHigherHomologyPontryagin

attribute [local instance] PeriodTorusHigherHomology.integerLinearMapModule
  PeriodTorusHigherHomology.integerTensorModule

variable (G : Type) [TopologicalSpace G] [AddCommGroup G] [IsTopologicalAddGroup G]
  [Module.IsTorsionFree ℤ (SingularHomology G 2)]

/-- Subtracting a multiple of the first factor does not change its actual square product. -/
theorem product11_sub_head (a b : SingularHomology G 1) (k : ℤ) :
    product11 G a (b - k • a) = product11 G a b := by
  rw [map_sub, map_zsmul, product11_self, zsmul_zero, sub_zero]

/-- Subtracting multiples of the first factor does not change the actual triple product. -/
theorem tripleProduct_sub_head (a b c : SingularHomology G 1) (k l : ℤ) :
    tripleProduct G a (b - k • a) (c - l • a) = tripleProduct G a b c := by
  calc
    tripleProduct G a (b - k • a) (c - l • a) =
        tripleProduct G a b (c - l • a) - k • tripleProduct G a a (c - l • a) := by
      rw [(tripleProduct G a).map_sub, LinearMap.sub_apply]
      exact congrArg (fun t => tripleProduct G a b (c - l • a) - t)
        (congrArg (fun f : SingularHomology G 1 →ₗ[ℤ] SingularHomology G 3 =>
          f (c - l • a)) (map_zsmul (tripleProduct G a) k a))
    _ = tripleProduct G a b (c - l • a) := by
      rw [tripleProduct_self01, zsmul_zero, sub_zero]
    _ = tripleProduct G a b c := by
      rw [map_sub, map_zsmul, tripleProduct_self02, zsmul_zero, sub_zero]

/-- A genuine continuous additive map fixing the first factor preserves a sheared product. -/
theorem product11_fixed_of_head (f : C(G, G))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (a b : SingularHomology G 1) (k : ℤ)
    (ha : singularHomologyMap f 1 a = a)
    (hb : singularHomologyMap f 1 b = b - k • a) :
    singularHomologyMap f 2 (product11 G a b) = product11 G a b := by
  rw [product_natural f hf 1, ha, hb, product11_sub_head]

/-- The same native naturality and cancellation statement for the triple product. -/
theorem tripleProduct_fixed_of_head (f : C(G, G))
    (hf : ∀ x y, f (x + y) = f x + f y)
    (a b c : SingularHomology G 1) (k l : ℤ)
    (ha : singularHomologyMap f 1 a = a)
    (hb : singularHomologyMap f 1 b = b - k • a)
    (hc : singularHomologyMap f 1 c = c - l • a) :
    singularHomologyMap f 3 (tripleProduct G a b c) = tripleProduct G a b c := by
  rw [tripleProduct_natural f hf, ha, hb, hc, tripleProduct_sub_head]

end Wikipedia.HopfProblem.TrianglePeriodFamily.BoundaryEllipticCapKernelWangShear
