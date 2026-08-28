import Wikipedia.NoExoticSixSphere.CompactProductFiberCohomology
import Wikipedia.NoExoticSixSphere.EuclideanCompactSupportTopCap

/-!
# A genuine compact-supported normal-fiber class on a product

The proved original Euclidean top cap followed by original augmentation
marks top compact-support cohomology by the actual mod-two coefficient.
Its unit class pulls back along the proper product projection. Every
actual fiber restriction recovers that same unit class, which remains
nonzero. Identification of its cap with the zero section, and comparison
with geometric intersection numbers, are not asserted in this file.
-/

noncomputable section

namespace NoExoticSixSphere.ProductNormalCohomologyClass

open CompactSupportCohomology CompactProductFiberCohomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- The original Euclidean cap followed by the original coefficient augmentation. -/
def fiberMark : Cohomology E (n + 3) ≃ₗ[ℤ] ZMod 2 :=
  (CompactSupportCapMap.euclideanTopEquiv E n).trans
    (CoefficientChains.connectedZeroEquiv ModTwoCapProduct.Coefficient E)

/-- The actual compact-supported class with unit cap augmentation. -/
def fiberClass : Cohomology E (n + 3) := (fiberMark E n).symm 1

theorem fiberMark_fiberClass : fiberMark E n (fiberClass E n) = 1 :=
  (fiberMark E n).apply_symm_apply 1

/-- The marking is the original cap-augmentation map, not an assigned group identification. -/
theorem fiberMark_apply (a : Cohomology E (n + 3)) :
    fiberMark E n a = CoefficientChains.augmentation ModTwoCapProduct.Coefficient E
      (CompactSupportCapMap.dualityMap (E := E) n E (n + 3) 0 (Nat.add_zero (n + 3)) a) := rfl

theorem fiberClass_ne_zero : fiberClass E n ≠ 0 := by
  intro he
  exact one_ne_zero ((fiberMark_fiberClass E n).symm.trans
    ((congrArg (fiberMark E n) he).trans (fiberMark E n).map_zero))

/-- Unit cap augmentation characterizes this original fiber class. -/
theorem fiberClass_unique (a : Cohomology E (n + 3)) (ha : fiberMark E n a = 1) :
    a = fiberClass E n :=
  (fiberMark E n).injective (ha.trans (fiberMark_fiberClass E n).symm)

variable (B : Type) [TopologicalSpace B] [CompactSpace B]

/-- Pull back the actual Euclidean class by the proper projection with compact base. -/
def normalClass : Cohomology (B × E) (n + 3) :=
  projectionPullback (B := B) (n + 3) (fiberClass E n)

/-- Restriction to any actual normal fiber recovers the original Euclidean class. -/
theorem normalClass_restrict [T1Space B] (b : B) :
    fiberPullback b (n + 3) (normalClass E n B) = fiberClass E n :=
  fiberPullback_projectionPullback b (n + 3) (fiberClass E n)

theorem normalClass_ne_zero [T1Space B] (b : B) : normalClass E n B ≠ 0 :=
  projectionPullback_ne_zero b (n + 3) (fiberClass_ne_zero E n)

/-- The actual restricted class has unit original cap augmentation at every base point. -/
theorem normalClass_fiberMark [T1Space B] (b : B) :
    fiberMark E n (fiberPullback b (n + 3) (normalClass E n B)) = 1 :=
  (congrArg (fiberMark E n) (normalClass_restrict E n B b)).trans (fiberMark_fiberClass E n)

end NoExoticSixSphere.ProductNormalCohomologyClass
