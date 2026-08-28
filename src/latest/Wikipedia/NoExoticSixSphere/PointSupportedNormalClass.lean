import Wikipedia.NoExoticSixSphere.ProductNormalCohomologyClass

/-!
# Point and zero-section representatives of the original normal class

The genuine radius-zero ball cohomology generator represents the
constructed Euclidean compact-support class. Proper projection pulls
this representative back to the actual zero-section support. This
retains a relative cocycle class supported on the zero section, rather
than only an abstract compact-support class.
-/

noncomputable section

open Metric TopologicalSpace

namespace NoExoticSixSphere.ProductNormalCohomologyClass

open CompactSupportCohomology CompactProductFiberCohomology

variable (E : Type) [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] (n : ℕ) [Fact (Module.finrank ℝ E = (n + 2) + 1)]

/-- Radius zero gives the genuine compact singleton support. -/
def pointSupport : Compacts E := ⟨closedBall (0 : E) 0, isCompact_closedBall (0 : E) 0⟩

theorem pointSupport_coe : (pointSupport E : Set E) = {0} := closedBall_zero

/-- The original supported class from the actual radius-zero relative cohomology marking. -/
def pointClass : Component E (n + 3) (pointSupport E) :=
  ClosedBallLocalHomology.topCohomologyClass E n 0 le_rfl

/-- Insertion of this actual point-supported class is the constructed Euclidean fiber class. -/
theorem of_pointClass : of E (n + 3) (pointSupport E) (pointClass E n) = fiberClass E n := by
  apply fiberClass_unique E n
  change CoefficientChains.augmentation ModTwoCapProduct.Coefficient E
    (CompactSupportedCapMap.dualityMap (E := E) n (closedBall (0 : E) 0)
      (isCompact_closedBall (0 : E) 0) (n + 3) 0 (Nat.add_zero (n + 3)) (pointClass E n)) = 1
  exact (ClosedBallLocalHomology.augmentation_topCap E n 0 le_rfl (pointClass E n)).trans
    (ClosedBallLocalHomology.topCohomologyClass_evaluation E n 0 le_rfl)

variable (B : Type) [TopologicalSpace B] [CompactSpace B]

/-- The actual inverse-image compact support under projection to the normal coordinate. -/
def zeroSectionSupport : Compacts (B × E) :=
  preimageCompact (ContinuousMap.snd : C(B × E, E)) isProperMap_snd_of_compactSpace
    (pointSupport E)

theorem zeroSectionSupport_coe : (zeroSectionSupport E B : Set (B × E)) =
    Set.univ ×ˢ ({0} : Set E) := by
  ext x
  change x.2 ∈ closedBall (0 : E) 0 ↔ x.1 ∈ Set.univ ∧ x.2 ∈ ({0} : Set E)
  rw [closedBall_zero]
  simp only [Set.mem_univ, true_and]

/-- Original relative pullback of the point generator, supported on the actual zero section. -/
def supportedNormalClass : Component (B × E) (n + 3) (zeroSectionSupport E B) :=
  SupportedModTwoCohomology.pullback (ContinuousMap.snd : C(B × E, E))
    (pointSupport E : Set E) (n + 3) (pointClass E n)

/-- The original compact-support normal class has this literal zero-section representative. -/
theorem of_supportedNormalClass :
    of (B × E) (n + 3) (zeroSectionSupport E B) (supportedNormalClass E n B) =
      normalClass E n B :=
  congrArg (projectionPullback (B := B) (n + 3)) (of_pointClass E n)

end NoExoticSixSphere.ProductNormalCohomologyClass
