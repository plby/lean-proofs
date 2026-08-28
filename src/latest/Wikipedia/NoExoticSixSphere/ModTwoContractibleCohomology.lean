import Wikipedia.NoExoticSixSphere.RelativeModTwoCochainSequence
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonCochainNullhomotopy

/-!
# Actual mod-two cohomology in a contractible ambient space

A genuine contraction supplies primitives of the original positive
cocycles. The native cycle quotient therefore vanishes in positive
degrees. The actual relative cohomology connecting map is consequently
an isomorphism between consecutive positive degrees.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem

namespace NoExoticSixSphere.ModTwoCapProduct

variable (X : Type) [TopologicalSpace X] [ContractibleSpace X]

/-- Every actual positive cocycle has an actual cochain primitive. -/
theorem contractible_closed_exact (p : ℕ) (α : Cochain X (p + 1))
    (hα : coboundary α = 0) : ∃ β : Cochain X p, coboundary β = α :=
  ConstantSheafSingularComparison.contractible_closed_exact
    (AddCommGrpCat.of (ZMod 2)) X p α hα

/-- The original positive cohomology classes of a contractible space vanish. -/
theorem contractible_cohomology_eq_zero (p : ℕ) (a : Cohomology X (p + 1)) : a = 0 := by
  obtain ⟨α, rfl⟩ := SingularCohomologyFree.cocycleClass_surjective (cochainComplex X) (p + 1) a
  obtain ⟨β, hβ⟩ := contractible_closed_exact X p α.val (cocycle_coboundary_zero X (p + 1) α)
  apply (SingularCohomologyFree.cocycleClass_eq_zero_iff (cochainComplex X) (p + 1) α).mpr
  refine ⟨β, ?_⟩
  exact hβ

theorem contractible_cohomology_subsingleton (p : ℕ) : Subsingleton (Cohomology X (p + 1)) :=
  ⟨fun a b => (contractible_cohomology_eq_zero X p a).trans
    (contractible_cohomology_eq_zero X p b).symm⟩

theorem contractible_cohomology_isZero (p : ℕ) : IsZero (Cohomology X (p + 1)) := by
  let := contractible_cohomology_subsingleton X p
  exact ModuleCat.isZero_of_subsingleton _

end NoExoticSixSphere.ModTwoCapProduct

namespace NoExoticSixSphere.RelativeModTwoCochains

variable {X : Type} [TopologicalSpace X] [ContractibleSpace X] (U : Set X)

/-- The original connecting map is an isomorphism when the ambient space contracts. -/
def connectingEquiv (p : ℕ) : ModTwoCapProduct.Cohomology U (p + 1) ≃ₗ[ℤ]
    Cohomology U (p + 2) :=
  ((sequence_shortExact U).δIso (p + 1) (p + 2) rfl
    (ModTwoCapProduct.contractible_cohomology_isZero X p)
    (ModTwoCapProduct.contractible_cohomology_isZero X (p + 1))).toLinearEquiv

theorem connectingEquiv_toLinearMap (p : ℕ) :
    (connectingEquiv U p).toLinearMap = connecting U (p + 1) := rfl

end NoExoticSixSphere.RelativeModTwoCochains
