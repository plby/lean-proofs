import Wikipedia.HopfProblem.FourthHurewiczChainClasses
import Wikipedia.HopfProblem.FourthHurewiczNormalizationCycleOperators
import Wikipedia.HopfProblem.FourthHurewiczFourSimplexHomology

/-!
# The genuine fourth Hurewicz image of normalized singular-chain classes

The actual cubical representative of a based four-simplex is its original
simplex minus the constant simplex. The corrections cancel exactly on
singular four-cycles, so their normalized native classes recover every
original fourth-homology class under the genuine Hurewicz map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FourthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]

/-- The original Hurewicz map sends the chain assignment to the actual corrected cycles. -/
theorem hurewiczMap_comp_fourSimplexClassOperator :
    (hurewiczMap x).comp (fourSimplexClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 4).comp
        (normalizedFourSimplexCycleOperator x) := by
  apply chainMap_ext X 4
  intro smp
  simp only [LinearMap.comp_apply, fourSimplexClassOperator_simplex,
    normalizedFourSimplexCycleOperator_simplex]
  exact hurewicz_basedFourSimplexClass (normalizedFourSimplex x smp)

/-- The constructed native class recovers the original class of each actual singular four-cycle. -/
theorem hurewiczMap_fourSimplexClassOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 4) :
    hurewiczMap x (fourSimplexClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 4 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fourSimplexClassOperator x) c.val
  change hurewiczMap x (fourSimplexClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 4
      (normalizedFourSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFourSimplexCycleOperator_class x c)

/-- Surjectivity of the actual integral-linear fourth Hurewicz map. -/
theorem hurewiczMap_surjective : Function.Surjective (hurewiczMap x) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 4 a
  exact ⟨fourSimplexClassOperator x c.val, hurewiczMap_fourSimplexClassOperator_cycle x c⟩

theorem hurewiczPi4_surjective : Function.Surjective (hurewiczPi4 x) := by
  intro a
  obtain ⟨b, hb⟩ := hurewiczMap_surjective x (Multiplicative.toAdd a)
  exact ⟨Additive.toMul b, congrArg Multiplicative.ofAdd hb⟩

end Wikipedia.HopfProblem.FourthHurewicz
