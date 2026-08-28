import Wikipedia.HopfProblem.FifthHurewiczChainClasses
import Wikipedia.HopfProblem.FifthHurewiczNormalizationCycleOperators
import Wikipedia.HopfProblem.FifthHurewiczFiveSimplexHomology

/-!
# The fifth Hurewicz image of normalized singular-chain classes

The actual cubical representative of a based five-simplex is its
original simplex minus the constant simplex. The constant correction
is a genuine six-boundary, and the constructed prism preserves the
original class of every actual five-cycle.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.FifthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)]

/-- The original Hurewicz map sends the chain assignment to the actual corrected cycles. -/
theorem hurewiczMap_comp_fiveSimplexClassOperator :
    (hurewiczMap x).comp (fiveSimplexClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 5).comp
        (normalizedFiveSimplexCycleOperator x) := by
  apply chainMap_ext X 5
  intro smp
  simp only [LinearMap.comp_apply, fiveSimplexClassOperator_simplex,
    normalizedFiveSimplexCycleOperator_simplex]
  exact hurewicz_basedFiveSimplexClass (normalizedFiveSimplex x smp)

/-- The constructed native class recovers the original class of each singular five-cycle. -/
theorem hurewiczMap_fiveSimplexClassOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 5) :
    hurewiczMap x (fiveSimplexClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 5 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_fiveSimplexClassOperator x) c.val
  change hurewiczMap x (fiveSimplexClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 5
      (normalizedFiveSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedFiveSimplexCycleOperator_class x c)

/-- Surjectivity of the actual integral-linear fifth Hurewicz map. -/
theorem hurewiczMap_surjective : Function.Surjective (hurewiczMap x) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 5 a
  exact ⟨fiveSimplexClassOperator x c.val, hurewiczMap_fiveSimplexClassOperator_cycle x c⟩

theorem hurewiczPi5_surjective : Function.Surjective (hurewiczPi5 x) := by
  intro a
  obtain ⟨b, hb⟩ := hurewiczMap_surjective x (Multiplicative.toAdd a)
  exact ⟨Additive.toMul b, congrArg Multiplicative.ofAdd hb⟩

end Wikipedia.HopfProblem.FifthHurewicz
