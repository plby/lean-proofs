import Wikipedia.HopfProblem.ThirdHurewiczChainClasses
import Wikipedia.HopfProblem.ThirdHurewiczNormalizationCycleOperators
import Wikipedia.HopfProblem.ThirdHurewiczThreeSimplexHomology

/-!
# The genuine Hurewicz image of normalized singular-chain classes

The actual cubical representative of each based three-simplex is its
original singular simplex minus the constant simplex. Linearization and
the explicit four-boundary correction therefore recover the original
third homology class of every actual singular three-cycle.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.ThirdHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)]

/-- The genuine native Hurewicz map of the chain assignment is exactly
the corrected original singular-cycle assignment. -/
theorem hurewiczMap_comp_threeSimplexClassOperator :
    (hurewiczMap x).comp (threeSimplexClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 3).comp
        (normalizedThreeSimplexCycleOperator x) := by
  apply chainMap_ext X 3
  intro smp
  simp only [LinearMap.comp_apply, threeSimplexClassOperator_simplex,
    normalizedThreeSimplexCycleOperator_simplex]
  exact hurewicz_basedThreeSimplexClass (normalizedThreeSimplex x smp)

/-- Every original actual cycle class is recovered, with no assumed
isomorphism or comparison map. -/
theorem hurewiczMap_threeSimplexClassOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 3) :
    hurewiczMap x (threeSimplexClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 3 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_threeSimplexClassOperator x) c.val
  change hurewiczMap x (threeSimplexClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 3
      (normalizedThreeSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedThreeSimplexCycleOperator_class x c)

/-- Surjectivity of the actual native degree-three Hurewicz map in
integral-linear notation follows already from the explicit cycle construction. -/
theorem hurewiczMap_surjective : Function.Surjective (hurewiczMap x) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 3 a
  exact ⟨threeSimplexClassOperator x c.val, hurewiczMap_threeSimplexClassOperator_cycle x c⟩

theorem hurewiczPi3_surjective : Function.Surjective (hurewiczPi3 x) := by
  intro a
  obtain ⟨b, hb⟩ := hurewiczMap_surjective x (Multiplicative.toAdd a)
  exact ⟨Additive.toMul b, congrArg Multiplicative.ofAdd hb⟩

end Wikipedia.HopfProblem.ThirdHurewicz
