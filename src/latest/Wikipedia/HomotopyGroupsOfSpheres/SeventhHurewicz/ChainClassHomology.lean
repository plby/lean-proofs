import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.ChainClasses
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.NormalizationCycleOperators
import Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz.SevenSimplexHomology

/-!
# The seventh Hurewicz image of normalized singular-chain classes

The actual cubical representative of a based seven-simplex is its original
simplex minus the constant simplex. The constant correction is a boundary
in degree seven, so normalized native classes recover every original
seventh-homology class under the Hurewicz map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz

open Wikipedia.HopfProblem

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)] [Subsingleton (π_ 6 X x)]

/-- The original Hurewicz map sends the chain assignment to the actual corrected cycles. -/
theorem hurewiczMap_comp_sevenSimplexClassOperator :
    (hurewiczMap x).comp (sevenSimplexClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 7).comp
        (normalizedSevenSimplexCycleOperator x) := by
  apply chainMap_ext X 7
  intro smp
  simp only [LinearMap.comp_apply, sevenSimplexClassOperator_simplex,
    normalizedSevenSimplexCycleOperator_simplex]
  exact hurewicz_basedSevenSimplexClass (normalizedSevenSimplex x smp)

/-- The constructed native class recovers the original class of each singular seven-cycle. -/
theorem hurewiczMap_sevenSimplexClassOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 7) :
    hurewiczMap x (sevenSimplexClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 7 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_sevenSimplexClassOperator x) c.val
  change hurewiczMap x (sevenSimplexClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 7
      (normalizedSevenSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedSevenSimplexCycleOperator_class x c)

/-- Surjectivity of the actual integral-linear seventh Hurewicz map. -/
theorem hurewiczMap_surjective : Function.Surjective (hurewiczMap x) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 7 a
  exact ⟨sevenSimplexClassOperator x c.val, hurewiczMap_sevenSimplexClassOperator_cycle x c⟩

theorem hurewiczPi7_surjective : Function.Surjective (hurewiczPi7 x) := by
  intro a
  obtain ⟨b, hb⟩ := hurewiczMap_surjective x (Multiplicative.toAdd a)
  exact ⟨Additive.toMul b, congrArg Multiplicative.ofAdd hb⟩

end Wikipedia.HomotopyGroupsOfSpheres.SeventhHurewicz
