import Wikipedia.HopfProblem.SixthHurewiczChainClasses
import Wikipedia.HopfProblem.SixthHurewiczNormalizationCycleOperators
import Wikipedia.HopfProblem.SixthHurewiczSixSimplexHomology

/-!
# The sixth Hurewicz image of normalized singular-chain classes

The actual cubical representative of a based six-simplex is its original
simplex minus the constant simplex. The corrections cancel exactly on
singular six-cycles, so their normalized native classes recover every
original sixth-homology class under the genuine Hurewicz map.
-/

noncomputable section

open scoped Topology

namespace Wikipedia.HopfProblem.SixthHurewicz

open FirstHurewicz SingularMayerVietoris

variable {X : Type} [TopologicalSpace X] [SimplyConnectedSpace X]
variable (x : X) [Subsingleton (π_ 2 X x)] [Subsingleton (π_ 3 X x)]
  [Subsingleton (π_ 4 X x)] [Subsingleton (π_ 5 X x)]

/-- The original Hurewicz map sends the chain assignment to the actual corrected cycles. -/
theorem hurewiczMap_comp_sixSimplexClassOperator :
    (hurewiczMap x).comp (sixSimplexClassOperator x) =
      (ModuleHomology.cycleClass (singularComplex X) 6).comp
        (normalizedSixSimplexCycleOperator x) := by
  apply chainMap_ext X 6
  intro smp
  simp only [LinearMap.comp_apply, sixSimplexClassOperator_simplex,
    normalizedSixSimplexCycleOperator_simplex]
  exact hurewicz_basedSixSimplexClass (normalizedSixSimplex x smp)

/-- The constructed native class recovers the original class of each singular six-cycle. -/
theorem hurewiczMap_sixSimplexClassOperator_cycle
    (c : ModuleHomology.Cycle (singularComplex X) 6) :
    hurewiczMap x (sixSimplexClassOperator x c.val) =
      ModuleHomology.cycleClass (singularComplex X) 6 c := by
  have h := LinearMap.congr_fun (hurewiczMap_comp_sixSimplexClassOperator x) c.val
  change hurewiczMap x (sixSimplexClassOperator x c.val) =
    ModuleHomology.cycleClass (singularComplex X) 6
      (normalizedSixSimplexCycleOperator x c.val) at h
  exact h.trans (normalizedSixSimplexCycleOperator_class x c)

/-- Surjectivity of the actual integral-linear sixth Hurewicz map. -/
theorem hurewiczMap_surjective : Function.Surjective (hurewiczMap x) := by
  intro a
  obtain ⟨c, rfl⟩ := ModuleHomology.cycleClass_surjective (singularComplex X) 6 a
  exact ⟨sixSimplexClassOperator x c.val, hurewiczMap_sixSimplexClassOperator_cycle x c⟩

theorem hurewiczPi6_surjective : Function.Surjective (hurewiczPi6 x) := by
  intro a
  obtain ⟨b, hb⟩ := hurewiczMap_surjective x (Multiplicative.toAdd a)
  exact ⟨Additive.toMul b, congrArg Multiplicative.ofAdd hb⟩

end Wikipedia.HopfProblem.SixthHurewicz
