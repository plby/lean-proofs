import Wikipedia.HopfProblem.ThreefoldLerayEdgePicard
import Wikipedia.HopfProblem.HolomorphicPicardCechExtensionClassNaturality

/-!
# The ordinary exponential cocycle formula for the actual Picard–Leray map

A genuine holomorphic additive cocycle on any actual open cover of the
constructed threefold gives an actual native bundle by exponentiating
its literal values and gluing. The Picard–Leray equivalence sends that
bundle's original isomorphism class to the original Leray edge of the
genuine extension class of the additive cocycle.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge

open HolomorphicPushforward HolomorphicFunctionSheaf.SphereH1

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

variable {ι : Type} {U : ι → Opens Space}

/-- Literal application of the original exponential sheaf map to the
values of an actual additive holomorphic cocycle. -/
def exponentialCocycle (c : CechOneCocycle totalAdditiveSheaf U) :
    CechOneCocycle (HolomorphicExponentialSheaf.unitsSheaf IF Space) U :=
  HolomorphicPicard.Cech.mapCocycle (HolomorphicExponentialSheaf.exponential IF Space) c

/-- The transition values are the ordinary scalar exponential `exp(cᵢⱼ)`
on the actual overlap, with no changed integral normalization. -/
@[simp] theorem exponentialCocycle_eval (c : CechOneCocycle totalAdditiveSheaf U)
    (i j : ι) (x : ↥(U i ⊓ U j)) :
    HolomorphicExponentialSheaf.unitSectionEval ((exponentialCocycle c).value i j) x =
      Complex.exp ((show HolomorphicFunctionSheaf.Section IF Space (U i ⊓ U j) from
        c.value i j) x) := rfl

/-- The original native holomorphic line bundle obtained by actual gluing
with these exponentiated transitions. -/
def exponentialCocycleBundle (hU : ∀ x : Space, ∃ i, x ∈ U i)
    (c : CechOneCocycle totalAdditiveSheaf U) : HolomorphicPicard.LineBundle.{0} IF Space :=
  HolomorphicPicard.LineBundle.ofCocycle IF Space U hU (exponentialCocycle c)

/-- The actual glued bundle's class is the original exponential map of
the genuine extension class of the additive cocycle. -/
theorem exponentialCocycleBundle_cohomologyClass (hU : ∀ x : Space, ∃ i, x ∈ U i)
    (c : CechOneCocycle totalAdditiveSheaf U) :
    HolomorphicPicard.LineBundle.cohomologyClass IF Space (exponentialCocycleBundle hU c) =
      CategoryTheory.Sheaf.H.map (HolomorphicExponentialSheaf.exponential IF Space) 1
        (HolomorphicPicard.CechExtension.classOf c hU) :=
  (HolomorphicPicard.LineBundle.cohomologyClass_ofCocycle IF Space U hU
    (exponentialCocycle c)).trans
      (HolomorphicPicard.CechExtension.classOf_naturality
        (HolomorphicExponentialSheaf.exponential IF Space) c hU).symm

/-- The Picard–Leray comparison retains the actual cocycle/exponential
formula: the class of the native bundle with transitions `exp(cᵢⱼ)` maps
to the original native edge of the original additive cocycle class. -/
theorem picardGlobalSectionsEquiv_exponentialCocycleBundle
    (hU : ∀ x : Space, ∃ i, x ∈ U i)
    (c : CechOneCocycle totalAdditiveSheaf U) :
    picardGlobalSectionsEquiv (HolomorphicPicard.LineBundle.toIsoClasses IF Space
      (exponentialCocycleBundle hU c)) =
        globalEdge (HolomorphicPicard.CechExtension.classOf c hU) := by
  change edgeGlobalSectionsLinearEquiv
    (PicardExponential.picardHolomorphicH1Equiv
      (HolomorphicPicard.LineBundle.toIsoClasses IF Space (exponentialCocycleBundle hU c))) =
        edgeGlobalSectionsLinearEquiv (HolomorphicPicard.CechExtension.classOf c hU)
  apply congrArg edgeGlobalSectionsLinearEquiv
  apply PicardExponential.exponentialH1_injective
  exact (PicardExponential.exponentialH1_picardHolomorphicH1Equiv_toIsoClasses
    (exponentialCocycleBundle hU c)).trans (exponentialCocycleBundle_cohomologyClass hU c)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge
