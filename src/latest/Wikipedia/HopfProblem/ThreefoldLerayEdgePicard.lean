import Wikipedia.HopfProblem.ThreefoldLerayEdgeSections
import Wikipedia.HopfProblem.ThreefoldPicardExponential

/-!
# Native Picard classes and global sections of the actual first direct image

The genuine holomorphic exponential identifies the original native Picard
group of the constructed threefold with its actual holomorphic `H¹`.
Composing with the original Leray edge gives an additive equivalence with
literal global sections of the genuine `R¹ f_* O_X`. The formulas below
retain the actual exponential map and the original native bundle cocycle.

No value, splitting, or dimension of the higher direct image is asserted.
-/

noncomputable section

open CategoryTheory TopologicalSpace
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge

attribute [local instance] chartedSpace

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The original tensor-product Picard group of actual native holomorphic
line bundles, compared with sections of the actual derived sheaf. -/
def picardGlobalSectionsEquiv : PicardExponential.PicardGroup ≃+ HigherGlobalSections :=
  PicardExponential.picardHolomorphicH1Equiv.trans edgeGlobalSectionsLinearEquiv.toAddEquiv

/-- The Picard comparison uses the original exponential preimage and the
original Leray edge, with their original native domains and targets. -/
@[simp] theorem picardGlobalSectionsEquiv_apply (x : PicardExponential.PicardGroup) :
    picardGlobalSectionsEquiv x =
      globalEdge (PicardExponential.picardHolomorphicH1Equiv x) := rfl

@[simp] theorem picardGlobalSectionsEquiv_symm_apply (s : HigherGlobalSections) :
    picardGlobalSectionsEquiv.symm s = PicardExponential.picardHolomorphicH1Equiv.symm
      (edgeGlobalSectionsLinearEquiv.symm s) := rfl

/-- Inverting the edge and applying the actual sheaf exponential returns
exactly the original unit-sheaf class of the native bundle class. -/
theorem exponentialH1_picardGlobalSectionsEquiv (x : PicardExponential.PicardGroup) :
    CategoryTheory.Sheaf.H.map (HolomorphicExponentialSheaf.exponential IF Space) 1
      (edgeGlobalSectionsLinearEquiv.symm (picardGlobalSectionsEquiv x)) =
        HolomorphicPicard.LineBundle.isoClassCohomologyClass IF Space x := by
  change PicardExponential.exponentialH1
    (edgeGlobalSectionsLinearEquiv.symm
      (edgeGlobalSectionsLinearEquiv (PicardExponential.picardHolomorphicH1Equiv x))) = _
  rw [edgeGlobalSectionsLinearEquiv.symm_apply_apply]
  exact PicardExponential.exponentialH1_picardHolomorphicH1Equiv x

/-- The formula specializes to every original native holomorphic line
bundle and its original genuine unit-sheaf cohomology class. -/
theorem exponentialH1_picardGlobalSectionsEquiv_toIsoClasses
    (V : HolomorphicPicard.LineBundle.{0} IF Space) :
    CategoryTheory.Sheaf.H.map (HolomorphicExponentialSheaf.exponential IF Space) 1
      (edgeGlobalSectionsLinearEquiv.symm (picardGlobalSectionsEquiv
        (HolomorphicPicard.LineBundle.toIsoClasses IF Space V))) =
          HolomorphicPicard.LineBundle.cohomologyClass IF Space V :=
  exponentialH1_picardGlobalSectionsEquiv _

/-- In particular the unit class is the genuine extension class of the
actual native transition cocycle, not a replacement classification datum. -/
theorem exponentialH1_picardGlobalSectionsEquiv_nativeCocycle
    (V : HolomorphicPicard.LineBundle.{0} IF Space) :
    CategoryTheory.Sheaf.H.map (HolomorphicExponentialSheaf.exponential IF Space) 1
      (edgeGlobalSectionsLinearEquiv.symm (picardGlobalSectionsEquiv
        (HolomorphicPicard.LineBundle.toIsoClasses IF Space V))) =
          HolomorphicPicard.CechExtension.classOf
            (HolomorphicPicardNative.nativeCocycle IF Space V.Fiber)
            (HolomorphicPicardNative.nativeCover_covers Space V.Fiber) :=
  exponentialH1_picardGlobalSectionsEquiv_toIsoClasses V

/-- Conversely, the bundle class assigned to a literal global section
has the original exponential of its genuine inverse-edge class. -/
theorem picardGlobalSectionsEquiv_symm_class (s : HigherGlobalSections) :
    HolomorphicPicard.LineBundle.isoClassCohomologyClass IF Space
      (picardGlobalSectionsEquiv.symm s) =
        CategoryTheory.Sheaf.H.map (HolomorphicExponentialSheaf.exponential IF Space) 1
          (edgeGlobalSectionsLinearEquiv.symm s) :=
  PicardExponential.picardHolomorphicH1Equiv_symm_class _

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.LerayEdge
