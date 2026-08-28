import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtTruncation
import Wikipedia.HopfProblem.ConstantSheafSingularComparisonPushforwardExtFunctor

/-!
# Degree-zero comparisons for the actual pushed augmented resolution
-/

noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt

open CuspNormalization.SheafCohomologyResolution
open CuspNormalization.SheafCohomologyFinitePushforward

variable {X Y : TopCat.{0}} [T2Space X] (f : X ⟶ Y)
  (hf : IsClosedMap f) (hfinite : ∀ y : Y, (f ⁻¹' {y}).Finite)
  (R : AugmentedResolution (AbelianSheaf X))

/-- The actual native degree-zero Ext comparison on the three terms. -/
def extZeroForwardMap : R.extZeroComplex (unitSheaf X) ⟶
    (pushforwardAugmentedResolution f hf hfinite R).extZeroComplex (unitSheaf Y) := by
  letI := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  letI := pushforward_preservesFiniteColimits f hf hfinite
  exact PushforwardExtFunctor.extZeroMap (pushforward f) (integerUnit f) R

/-- The actual induced native Ext-zero cokernel map. -/
def extCokernelForwardMap : cokernel (R.extZeroComplex (unitSheaf X)).g ⟶
    cokernel ((pushforwardAugmentedResolution f hf hfinite R).extZeroComplex (unitSheaf Y)).g := by
  letI := (pushforward_preservesFiniteLimitsAndColimits f hf hfinite).1
  letI := pushforward_preservesFiniteColimits f hf hfinite
  exact PushforwardExtFunctor.extCokernelMap (pushforward f) (integerUnit f) R

@[reassoc] theorem extCokernelForwardMap_π :
    cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫ extCokernelForwardMap f hf hfinite R =
      forwardHom f hf hfinite R.complex.X₃ 0 ≫
        cokernel.π
          ((pushforwardAugmentedResolution f hf hfinite R).extZeroComplex (unitSheaf Y)).g :=
  cokernel.π_desc _ _ _

/-- The native Ext-zero maps preserve the literal three-term
global-section complex, term by term. -/
theorem extZeroGlobal_forward :
    extZeroForwardMap f hf hfinite R ≫
        (pushforwardAugmentedResolution f hf hfinite R).extZeroGlobalIso.hom =
      R.extZeroGlobalIso.hom := by
  apply ShortComplex.hom_ext
  · exact h0Global_forward f hf hfinite R.complex.X₁
  · exact h0Global_forward f hf hfinite R.complex.X₂
  · exact h0Global_forward f hf hfinite R.complex.X₃

/-- The native Ext-zero cokernel map preserves the literal
global-section cokernel comparison. -/
theorem extGlobalCokernel_forward :
    extCokernelForwardMap f hf hfinite R ≫
        (pushforwardAugmentedResolution f hf hfinite R).extGlobalCokernelIso.hom =
      R.extGlobalCokernelIso.hom := by
  let Q := pushforwardAugmentedResolution f hf hfinite R
  apply (cancel_epi (cokernel.π (R.extZeroComplex (unitSheaf X)).g)).mp
  have h₁ : cokernel.π (R.extZeroComplex (unitSheaf X)).g ≫
        (extCokernelForwardMap f hf hfinite R ≫ Q.extGlobalCokernelIso.hom) =
      (forwardHom f hf hfinite R.complex.X₃ 0 ≫
        cokernel.π (Q.extZeroComplex (unitSheaf Y)).g) ≫ Q.extGlobalCokernelIso.hom :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ Q.extGlobalCokernelIso.hom)
        (extCokernelForwardMap_π f hf hfinite R))
  have h₂ : (forwardHom f hf hfinite R.complex.X₃ 0 ≫
        cokernel.π (Q.extZeroComplex (unitSheaf Y)).g) ≫ Q.extGlobalCokernelIso.hom =
      forwardHom f hf hfinite R.complex.X₃ 0 ≫
        ((h0GlobalIso Q.complex.X₃).hom ≫ cokernel.π R.globalComplex.g) :=
    (Category.assoc _ _ _).trans
      (congrArg (fun k => forwardHom f hf hfinite R.complex.X₃ 0 ≫ k)
        Q.extGlobalCokernelIso_π)
  have h₃ : forwardHom f hf hfinite R.complex.X₃ 0 ≫
        ((h0GlobalIso Q.complex.X₃).hom ≫ cokernel.π R.globalComplex.g) =
      (h0GlobalIso R.complex.X₃).hom ≫ cokernel.π R.globalComplex.g :=
    (Category.assoc _ _ _).symm.trans
      (congrArg (fun k => k ≫ cokernel.π R.globalComplex.g)
        (h0Global_forward f hf hfinite R.complex.X₃))
  exact h₁.trans (h₂.trans (h₃.trans R.extGlobalCokernelIso_π.symm))

end Wikipedia.HopfProblem.ConstantSheafSingularComparison.PushforwardExt
