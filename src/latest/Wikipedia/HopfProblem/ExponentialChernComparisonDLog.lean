import Wikipedia.HopfProblem.ExponentialChernComparisonCochainZero
import Wikipedia.HopfProblem.ExponentialChernComparisonDLogResolution
import Wikipedia.HopfProblem.HolomorphicExponentialSheafSequence

/-!
# The actual logarithmic differential from the exponential cokernel

Evaluate a holomorphic function on the original singular vertices and
apply the original cochain differential, with target restricted to its
actual kernel. The ordinary-exponential integer inclusion maps to zero
by the constant augmentation square. The genuine cokernel property of
the original exponential therefore descends this map to the units sheaf.
This constructs a morphism of the original short exact sequences, without
assuming global logarithms or a cohomology-class comparison.
-/

noncomputable section

open TopologicalSpace Opposite CategoryTheory CategoryTheory.Limits
open scoped ContDiff Manifold

namespace Wikipedia.HopfProblem.ExponentialChernComparison.DLog

open ConstantSheafSingularComparison HolomorphicExponentialSheaf

private theorem square_comp_zero {C : Type*} [Category C] [HasZeroMorphisms C]
    (S T : ShortComplex C) (a : S.X₁ ⟶ T.X₁) (b : S.X₂ ⟶ T.X₂)
    (hab : S.f ≫ b = a ≫ T.f) : S.f ≫ (b ≫ T.g) = 0 := by
  rw [← Category.assoc, hab, Category.assoc, T.zero, comp_zero]

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [TopologicalSpace H] (I : ModelWithCorners ℂ E H)
    (M : Type) [TopologicalSpace M] [ChartedSpace H M]
    (hLC : LocallyContractibleSpace M)

/-- The evaluated integer periods vanish under the original differential
into the actual first kernel. -/
theorem integerInclusion_evaluate_toK :
    (exponentialComplex I M).f ≫
        (CochainZero.evaluate I M ≫ (resolution (TopCat.of M) hLC).toK) = 0 :=
  square_comp_zero (exponentialComplex I M) (resolution (TopCat.of M) hLC).first
    (CochainZero.integerCoefficientMap (TopCat.of M)) (CochainZero.evaluate I M)
    (CochainZero.integerInclusion_evaluate I M)

/-- The actual logarithmic differential, descended through the genuine
cokernel of the original integer-period inclusion. -/
def dlog : unitsSheaf I M ⟶ (resolution (TopCat.of M) hLC).K :=
  (exponentialComplex_exact I M).desc
    (CochainZero.evaluate I M ≫ (resolution (TopCat.of M) hLC).toK)
    (integerInclusion_evaluate_toK I M hLC)

/-- On actual exponential sections the descended map is exactly the
original evaluated cochain differential into its genuine kernel. -/
@[reassoc] theorem exponential_dlog :
    exponential I M ≫ dlog I M hLC =
      CochainZero.evaluate I M ≫ (resolution (TopCat.of M) hLC).toK :=
  (exponentialComplex_exact I M).g_desc
    (CochainZero.evaluate I M ≫ (resolution (TopCat.of M) hLC).toK)
    (integerInclusion_evaluate_toK I M hLC)

/-- The original exponential epimorphism uniquely determines this map. -/
theorem dlog_unique (f : unitsSheaf I M ⟶ (resolution (TopCat.of M) hLC).K)
    (hf : exponential I M ≫ f =
      CochainZero.evaluate I M ≫ (resolution (TopCat.of M) hLC).toK) :
    f = dlog I M hLC := by
  apply (cancel_epi (exponential I M)).mp
  exact hf.trans (exponential_dlog I M hLC).symm

/-- The original exponential sequence maps to the actual first sequence
of the constant-complex singular-cochain resolution. -/
def complexMap : exponentialComplex I M ⟶ (resolution (TopCat.of M) hLC).first where
  τ₁ := CochainZero.integerCoefficientMap (TopCat.of M)
  τ₂ := CochainZero.evaluate I M
  τ₃ := dlog I M hLC
  comm₁₂ := (CochainZero.integerInclusion_evaluate I M).symm
  comm₂₃ := (exponential_dlog I M hLC).symm

@[simp] theorem complexMap_τ₁ :
    (complexMap I M hLC).τ₁ = CochainZero.integerCoefficientMap (TopCat.of M) := rfl

@[simp] theorem complexMap_τ₂ :
    (complexMap I M hLC).τ₂ = CochainZero.evaluate I M := rfl

@[simp] theorem complexMap_τ₃ :
    (complexMap I M hLC).τ₃ = dlog I M hLC := rfl

/-- Including the kernel gives the literal native cochain differential
of the original holomorphic evaluation map. -/
@[reassoc] theorem exponential_dlog_ι :
    exponential I M ≫ dlog I M hLC ≫
        kernel.ι (resolution (TopCat.of M) hLC).complex.g =
      CochainZero.evaluate I M ≫
        sheafDifferential (TopCat.of M) (AddCommGrpCat.of ℂ) 0 1 := by
  let R := resolution (TopCat.of M) hLC
  calc
    _ = (exponential I M ≫ dlog I M hLC) ≫ kernel.ι R.complex.g :=
      (Category.assoc _ _ _).symm
    _ = (CochainZero.evaluate I M ≫ R.toK) ≫ kernel.ι R.complex.g :=
      congrArg (fun f => f ≫ kernel.ι R.complex.g) (exponential_dlog I M hLC)
    _ = CochainZero.evaluate I M ≫ (R.toK ≫ kernel.ι R.complex.g) :=
      Category.assoc _ _ _
    _ = _ := congrArg (fun f => CochainZero.evaluate I M ≫ f)
      (resolution_toK_ι (TopCat.of M) hLC)

/-- The quotient construction retains the actual value on each locally
given holomorphic logarithm. -/
theorem dlog_exponential_app (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    (dlog I M hLC).hom.app (op U) ((exponential I M).hom.app (op U) f) =
      (resolution (TopCat.of M) hLC).toK.hom.app (op U)
        ((CochainZero.evaluate I M).hom.app (op U) f) :=
  ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun e => e.hom) (exponential_dlog I M hLC)) (op U)) f

/-- After the original kernel inclusion, an actual local logarithm gives
the sheafification unit of its literal singular zero-cochain coboundary. -/
theorem dlog_exponential_app_ι (U : Opens M)
    (f : HolomorphicFunctionSheaf.Section I M U) :
    (kernel.ι (resolution (TopCat.of M) hLC).complex.g).hom.app (op U)
        ((dlog I M hLC).hom.app (op U) ((exponential I M).hom.app (op U) f)) =
      (cochainSheafUnit (TopCat.of M) (AddCommGrpCat.of ℂ) 1).app (op U)
        ((singularCochainComplex U (AddCommGrpCat.of ℂ)).d 0 1
          (CochainZero.evaluateSections I M U f)) := by
  have h := ConcreteCategory.congr_hom
    (NatTrans.congr_app (congrArg (fun e => e.hom) (exponential_dlog_ι I M hLC)) (op U)) f
  change (kernel.ι (resolution (TopCat.of M) hLC).complex.g).hom.app (op U)
      ((dlog I M hLC).hom.app (op U) ((exponential I M).hom.app (op U) f)) =
    (sheafDifferential (TopCat.of M) (AddCommGrpCat.of ℂ) 0 1).hom.app (op U)
      ((CochainZero.evaluate I M).hom.app (op U) f) at h
  rw [h, CochainZero.evaluate_app]
  exact ConcreteCategory.congr_hom
    (NatTrans.congr_app
      (cochainSheafUnit_d (TopCat.of M) (AddCommGrpCat.of ℂ) 0 1) (op U))
    (CochainZero.evaluateSections I M U f)

end Wikipedia.HopfProblem.ExponentialChernComparison.DLog
