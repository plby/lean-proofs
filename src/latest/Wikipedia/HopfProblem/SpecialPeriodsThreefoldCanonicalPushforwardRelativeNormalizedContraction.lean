import Wikipedia.HopfProblem.SpecialPeriodsThreefoldCanonicalPushforwardRelativeNormalizedBasic

/-!
# Exact finite contraction of the normalized relative section

The proved cancellation has identity preferred fibre multiplier. On the
finite chart the actual positive section and both native contraction
factors consequently have coefficient one. Absolute canonical descent
therefore recovers exactly the original normalized form, including at
the order-four elliptic zero fibre.
-/

noncomputable section

open Bundle Set TopologicalSpace
open scoped ContDiff Manifold OnePoint

namespace Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative

open CanonicalGlobalLineBundle
open HolomorphicFunctionSheaf.SphereH1
open HolomorphicFunctionSheaf.SphereH1.NegativeOneFrames

attribute [local instance] Threefold.chartedSpace Threefold.space_isManifold

local notation "IF" => modelWithCornersSelf ℂ (ℂ × ComplexPlane₂)

/-- The actual intermediate base tensor section, before holomorphic cancellation. -/
def normalizedBaseTensorSection (U : Opens RiemannSphere) : BaseTensorSection U :=
  (baseTensorPositiveSectionLinearEquiv U).symm (Positive.sectionOn U)

/-- Genuine cancellation introduces no arbitrary scalar in the preferred fibre. -/
theorem normalizedBaseTensorSection_apply (U : Opens RiemannSphere) (p : U) :
    normalizedBaseTensorSection U p = id (α := ℂ) (Positive.sectionValue p) := by
  change (baseTensorPositiveFiberEquiv p).symm (Positive.sectionOn U p) = _
  have h := Powers.singleDualSquareFiberEquiv_apply 𝓘(ℂ) CanonicalGlobal.BaseTwist.data p
    ((baseTensorPositiveFiberEquiv p).symm (Positive.sectionOn U p))
  exact h.symm.trans ((baseTensorPositiveFiberEquiv p).apply_symm_apply (Positive.sectionOn U p))

theorem projectionFormula_normalizedSection (U : Opens RiemannSphere) :
    projectionFormulaSectionLinearEquiv U (normalizedSection U) =
      normalizedBaseTensorSection U := by
  apply (baseTensorPositiveSectionLinearEquiv U).injective
  exact (normalizedSection_positive U).trans
    ((baseTensorPositiveSectionLinearEquiv U).apply_symm_apply (Positive.sectionOn U)).symm

private theorem finite_index (p : RiemannSphere) (hp : p ∈ finiteChart) :
    CanonicalGlobal.BaseTwist.data.indexAt p = false := by
  classical
  exact if_neg ((mem_finiteChart p).mp hp)

private theorem positive_preferred_finite (p : RiemannSphere) (hp : p ∈ finiteChart) :
    id (α := ℂ) (Positive.sectionValue p) = 1 := by
  change Positive.coefficient (CanonicalGlobal.BaseTwist.data.indexAt p) p = 1
  rw [finite_index p hp]
  rfl

/-- The finite native contraction has literal preferred coefficient one. -/
theorem normalizedBaseTensorSection_contraction_finite (U : Opens RiemannSphere)
    (hU : U ≤ finiteChart) (p : U) :
    id (α := ℂ) (targetContraction false U hU (normalizedBaseTensorSection U) p) = 1 := by
  have hindex : RelativeBundle.baseData.indexAt p = false := finite_index p (hU p.property)
  change (RelativeBundle.baseData.transition (RelativeBundle.baseData.indexAt p) false p : ℂ) *
    id (α := ℂ) (normalizedBaseTensorSection U p) = 1
  rw [hindex, RelativeBundle.baseData.transition_self false p (hU p.property),
    Units.val_one, one_mul, normalizedBaseTensorSection_apply]
  exact positive_preferred_finite p (hU p.property)

/-- The actual absolute ideal section obtained by finite contraction. -/
def normalizedAbsoluteIdeal (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    NegativeOneSection U :=
  BaseIdeal.sectionLinearEquiv U
    (targetContraction false U hU (normalizedBaseTensorSection U))

/-- Its literal holomorphic function is one on the whole original finite subopen. -/
theorem normalizedAbsoluteIdeal_apply (U : Opens RiemannSphere) (hU : U ≤ finiteChart)
    (p : U) : (normalizedAbsoluteIdeal U hU).val p = 1 := by
  rw [normalizedAbsoluteIdeal,
    BaseIdeal.sectionLinearEquiv_value U _ false p (hU p.property),
    CanonicalGlobal.BaseTwist.idealFrameValue_false, mul_one,
    HolomorphicCharacterBundle.TransitionData.core_localTriv_apply,
    finite_index p (hU p.property),
    CanonicalGlobal.BaseTwist.data.transition_self false p (hU p.property),
    Units.val_one, one_mul]
  exact normalizedBaseTensorSection_contraction_finite U hU p

/-- The actual local projection formula determines the contracted absolute ideal section. -/
theorem normalizedSection_contracted_ideal (U : Opens RiemannSphere) (hU : U ≤ finiteChart) :
    presentationToIdealLinearEquiv U (sourceContraction false U hU (normalizedSection U)) =
      normalizedAbsoluteIdeal U hU := by
  have hp := projectionFormula_normalizedSection U
  rw [projectionFormulaSectionLinearEquiv_eq_local false U hU] at hp
  have hc := (targetContraction_localLinearEquiv false U hU (normalizedSection U)).symm.trans
    (congrArg (targetContraction false U hU) hp)
  have h := congrArg (BaseIdeal.sectionLinearEquiv U) hc
  change (BaseIdeal.sectionLinearEquiv U)
      ((BaseIdeal.sectionLinearEquiv U).symm
        (presentationToIdealLinearEquiv U
          (sourceContraction false U hU (normalizedSection U)))) =
    normalizedAbsoluteIdeal U hU at h
  rw [LinearEquiv.apply_symm_apply] at h
  exact h

/-- Finite contraction recovers the actual absolute canonical section, not a formal generator. -/
theorem normalizedSection_sourceContraction (U : Opens RiemannSphere)
    (hU : U ≤ finiteChart) :
    sourceContraction false U hU (normalizedSection U) =
      nativePresentationSectionLinearEquiv (Threefold.basePreimage U)
        ((canonicalSectionIdealEquiv U).symm (normalizedAbsoluteIdeal U hU)) := by
  have h := congrArg (presentationToIdealLinearEquiv U).symm
    (normalizedSection_contracted_ideal U hU)
  exact ((presentationToIdealLinearEquiv U).symm_apply_apply _).symm.trans h

/-- The contraction is exactly the native presentation of the original Ω at every finite point. -/
theorem normalizedSection_sourceContraction_finite_value (U : Opens RiemannSphere)
    (hU : U ≤ finiteChart) (x : Threefold.basePreimage U) :
    sourceContraction false U hU (normalizedSection U) x =
      NativePresentation.fiberEquiv x.val (GlobalMeromorphicSection.rawSection x.val) := by
  have hs := congrArg
    (fun s : PresentationSection (Threefold.basePreimage U) => s x)
    (normalizedSection_sourceContraction U hU)
  have hf := canonicalSectionIdealEquiv_symm_finite U (normalizedAbsoluteIdeal U hU) x
    ((mem_finiteChart _).mp (hU x.property))
  rw [normalizedAbsoluteIdeal_apply, one_smul] at hf
  exact hs.trans (congrArg (NativePresentation.fiberEquiv x.val) hf)

end Wikipedia.HopfProblem.SpecialPeriods.Threefold.Canonical.Pushforward.Relative
