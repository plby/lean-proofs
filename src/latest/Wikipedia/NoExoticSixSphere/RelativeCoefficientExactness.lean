import Wikipedia.NoExoticSixSphere.RelativeCoefficientComplex
import Wikipedia.NoExoticSixSphere.ShortExactCokernelRows
import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Exact coefficient sequences on actual relative singular complexes

The original coefficient-change functor on relative complexes preserves
short exact sequences. The proof compares it with the cokernel row of the
two native absolute coefficient sequences and applies the snake lemma.
No freeness or exactness of relative chains is an input assumption.
-/

noncomputable section

open CategoryTheory Limits
open Wikipedia.HopfProblem SingularMayerVietoris SphereHomologyCoefficients

namespace NoExoticSixSphere.RelativeCoefficients

variable {X : Type} [TopologicalSpace X]
  (S : ShortComplex (ModuleCat.{0} ℤ)) (U : Set X)

def cokernelComparison₁ : complex S.X₁ U ⟶ (cokernel (inclusionSequenceMap S U)).X₁ :=
  cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₁

def cokernelComparison₂ : complex S.X₂ U ⟶ (cokernel (inclusionSequenceMap S U)).X₂ :=
  cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₂

def cokernelComparison₃ : complex S.X₃ U ⟶ (cokernel (inclusionSequenceMap S U)).X₃ :=
  cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₃

def rowProjection₁ :
    coefficientComplex S.X₁ X ⟶ (cokernel (inclusionSequenceMap S U)).X₁ :=
  (cokernel.π (inclusionSequenceMap S U)).τ₁

def rowProjection₂ :
    coefficientComplex S.X₂ X ⟶ (cokernel (inclusionSequenceMap S U)).X₂ :=
  (cokernel.π (inclusionSequenceMap S U)).τ₂

def rowProjection₃ :
    coefficientComplex S.X₃ X ⟶ (cokernel (inclusionSequenceMap S U)).X₃ :=
  (cokernel.π (inclusionSequenceMap S U)).τ₃

theorem rowProjection_comm₁₂ :
    rowProjection₁ S U ≫ (cokernel (inclusionSequenceMap S U)).f =
      coefficientComplexMap S.f X ≫ rowProjection₂ S U :=
  (cokernel.π (inclusionSequenceMap S U)).comm₁₂

theorem rowProjection_comm₂₃ :
    rowProjection₂ S U ≫ (cokernel (inclusionSequenceMap S U)).g =
      coefficientComplexMap S.g X ≫ rowProjection₃ S U :=
  (cokernel.π (inclusionSequenceMap S U)).comm₂₃

theorem projection_cokernelComparison₁ :
    projection S.X₁ U ≫ cokernelComparison₁ S U =
      rowProjection₁ S U :=
  π_comp_cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₁

theorem projection_cokernelComparison₂ :
    projection S.X₂ U ≫ cokernelComparison₂ S U =
      rowProjection₂ S U :=
  π_comp_cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₂

theorem projection_cokernelComparison₃ :
    projection S.X₃ U ≫ cokernelComparison₃ S U =
      rowProjection₃ S U :=
  π_comp_cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₃

/-- The comparison with the actual cokernel row retains each original coefficient map. -/
def sequenceCokernelComparison : S.map (functor U) ⟶ cokernel (inclusionSequenceMap S U) where
  τ₁ := cokernelComparison₁ S U
  τ₂ := cokernelComparison₂ S U
  τ₃ := cokernelComparison₃ S U
  comm₁₂ := by
    apply (cancel_epi (cokernel.π (inclusion S.X₁ U))).mp
    change projection S.X₁ U ≫ (_ ≫ _) = projection S.X₁ U ≫ (change S.f U ≫ _)
    rw [← Category.assoc, projection_cokernelComparison₁,
      rowProjection_comm₁₂,
      ← Category.assoc, projection_change, Category.assoc, projection_cokernelComparison₂]
  comm₂₃ := by
    apply (cancel_epi (cokernel.π (inclusion S.X₂ U))).mp
    change projection S.X₂ U ≫ (_ ≫ _) = projection S.X₂ U ≫ (change S.g U ≫ _)
    rw [← Category.assoc, projection_cokernelComparison₂,
      rowProjection_comm₂₃,
      ← Category.assoc, projection_change, Category.assoc, projection_cokernelComparison₃]

instance sequenceCokernelComparison_isIso : IsIso (sequenceCokernelComparison S U) := by
  apply (ShortComplex.isIso_iff _).mpr
  refine ⟨?_, ?_, ?_⟩
  · exact inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₁))
  · exact inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₂))
  · exact inferInstanceAs (IsIso (cokernelComparison (inclusionSequenceMap S U) ShortComplex.π₃))

/-- Any actual short exact coefficient sequence remains short exact on relative chains. -/
theorem functor_shortExact (hS : S.ShortExact) : (S.map (functor U)).ShortExact := by
  have : Mono (inclusionSequenceMap S U).τ₃ := inclusion_mono S.X₃ U
  have h := ShortExactCokernelRows.cokernel_shortExact (inclusionSequenceMap S U)
    (nativeCoefficientFunctor_shortExact U S hS) (nativeCoefficientFunctor_shortExact X S hS)
  exact ShortComplex.shortExact_of_iso (asIso (sequenceCokernelComparison S U)).symm h

end NoExoticSixSphere.RelativeCoefficients
