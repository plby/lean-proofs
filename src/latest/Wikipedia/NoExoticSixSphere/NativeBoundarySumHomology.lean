import Wikipedia.HopfProblem.PeriodTorusHigherHomologyCircleDisjoint
import Wikipedia.HopfProblem.SphereHomologyCoefficientsNaturality
import Wikipedia.NoExoticSixSphere.ZeroSecondHomologyEvaluation
import Mathlib.Topology.Sets.Opens

/-!
# Actual middle homology maps for a presented disjoint boundary

The supplied homeomorphism determines the original two component maps.
Integral disjoint-union coordinates and the actual coefficient reduction
prove that their mod-two sum is surjective. If the first component has
zero mod-two middle homology, the second component map alone is surjective.
No connectedness or smooth structure on the whole boundary is assumed.
-/

noncomputable section

open Set Function ContinuousMap
open Wikipedia.HopfProblem SingularMayerVietoris PeriodTorusHigherHomology
open SphereHomologyCoefficients

namespace NoExoticSixSphere.NativeBoundarySum

variable {X Y Z : Type} [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  (h : (X ⊕ Y) ≃ₜ Z)

def inl : C(X, Z) := ⟨fun x ↦ h (Sum.inl x), h.continuous.comp continuous_inl⟩

def inr : C(Y, Z) := ⟨fun y ↦ h (Sum.inr y), h.continuous.comp continuous_inr⟩

theorem isOpenEmbedding_inl : Topology.IsOpenEmbedding (inl h) :=
  h.isOpenEmbedding.comp Topology.IsOpenEmbedding.inl

theorem isOpenEmbedding_inr : Topology.IsOpenEmbedding (inr h) :=
  h.isOpenEmbedding.comp Topology.IsOpenEmbedding.inr

theorem disjoint_inclusions : Disjoint (range (inl h)) (range (inr h)) := by
  apply Set.disjoint_left.mpr
  rintro _ ⟨x, rfl⟩ ⟨y, he⟩
  exact Sum.inr_ne_inl (h.injective he)

def integralEquiv (n : ℕ) :
    (SingularHomology X n × SingularHomology Y n) ≃ₗ[ℤ] SingularHomology Z n :=
  (sumHomologyEquiv X Y n).symm.trans (homeomorphHomologyEquiv h n)

theorem integralEquiv_apply (n : ℕ) (a : SingularHomology X n × SingularHomology Y n) :
    integralEquiv h n a = singularHomologyMap (inl h) n a.1 +
      singularHomologyMap (inr h) n a.2 := by
  change singularHomologyMap (h : C(X ⊕ Y, Z)) n ((sumHomologyEquiv X Y n).symm a) = _
  rw [sumHomologyEquiv_symm_apply, map_add, ← LinearMap.comp_apply,
    ← singularHomologyMap_comp, ← LinearMap.comp_apply, ← singularHomologyMap_comp]
  rfl

include h in
theorem target_secondHomology_subsingleton
    [Subsingleton (SingularHomology X 2)] [Subsingleton (SingularHomology Y 2)] :
    Subsingleton (SingularHomology Z 2) := (integralEquiv h 2).surjective.subsingleton

def modTwoSum : (ModHomology 2 X 3 × ModHomology 2 Y 3) →ₗ[ℤ] ModHomology 2 Z 3 :=
  ConstantSheafSingularComparison.addHomToIntLinearMap
    ((modHomologyMap 2 (inl h) 3).toAddMonoidHom.coprod
      (modHomologyMap 2 (inr h) 3).toAddMonoidHom)

theorem modTwoSum_apply (a : ModHomology 2 X 3 × ModHomology 2 Y 3) :
    modTwoSum h a = modHomologyMap 2 (inl h) 3 a.1 + modHomologyMap 2 (inr h) 3 a.2 := rfl

theorem modTwoSum_reduction (a : SingularHomology X 3 × SingularHomology Y 3) :
    modTwoSum h (reductionHomologyMap 2 X 3 a.1, reductionHomologyMap 2 Y 3 a.2) =
      reductionHomologyMap 2 Z 3 (integralEquiv h 3 a) := by
  rw [modTwoSum_apply, integralEquiv_apply, map_add,
    modHomologyMap_reduction, modHomologyMap_reduction]

variable [Subsingleton (SingularHomology Z 2)]

theorem modTwoSum_surjective : Surjective (modTwoSum h) := by
  intro b
  obtain ⟨c, rfl⟩ := ZeroSecondHomologyEvaluation.reduction_surjective Z b
  obtain ⟨a, ha⟩ := (integralEquiv h 3).surjective c
  refine ⟨(reductionHomologyMap 2 X 3 a.1, reductionHomologyMap 2 Y 3 a.2), ?_⟩
  rw [modTwoSum_reduction, ha]

theorem inr_modTwo_surjective [Subsingleton (ModHomology 2 X 3)] :
    Surjective (modHomologyMap 2 (inr h) 3) := by
  intro b
  obtain ⟨a, ha⟩ := modTwoSum_surjective h b
  refine ⟨a.2, ?_⟩
  rw [modTwoSum_apply, Subsingleton.elim a.1 0, map_zero, zero_add] at ha
  exact ha

omit [Subsingleton (SingularHomology Z 2)] in
def clopenComplementHomeomorph (U : TopologicalSpace.Opens Z) (hU : IsClosed (U : Set Z)) :
    (↥((U : Set Z)ᶜ) ⊕ U) ≃ₜ Z := by
  classical
  let e : (↥((U : Set Z)ᶜ) ⊕ U) ≃ Z :=
    (Equiv.sumComm _ _).trans (Equiv.Set.sumCompl (U : Set Z))
  have he : (e : (↥((U : Set Z)ᶜ) ⊕ U) → Z) = Sum.elim Subtype.val Subtype.val := by
    funext z
    cases z <;> rfl
  apply e.toHomeomorphOfContinuousOpen
  · rw [he]
    exact continuous_subtype_val.sumElim continuous_subtype_val
  · rw [he]
    exact hU.isOpen_compl.isOpenMap_subtype_val.sumElim U.isOpen.isOpenMap_subtype_val

omit [Subsingleton (SingularHomology Z 2)] in
theorem inr_clopenComplementHomeomorph
    (U : TopologicalSpace.Opens Z) (hU : IsClosed (U : Set Z)) :
    inr (clopenComplementHomeomorph U hU) = subtypeInclusion (U : Set Z) := rfl

end NoExoticSixSphere.NativeBoundarySum
