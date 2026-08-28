import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicCayley
import Wikipedia.HomotopyGroupsOfSpheres.FiniteSubmoduleProjection

/-! # Smooth Cayley atlas on the quaternionic operator group -/

noncomputable section

open scoped Manifold ContDiff
open Set

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.CayleyTransform

namespace CayleyAtlas

variable {n : ℕ}

def leftTranslate (a : symplecticSubgroup n) : symplecticSubgroup n ≃ₜ symplecticSubgroup n where
  toFun b := a * b
  invFun b := a⁻¹ * b
  left_inv b := inv_mul_cancel_left a b
  right_inv b := mul_inv_cancel_left a b
  continuous_toFun := continuous_const.mul continuous_id
  continuous_invFun := continuous_const.mul continuous_id

def atOperator (a : symplecticSubgroup n) :
    OpenPartialHomeomorph (symplecticSubgroup n) (SkewSpace n) :=
  (leftTranslate a).symm.toOpenPartialHomeomorph.trans (cayleyChart n)

theorem atOperator_apply (a b : symplecticSubgroup n) :
    atOperator a b = cayleyCoordinates n (a⁻¹ * b) := rfl

theorem atOperator_symm_apply (a : symplecticSubgroup n) (K : SkewSpace n) :
    (atOperator a).symm K = a * symplecticCayley n K := rfl

theorem atOperator_source (a : symplecticSubgroup n) :
    (atOperator a).source = {b | a⁻¹ * b ∈ cayleyDomain n} := by
  ext b
  change (b ∈ univ ∧ a⁻¹ * b ∈ cayleyDomain n) ↔ _
  simp only [mem_univ, true_and, mem_ofPred_eq]

theorem mem_atOperator_source (a : symplecticSubgroup n) : a ∈ (atOperator a).source := by
  rw [atOperator_source]
  change a⁻¹ * a ∈ cayleyDomain n
  rw [inv_mul_cancel]
  exact one_mem_cayleyDomain n

instance chartedSpace (n : ℕ) : ChartedSpace (SkewSpace n) (symplecticSubgroup n) where
  atlas := range atOperator
  chartAt := atOperator
  mem_chart_source := mem_atOperator_source
  chart_mem_atlas a := ⟨a, rfl⟩

/-- The original inclusion of the quaternionic skew model into real operators. -/
def skewInclusion (n : ℕ) : SkewSpace n →L[ℝ]
    (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) :=
  (skewSubmodule n).subtypeL

theorem skewInclusion_injective (n : ℕ) : Function.Injective (skewInclusion n) := by
  intro K L h
  exact Subtype.ext h

/-- Finite-dimensional linear algebra supplies a continuous projection onto the model. -/
def skewProjection (n : ℕ) :
    (Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)) →L[ℝ] SkewSpace n :=
  finiteSubmoduleProjection (skewSubmodule n)

theorem skewProjection_coe (K : SkewSpace n) : skewProjection n K.val = K :=
  finiteSubmoduleProjection_apply (skewSubmodule n) K

theorem contDiff_skewProjection : ContDiff ℝ ∞ (skewProjection n) :=
  contDiff_finiteSubmoduleProjection (skewSubmodule n)

theorem skewProjection_fraction (a : symplecticSubgroup n) (ha : a ∈ cayleyDomain n) :
    skewProjection n (fraction a.val.val.val) = symplecticCoordinate n a ha :=
  skewProjection_coe (symplecticCoordinate n a ha)

def transitionOperator (a b : symplecticSubgroup n) (K : SkewSpace n) : symplecticSubgroup n :=
  b⁻¹ * (a * symplecticCayley n K)

def transitionAmbient (a b : symplecticSubgroup n) (K : SkewSpace n) :
    Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4) :=
  (b⁻¹).val.val.val.comp (a.val.val.val.comp (operator (toOrthogonalSkew n K)))

theorem transitionOperator_operator (a b : symplecticSubgroup n) (K : SkewSpace n) :
    (transitionOperator a b K).val.val.val = transitionAmbient a b K := rfl

theorem contDiff_cayleyOperator :
    ContDiff ℝ ∞ (fun K : SkewSpace n => operator (toOrthogonalSkew n K)) := by
  have h : ContDiff ℝ ∞ (toOrthogonalSkew n) :=
    finiteLinearMap_contDiff (E := SkewSpace n) (F := SkewOperators (4 * n + 4))
      (toOrthogonalSkew n)
  exact (contDiff_operator (n := 4 * n + 4)).comp h

theorem contDiff_transitionAmbient (a b : symplecticSubgroup n) :
    ContDiff ℝ ∞ (transitionAmbient a b) :=
  contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_cayleyOperator)

theorem transition_mem_domain (a b : symplecticSubgroup n) (K : SkewSpace n)
    (hK : K ∈ ((atOperator a).symm.trans (atOperator b)).source) :
    transitionOperator a b K ∈ cayleyDomain n := by
  have h := hK.2
  change (atOperator a).symm K ∈ (atOperator b).source at h
  rw [atOperator_source] at h
  exact h

theorem transition_eq (a b : symplecticSubgroup n) (K : SkewSpace n)
    (hK : K ∈ ((atOperator a).symm.trans (atOperator b)).source) :
    ((atOperator a).symm.trans (atOperator b)) K =
      skewProjection n (fraction (transitionAmbient a b K)) := by
  have hmem := transition_mem_domain a b K hK
  change cayleyCoordinates n (transitionOperator a b K) = _
  rw [cayleyCoordinates_of_mem n _ hmem, ← transitionOperator_operator]
  exact (skewProjection_fraction (transitionOperator a b K) hmem).symm

theorem contDiffOn_transition (a b : symplecticSubgroup n) :
    ContDiffOn ℝ ∞ ((atOperator a).symm.trans (atOperator b))
      ((atOperator a).symm.trans (atOperator b)).source := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun K => skewProjection n (fraction (transitionAmbient a b K)))
      ((atOperator a).symm.trans (atOperator b)).source := by
    intro K hK
    have hden : (1 + transitionAmbient a b K).IsInvertible := by
      rw [← transitionOperator_operator]
      exact transition_mem_domain a b K hK
    have hfrac : ContDiffAt ℝ ∞ (fun K => fraction (transitionAmbient a b K)) K :=
      ContDiffAt.comp (f := transitionAmbient a b) (g := fraction) K
        (contDiffAt_fraction _ hden) (contDiff_transitionAmbient a b).contDiffAt
    exact (contDiff_skewProjection.contDiffAt.comp K hfrac).contDiffWithinAt
  exact hsmooth.congr (fun K hK => transition_eq a b K hK)

/-- The manifold structure is proved from transitions of the actual Cayley coordinates. -/
instance isManifold (n : ℕ) : IsManifold 𝓘(ℝ, SkewSpace n) ∞ (symplecticSubgroup n) :=
  isManifold_of_contDiffOn 𝓘(ℝ, SkewSpace n) ∞ (symplecticSubgroup n) (by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using
        contDiffOn_transition a b)

end CayleyAtlas

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns
