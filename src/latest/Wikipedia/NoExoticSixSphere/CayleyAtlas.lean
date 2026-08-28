import Wikipedia.NoExoticSixSphere.CayleyChart

/-!
# Smooth Cayley atlas on the actual orthogonal operator space

Translate the identity Cayley chart by orthogonal multiplication. Transition
maps are the skew-adjoint projection of explicit smooth ambient rational maps,
on precisely the overlap where their denominators are invertible.
-/

open scoped Manifold ContDiff
open Set

namespace NoExoticSixSphere

open GLOrthonormalization OrthogonalPaths

namespace CayleyAtlas

open CayleyTransform

variable {n : ℕ}

/-- Left multiplication is a homeomorphism for the original operator-norm topology. -/
noncomputable def leftTranslate (a : OrthogonalOperators n) :
    OrthogonalOperators n ≃ₜ OrthogonalOperators n where
  toFun := mul a
  invFun := mul (inverse a)
  left_inv b := by rw [← OrthogonalPaths.mul_assoc, inverse_mul, identity_mul]
  right_inv b := by rw [← OrthogonalPaths.mul_assoc, mul_inverse, identity_mul]
  continuous_toFun := continuous_mul (fun _ ↦ a) id continuous_const continuous_id
  continuous_invFun := continuous_mul (fun _ ↦ inverse a) id continuous_const continuous_id

/-- Translate the identity chart to an arbitrary orthogonal operator. -/
noncomputable def atOperator (a : OrthogonalOperators n) :
    OpenPartialHomeomorph (OrthogonalOperators n) (SkewOperators n) :=
  (leftTranslate a).symm.toOpenPartialHomeomorph.trans CayleyTransform.chart

theorem atOperator_apply (a b : OrthogonalOperators n) :
    atOperator a b = coordinates (mul (inverse a) b) := rfl

theorem atOperator_symm_apply (a : OrthogonalOperators n) (K : SkewOperators n) :
    (atOperator a).symm K = mul a (orthogonal K) := rfl

theorem atOperator_source (a : OrthogonalOperators n) :
    (atOperator a).source = {b | mul (inverse a) b ∈ domain} := by
  ext b
  change (b ∈ univ ∧ mul (inverse a) b ∈ domain) ↔ _
  simp only [mem_univ, true_and, mem_ofPred_eq]

theorem mem_atOperator_source (a : OrthogonalOperators n) : a ∈ (atOperator a).source := by
  rw [atOperator_source]
  change mul (inverse a) a ∈ domain
  rw [inverse_mul]
  exact identity_mem_domain

noncomputable instance chartedSpace (n : ℕ) :
    ChartedSpace (SkewOperators n) (OrthogonalOperators n) where
  atlas := range atOperator
  chartAt := atOperator
  mem_chart_source := mem_atOperator_source
  chart_mem_atlas a := ⟨a, rfl⟩

/-- A continuous linear projection onto the actual skew-adjoint model. -/
noncomputable def skewProjection :
    (Vector n →L[ℝ] Vector n) →L[ℝ] SkewOperators n :=
  LinearMap.toContinuousLinearMap (F' := SkewOperators n) (skewAdjointPart ℝ)

theorem skewProjection_coe (K : SkewOperators n) : skewProjection (n := n) K = K := by
  apply Subtype.ext
  change (⅟ (2 : ℝ)) • ((K : Vector n →L[ℝ] Vector n) - star (K : Vector n →L[ℝ] Vector n)) = K
  rw [K.2, sub_neg_eq_add, smul_add, invOf_two_smul_add_invOf_two_smul]

theorem skewProjection_fraction (a : OrthogonalOperators n) (ha : (1 + a.1.1).IsInvertible) :
    skewProjection (fraction a.1.1) = coordinate a ha := by
  have h := skewProjection_coe (coordinate a ha)
  rw [coordinate_operator] at h
  exact h

noncomputable def transitionOrthogonal (a b : OrthogonalOperators n) (K : SkewOperators n) :
    OrthogonalOperators n := mul (inverse b) (mul a (orthogonal K))

noncomputable def transitionAmbient (a b : OrthogonalOperators n) (K : SkewOperators n) :
    Vector n →L[ℝ] Vector n := (inverse b).1.1.comp (a.1.1.comp (operator K))

theorem transitionOrthogonal_operator (a b : OrthogonalOperators n) (K : SkewOperators n) :
    (transitionOrthogonal a b K).1.1 = transitionAmbient a b K := by
  apply ContinuousLinearMap.ext
  intro x
  rfl

theorem contDiff_transitionAmbient (a b : OrthogonalOperators n) :
    ContDiff ℝ ∞ (transitionAmbient a b) :=
  contDiff_const.clm_comp (contDiff_const.clm_comp contDiff_operator)

theorem transition_mem_domain (a b : OrthogonalOperators n) (K : SkewOperators n)
    (hK : K ∈ ((atOperator a).symm.trans (atOperator b)).source) :
    transitionOrthogonal a b K ∈ domain := by
  have h := hK.2
  change (atOperator a).symm K ∈ (atOperator b).source at h
  rw [atOperator_source] at h
  exact h

theorem transition_eq (a b : OrthogonalOperators n) (K : SkewOperators n)
    (hK : K ∈ ((atOperator a).symm.trans (atOperator b)).source) :
    ((atOperator a).symm.trans (atOperator b)) K =
      skewProjection (fraction (transitionAmbient a b K)) := by
  have hmem := transition_mem_domain a b K hK
  change coordinates (transitionOrthogonal a b K) = _
  rw [coordinates_of_mem _ hmem, ← transitionOrthogonal_operator]
  exact (skewProjection_fraction (transitionOrthogonal a b K) hmem).symm

theorem contDiffOn_transition (a b : OrthogonalOperators n) :
    ContDiffOn ℝ ∞ ((atOperator a).symm.trans (atOperator b))
      ((atOperator a).symm.trans (atOperator b)).source := by
  have hsmooth : ContDiffOn ℝ ∞
      (fun K ↦ skewProjection (fraction (transitionAmbient a b K)))
      ((atOperator a).symm.trans (atOperator b)).source := by
    intro K hK
    have hden : (1 + transitionAmbient a b K).IsInvertible := by
      rw [← transitionOrthogonal_operator]
      exact transition_mem_domain a b K hK
    have hfrac : ContDiffAt ℝ ∞ (fun K ↦ fraction (transitionAmbient a b K)) K :=
      ContDiffAt.comp (f := transitionAmbient a b) (g := fraction) K
        (contDiffAt_fraction _ hden) (contDiff_transitionAmbient a b).contDiffAt
    exact (skewProjection.contDiff.contDiffAt.comp K hfrac).contDiffWithinAt
  exact hsmooth.congr (fun K hK ↦ transition_eq a b K hK)

/-- The smooth structure is built from verified transitions of actual Cayley charts. -/
noncomputable instance isManifold (n : ℕ) :
    IsManifold 𝓘(ℝ, SkewOperators n) ∞ (OrthogonalOperators n) :=
  isManifold_of_contDiffOn 𝓘(ℝ, SkewOperators n) ∞ (OrthogonalOperators n) (by
    rintro _ _ ⟨a, rfl⟩ ⟨b, rfl⟩
    simpa only [modelWithCornersSelf_coe, modelWithCornersSelf_coe_symm,
      Function.comp_id, Function.id_comp, range_id, preimage_id, inter_univ] using
        contDiffOn_transition a b)

end CayleyAtlas

end NoExoticSixSphere
