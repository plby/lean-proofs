import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicAntipodalIndex
import Wikipedia.HomotopyGroupsOfSpheres.QuaternionicIndexTestField
import Wikipedia.NoExoticSixSphere.OrthogonalIndexEstimate

/-!
# Actual negative energy variations within the symplectic group

The independent quaternionic test fields are realized by `γ(t) exp(s W(t))`
in the original symplectic subgroup. They fix both endpoints, are smooth in
both parameters, and have strictly negative second energy derivative in
every nonzero parameter direction. No global Morse deformation is assumed.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.NegativeVariation

open NoExoticSixSphere.GLOrthonormalization NoExoticSixSphere.HilbertSchmidt
open NoExoticSixSphere.OrthogonalCommutator NoExoticSixSphere.OrthogonalPathEnergy
open NoExoticSixSphere.SkewSpectralPlane IndexTestField

variable {n : ℕ}

def family (γ : ℝ → symplecticSubgroup n) (W : ℝ → SkewSpace n)
    (p : ℝ × ℝ) : symplecticSubgroup n := γ p.2 * Exponential.exp (p.1 • W p.2)

theorem family_orthogonal (γ : ℝ → symplecticSubgroup n) (W : ℝ → SkewSpace n) (p : ℝ × ℝ) :
    (family γ W p).val = NoExoticSixSphere.OrthogonalExponentialVariation.family
      (fun t => (γ t).val) (fun t => toOrthogonalSkew n (W t)) p := by
  change (γ p.2).val * NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (p.1 • W p.2)) =
      (γ p.2).val * NoExoticSixSphere.OrthogonalExponential.exp
        (p.1 • toOrthogonalSkew n (W p.2))
  rw [map_smul]

theorem family_zero (γ : ℝ → symplecticSubgroup n) (W : ℝ → SkewSpace n) (t : ℝ) :
    family γ W (0, t) = γ t := by
  simp only [family, zero_smul, Exponential.exp_zero, mul_one]

theorem family_of_field_zero (γ : ℝ → symplecticSubgroup n) (W : ℝ → SkewSpace n)
    {t : ℝ} (ht : W t = 0) (s : ℝ) : family γ W (s, t) = γ t := by
  simp only [family, ht, smul_zero, Exponential.exp_zero, mul_one]

theorem contDiff_family_operator {γ : ℝ → symplecticSubgroup n} {W : ℝ → SkewSpace n}
    (hγ : ContDiff ℝ ∞ (fun t => (γ t).val.val.val)) (hW : ContDiff ℝ ∞ W) :
    ContDiff ℝ ∞ (fun p => (family γ W p).val.val.val) := by
  have hL : ContDiff ℝ ∞ (toOrthogonalSkew n) :=
    finiteLinearMap_contDiff (E := SkewSpace n)
      (F := NoExoticSixSphere.CayleyTransform.SkewOperators (4 * n + 4)) (toOrthogonalSkew n)
  have hWO : ContDiff ℝ ∞ (fun t => toOrthogonalSkew n (W t)) := hL.comp hW
  have h := NoExoticSixSphere.OrthogonalExponentialVariation.contDiff_family_operator
    (γ := fun t => (γ t).val) hγ hWO
  simpa only [NoExoticSixSphere.OrthogonalMaurerCartan.operator, family_orthogonal] using h

theorem family_test_orthogonal (b : symplecticSubgroup n) (K A : SkewSpace n) (p : ℝ × ℝ) :
    (family (fun t => b * Exponential.exp (t • K)) (field K A) p).val =
      NoExoticSixSphere.OrthogonalExponentialVariation.family
        (fun t => b.val * NoExoticSixSphere.OrthogonalExponential.exp (t • toOrthogonalSkew n K))
        (NoExoticSixSphere.OrthogonalIndexTestField.field
          (toOrthogonalSkew n K) (toOrthogonalSkew n A)) p := by
  change (b.val * NoExoticSixSphere.OrthogonalExponential.exp
    (toOrthogonalSkew n (p.2 • K))) * NoExoticSixSphere.OrthogonalExponential.exp
      (toOrthogonalSkew n (p.1 • field K A p.2)) = _
  rw [map_smul, map_smul, toOrthogonal_field]
  rfl

theorem negative_secondDerivative (b : symplecticSubgroup n) (K A : SkewSpace n)
    (h : 4 * Real.pi ^ 2 * squareNorm A.val < squareNorm (commutator K.val A.val)) :
    deriv (deriv (fun s => energy
      (fun t => (family (fun r => b * Exponential.exp (r • K)) (field K A) (s, t)).val.val.val)
        0 1)) 0 < 0 := by
  have he := NoExoticSixSphere.OrthogonalIndexTestField.negative_secondDerivative
    b.val (toOrthogonalSkew n K) (toOrthogonalSkew n A) h
  simpa only [family_test_orthogonal] using he

/-- The pointwise index bound is realized by independent, smooth, endpoint-zero
fields and actual symplectic exponential variations. -/
theorem exists_negative_fieldFamily (b : symplecticSubgroup n) (K : SkewSpace n)
    (hexp : (Exponential.exp K).val.val.val =
      -(1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4)))
    (hnot : gram (toOrthogonalSkew n K) ≠
      Real.pi ^ 2 • (1 : Vector (4 * n + 4) →L[ℝ] Vector (4 * n + 4))) :
    ∃ F : (Fin n → ℝ) →ₗ[ℝ] (ℝ → SkewSpace n), Function.Injective F ∧ ∀ c,
      ContDiff ℝ ∞ (F c) ∧ F c 0 = 0 ∧ F c 1 = 0 ∧
      (c ≠ 0 → deriv (deriv (fun s => energy
        (fun t => (family (fun r => b * Exponential.exp (r • K)) (F c) (s, t)).val.val.val)
          0 1)) 0 < 0) := by
  obtain ⟨T, hT, hneg⟩ := exists_negativeFamily K hexp hnot
  let F := (fieldLinear K).comp T
  refine ⟨F, (fieldLinear_injective K).comp hT, fun c => ?_⟩
  exact ⟨contDiff_field K (T c), field_zero K (T c), field_one K (T c),
    fun hc => negative_secondDerivative b K (T c) (hneg c hc)⟩

end Wikipedia.HomotopyGroupsOfSpheres.QuaternionicColumns.NegativeVariation
