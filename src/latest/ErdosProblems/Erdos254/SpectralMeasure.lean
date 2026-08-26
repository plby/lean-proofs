/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
import ErdosProblems.Erdos254.Basic

namespace Erdos254

open MeasureTheory Set
open scoped InnerProductSpace ComplexConjugate Topology CompactlySupported

variable {X H : Type*} [TopologicalSpace X]
  [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- The scalar functional associated to a vector and an operator representation. -/
noncomputable def vectorFunctional
    (R : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) : C(X, ℂ) →ₗ[ℂ] ℂ where
  toFun f := inner ℂ v (R f v)
  map_add' f g := by simp
  map_smul' c f := by simp

lemma vectorFunctional_star (R : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (v : H) (f : C(X, ℂ)) :
    vectorFunctional R v (star f) = star (vectorFunctional R v f) := by
  simp only [vectorFunctional, LinearMap.coe_mk, AddHom.coe_mk, map_star,
    ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right]
  exact (inner_conj_symm _ _).symm

/-- Complexification of a real continuous function. -/
def complexify (f : C(X, ℝ)) : C(X, ℂ) :=
  ⟨fun x ↦ (f x : ℂ), Complex.continuous_ofReal.comp f.continuous⟩

@[simp] lemma complexify_apply (f : C(X, ℝ)) (x : X) :
    complexify f x = (f x : ℂ) := rfl

@[simp] lemma complexify_add (f g : C(X, ℝ)) :
    complexify (f + g) = complexify f + complexify g := by ext; simp

@[simp] lemma complexify_sub (f g : C(X, ℝ)) :
    complexify (f - g) = complexify f - complexify g := by ext; simp

@[simp] lemma complexify_smul (c : ℝ) (f : C(X, ℝ)) :
    complexify (c • f) = (c : ℂ) • complexify f := by ext; simp

@[simp] lemma star_complexify (f : C(X, ℝ)) : star (complexify f) = complexify f := by
  ext; simp

lemma vectorFunctional_nonneg (R : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H))
    (v : H) (f : C(X, ℝ)) (hf : 0 ≤ f) :
    0 ≤ (vectorFunctional R v (complexify f)).re := by
  let q : C(X, ℂ) := complexify ⟨fun x ↦ Real.sqrt (f x), by fun_prop⟩
  have hq : star q * q = complexify f := by
    ext x
    simpa [q, ← Complex.ofReal_mul] using Real.mul_self_sqrt (hf x)
  rw [← hq]
  simp only [vectorFunctional, LinearMap.coe_mk, AddHom.coe_mk, map_mul, map_star,
    mul_apply_eq_comp, ContinuousLinearMap.star_eq_adjoint,
    ContinuousLinearMap.adjoint_inner_right]
  simpa using (inner_self_nonneg (𝕜 := ℂ) (x := R q v))

section Riesz

variable [CompactSpace X] [T2Space X] [MeasurableSpace X] [BorelSpace X]

/-- Riesz representation for a complex linear functional which preserves conjugation
and is positive on real nonnegative continuous functions. -/
theorem exists_scalar_measure (Φ : C(X, ℂ) →ₗ[ℂ] ℂ)
    (hstar : ∀ f, Φ (star f) = star (Φ f))
    (hpos : ∀ f : C(X, ℝ), 0 ≤ f → 0 ≤ (Φ (complexify f)).re) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      ∀ f : C(X, ℂ), ∫ x, f x ∂μ = Φ f := by
  let Λ : C_c(X, ℝ) →ₚ[ℝ] ℝ :=
    { toFun f := (Φ (complexify f.toContinuousMap)).re
      map_add' f g := by
        change (Φ (complexify (f.toContinuousMap + g.toContinuousMap))).re = _
        simp
      map_smul' c f := by
        change (Φ (complexify (c • f.toContinuousMap))).re = _
        simp
      monotone' f g hfg := by
        have h := hpos (g.toContinuousMap - f.toContinuousMap) (sub_nonneg.mpr hfg)
        simpa using h }
  let μ := RealRMK.rieszMeasure Λ
  have : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have hr (f : C(X, ℝ)) : ∫ x, f x ∂μ = (Φ (complexify f)).re := by
    exact RealRMK.integral_rieszMeasure Λ ⟨f, HasCompactSupport.of_compactSpace _⟩
  have hi (f : C(X, ℝ)) : (Φ (complexify f)).im = 0 := by
    have h := congrArg Complex.im (hstar (complexify f))
    simp only [star_complexify] at h
    change (Φ (complexify f)).im = -(Φ (complexify f)).im at h
    linarith
  refine ⟨μ, inferInstance, fun f ↦ ?_⟩
  let fr : C(X, ℝ) := ⟨fun x ↦ (f x).re, by fun_prop⟩
  let fi : C(X, ℝ) := ⟨fun x ↦ (f x).im, by fun_prop⟩
  have hf : f = complexify fr + Complex.I • complexify fi := by
    ext x
    simp only [ContinuousMap.add_apply, complexify_apply, ContinuousMap.smul_apply,
      smul_eq_mul, fr, fi, ContinuousMap.coe_mk]
    exact (Complex.re_add_im (f x)).symm.trans (by ring)
  have hint : Integrable f μ := f.continuous.integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)
  apply Complex.ext
  · have h : (∫ x, f x ∂μ).re = ∫ x, fr x ∂μ := by
      simpa [fr] using (integral_re hint).symm
    rw [h, hr fr, hf, map_add, map_smul]
    simp [hi]
  · have h : (∫ x, f x ∂μ).im = ∫ x, fi x ∂μ := by
      simpa [fi] using (integral_im hint).symm
    rw [h, hr fi, hf, map_add, map_smul]
    simp [hi]

theorem exists_vector_measure
    (R : C(X, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H)) (v : H) :
    ∃ μ : Measure X, IsFiniteMeasure μ ∧
      ∀ f : C(X, ℂ), ∫ x, f x ∂μ = inner ℂ v (R f v) :=
  exists_scalar_measure (vectorFunctional R v) (vectorFunctional_star R v)
    (vectorFunctional_nonneg R v)

end Riesz

/-- The coordinate function on the complex unit circle. -/
def circleCoordinate : C(Circle, ℂ) := ⟨Subtype.val, continuous_subtype_val⟩

noncomputable instance circleMeasurableSpace : MeasurableSpace Circle := borel Circle

instance circleBorelSpace : BorelSpace Circle := ⟨rfl⟩

@[simp] lemma circleCoordinate_apply (z : Circle) : circleCoordinate z = (z : ℂ) := rfl

/-- Functional calculus for a unitary, with functions on the entire unit circle. -/
noncomputable def circleRepresentation (U : unitary (H →L[ℂ] H)) :
    C(Circle, ℂ) →⋆ₐ[ℂ] (H →L[ℂ] H) :=
  cfcHomSuperset (show IsStarNormal (U : H →L[ℂ] H) from inferInstance)
    (Unitary.spectrum_subset_circle (𝕜 := ℂ) U)

@[simp] lemma circleRepresentation_coordinate (U : unitary (H →L[ℂ] H)) :
    circleRepresentation U circleCoordinate = (U : H →L[ℂ] H) :=
  cfcHomSuperset_id _ _

/-- Scalar spectral measure of a unitary operator, constructed by functional calculus
and Riesz representation. The square formula will be used for its atom at `1`. -/
theorem exists_unitary_spectral_measure (U : unitary (H →L[ℂ] H)) (v : H) :
    ∃ μ : Measure Circle, IsFiniteMeasure μ ∧
      (∀ n : ℕ, ∫ z, (z : ℂ) ^ n ∂μ = inner ℂ v (((U : H →L[ℂ] H) ^ n) v)) ∧
      (∀ f : C(Circle, ℂ), ∫ z, ‖f z‖ ^ 2 ∂μ = ‖circleRepresentation U f v‖ ^ 2) := by
  obtain ⟨μ, hfin, hμ⟩ := exists_vector_measure (circleRepresentation U) v
  have : IsFiniteMeasure μ := hfin
  refine ⟨μ, hfin, fun n ↦ ?_, fun f ↦ ?_⟩
  · simpa using hμ (circleCoordinate ^ n)
  · have h := congrArg Complex.re (hμ (star f * f))
    have hint : Integrable (star f * f) μ :=
      (star f * f).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hre : (∫ z, (star f * f) z ∂μ).re = ∫ z, ‖f z‖ ^ 2 ∂μ := by
      rw [← show (∫ z, RCLike.re ((star f * f) z) ∂μ) =
          (∫ z, (star f * f) z ∂μ).re from integral_re hint]
      congr 1
      funext z
      simpa [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq (f z)
    rw [hre] at h
    simp only [map_mul, map_star, mul_apply_eq_comp,
      ContinuousLinearMap.star_eq_adjoint, ContinuousLinearMap.adjoint_inner_right] at h
    exact h.trans (inner_self_eq_norm_sq (𝕜 := ℂ) _)

end Erdos254
