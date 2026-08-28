import Wikipedia.HopfProblem.CuspHoneycombHexagonSquares
import Wikipedia.HopfProblem.CuspPositiveRetractionTwist

/-!
# Opposite boundary gluing on the actual positive hexagon

The established twisted translation identifying the two opposite complex
boundary curves preserves the actual positive part for the purely
imaginary correction. Restricting it gives a homeomorphism of the literal
positive sides. Its endpoint formulas reverse the two toric origins.
-/

open Set Topology

namespace Wikipedia.HopfProblem.CuspHoneycombHexagon

open ToricCharts ToricFan ToricSpace ToricComponent CuspQuotient CuspPositive

/-- The actual opposite-side gluing restricted to the positive locus. -/
noncomputable def oppositePositiveBoundaryMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    positiveBoundary (k + 3) :=
  ⟨⟨⟨twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k)) (x.1.1 : Space), by
      rw [twistedTranslate_mem_rayDivisor, cuspVector_cuspVector]
      simp only [zero_sub, neg_neg]
      exact x.2⟩,
    twistedTranslate_positiveTwist_preserves_positivePart C₀
      (cuspVector (hexagonRay k)) x.1.2⟩, by
    change twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k))
      (x.1.1 : Space) ∈ rayDivisor (hexagonRay (k + 3))
    rw [hexagonRay_opposite, twistedTranslate_mem_rayDivisor,
      cuspVector_cuspVector, sub_self]
    exact x.1.1.2⟩

private noncomputable def oppositePositiveBoundaryInv
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (y : positiveBoundary (k + 3)) :
    positiveBoundary k :=
  ⟨⟨⟨twistedTranslate (positiveTwist C₀) (-cuspVector (hexagonRay k)) (y.1.1 : Space), by
      rw [twistedTranslate_mem_rayDivisor, cuspVector_neg, cuspVector_cuspVector,
        neg_neg, zero_sub, ← hexagonRay_opposite]
      exact y.2⟩,
    twistedTranslate_positiveTwist_preserves_positivePart C₀
      (-cuspVector (hexagonRay k)) y.1.2⟩, by
    change twistedTranslate (positiveTwist C₀) (-cuspVector (hexagonRay k))
      (y.1.1 : Space) ∈ rayDivisor (hexagonRay k)
    rw [twistedTranslate_mem_rayDivisor, cuspVector_neg, cuspVector_cuspVector,
      neg_neg, sub_self]
    exact y.1.1.2⟩

/-- The opposite boundaries of the actual positive zero component are
homeomorphic by the genuine positive-twist lattice action. -/
noncomputable def oppositePositiveBoundaryHomeomorph
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    positiveBoundary k ≃ₜ positiveBoundary (k + 3) where
  toFun := oppositePositiveBoundaryMap C₀ k
  invFun := oppositePositiveBoundaryInv C₀ k
  left_inv x := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change twistedTranslate (positiveTwist C₀) (-cuspVector (hexagonRay k))
      (twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k)) (x.1.1 : Space)) =
        (x.1.1 : Space)
    rw [twistedTranslate_add, neg_add_cancel, twistedTranslate_zero]
  right_inv y := by
    apply Subtype.ext
    apply Subtype.ext
    apply Subtype.ext
    change twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k))
      (twistedTranslate (positiveTwist C₀) (-cuspVector (hexagonRay k)) (y.1.1 : Space)) =
        (y.1.1 : Space)
    rw [twistedTranslate_add, add_neg_cancel, twistedTranslate_zero]
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (centralTranslationHomeomorph (positiveTwist C₀)
      (cuspVector (hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))
  continuous_invFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (centralTranslationHomeomorph (positiveTwist C₀)
      (-cuspVector (hexagonRay k))).continuous.comp
        (continuous_subtype_val.comp (continuous_subtype_val.comp continuous_subtype_val))

theorem oppositePositiveBoundaryHomeomorph_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : Space) =
      twistedTranslate (positiveTwist C₀) (cuspVector (hexagonRay k)) (x.1.1 : Space) := rfl

theorem oppositePositiveBoundaryHomeomorph_symm_coe
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (y : positiveBoundary (k + 3)) :
    (((oppositePositiveBoundaryHomeomorph C₀ k).symm y).1.1 : Space) =
      twistedTranslate (positiveTwist C₀) (-cuspVector (hexagonRay k)) (y.1.1 : Space) := rfl

/-- This is exactly the previously established complex boundary map,
with its domain and codomain restricted to the positive loci. -/
theorem oppositePositiveBoundaryHomeomorph_eq_oppositeBoundaryMap
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : Space) =
      ((oppositeBoundaryMap (positiveTwist C₀) (hexagonRay k) ⟨x.1.1, x.2⟩).1 : Space) := rfl

/-- Opposite positive-side points have the same image in the actual cusp
quotient. -/
theorem componentProjection_oppositePositiveBoundaryHomeomorph
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (ε : ℝ) (hε : 0 < ε)
    (k : Fin 6) (x : positiveBoundary k) :
    componentProjection (positiveTwist C₀) ε hε
      (oppositePositiveBoundaryHomeomorph C₀ k x).1.1 =
        componentProjection (positiveTwist C₀) ε hε x.1.1 :=
  componentProjection_oppositeBoundaryMap (positiveTwist C₀) ε hε
    (hexagonRay k) ⟨x.1.1, x.2⟩

theorem zeroTriangle_shift_opposite_previous (k : Fin 6) :
    (zeroTriangle (k - 1)).shift (-hexagonRay k) = zeroTriangle (k + 3) := by
  fin_cases k <;> decide

theorem zeroTriangle_shift_opposite_current (k : Fin 6) :
    (zeroTriangle k).shift (-hexagonRay k) = zeroTriangle (k + 2) := by
  fin_cases k <;> decide

/-- The first endpoint maps to the second endpoint of the opposite side.
The torus multiplier fixes an affine origin for every correction. -/
theorem opposite_twistedTranslate_origin_previous
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    twistedTranslate C (cuspVector (hexagonRay k)) (inclusion (zeroTriangle (k - 1)) 0) =
      inclusion (zeroTriangle (k + 3)) 0 := by
  rw [twistedTranslate_origin, cuspVector_cuspVector, zeroTriangle_shift_opposite_previous]

/-- The second endpoint maps to the first endpoint of the opposite side. -/
theorem opposite_twistedTranslate_origin_current
    (C : ℂ → Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) :
    twistedTranslate C (cuspVector (hexagonRay k)) (inclusion (zeroTriangle k) 0) =
      inclusion (zeroTriangle (k + 2)) 0 := by
  rw [twistedTranslate_origin, cuspVector_cuspVector, zeroTriangle_shift_opposite_current]

theorem oppositePositiveBoundaryHomeomorph_origin_previous
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k)
    (hx : (x.1.1 : Space) = inclusion (zeroTriangle (k - 1)) 0) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : Space) =
      inclusion (zeroTriangle (k + 3)) 0 := by
  rw [oppositePositiveBoundaryHomeomorph_coe, hx, opposite_twistedTranslate_origin_previous]

theorem oppositePositiveBoundaryHomeomorph_origin_current
    (C₀ : Matrix (Fin 2) (Fin 2) ℂ) (k : Fin 6) (x : positiveBoundary k)
    (hx : (x.1.1 : Space) = inclusion (zeroTriangle k) 0) :
    ((oppositePositiveBoundaryHomeomorph C₀ k x).1.1 : Space) =
      inclusion (zeroTriangle (k + 2)) 0 := by
  rw [oppositePositiveBoundaryHomeomorph_coe, hx, opposite_twistedTranslate_origin_current]

end Wikipedia.HopfProblem.CuspHoneycombHexagon
