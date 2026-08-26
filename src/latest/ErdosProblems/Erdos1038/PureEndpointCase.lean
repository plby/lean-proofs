import ErdosProblems.Erdos1038.EndpointNormalization

/-!
# The pure endpoint case

If endpoint normalization leaves no residual roots, every root occurrence is
the endpoint root `-1`.  Monicity then identifies the normalized polynomial
with a positive power of `X + 1`.  Its strict unit sublevel set is exactly
`(-2, 0)`, so translation invariance gives sublevel volume `2` for the
original polynomial.
-/

open scoped ENNReal Real
open MeasureTheory Set Polynomial

namespace Erdos1038

noncomputable section

/-- Every positive power of `X + 1` has the same strict unit sublevel set. -/
theorem sublevelSet_X_add_one_pow {n : ℕ} (hn : 0 < n) :
    sublevelSet ((X + 1 : Polynomial ℝ) ^ n) = Ioo (-2 : ℝ) 0 := by
  ext x
  change |((X + 1 : Polynomial ℝ) ^ n).eval x| < 1 ↔
    -2 < x ∧ x < 0
  simp only [eval_pow, eval_add, eval_X, eval_one, abs_pow]
  rw [pow_lt_one_iff_of_nonneg (abs_nonneg _) (Nat.ne_of_gt hn), abs_lt]
  constructor <;> rintro ⟨hlo, hhi⟩ <;> constructor <;> linarith

theorem sublevelVolume_X_add_one_pow {n : ℕ} (hn : 0 < n) :
    sublevelVolume ((X + 1 : Polynomial ℝ) ^ n) = ENNReal.ofReal 2 := by
  rw [sublevelVolume, sublevelSet_X_add_one_pow hn, Real.volume_Ioo]
  norm_num

namespace EndpointNormalizationHypotheses

variable {f : Polynomial ℝ} (h : EndpointNormalizationHypotheses f)

/-- With no residual roots, endpoint multiplicity is the full degree. -/
lemma endpointMultiplicity_eq_natDegree_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    endpointMultiplicity h.normalizedPolynomial =
      h.normalizedPolynomial.natDegree := by
  have htotal := h.endpointMultiplicity_add_residual_card
  rw [hres, Multiset.card_zero, add_zero] at htotal
  exact htotal

/-- Root multiset in the pure endpoint case. -/
lemma normalized_roots_eq_replicate_endpoint_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    h.normalizedPolynomial.roots =
      Multiset.replicate (endpointMultiplicity h.normalizedPolynomial)
        (-1 : ℝ) := by
  have hsplit := replicate_endpoint_add_residual h.normalizedPolynomial
  rw [hres, add_zero] at hsplit
  exact hsplit.symm

/-- A monic endpoint-normalized polynomial without residual roots is a pure
power of its endpoint factor. -/
theorem normalizedPolynomial_eq_endpointPower_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    h.normalizedPolynomial =
      (X + 1 : Polynomial ℝ) ^
        endpointMultiplicity h.normalizedPolynomial := by
  have hroots :=
    h.normalized_roots_eq_replicate_endpoint_of_residual_eq_zero hres
  calc
    h.normalizedPolynomial =
        (h.normalizedPolynomial.roots.map fun r ↦ X - C r).prod :=
      h.normalized_admissible.splits.eq_prod_roots_of_monic
        h.normalized_admissible.monic
    _ = (X + 1 : Polynomial ℝ) ^
        endpointMultiplicity h.normalizedPolynomial := by
      rw [hroots]
      simp

theorem normalizedPolynomial_eq_natDegreePower_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    h.normalizedPolynomial =
      (X + 1 : Polynomial ℝ) ^ h.normalizedPolynomial.natDegree := by
  calc
    h.normalizedPolynomial =
        (X + 1 : Polynomial ℝ) ^
          endpointMultiplicity h.normalizedPolynomial :=
      h.normalizedPolynomial_eq_endpointPower_of_residual_eq_zero hres
    _ = (X + 1 : Polynomial ℝ) ^ h.normalizedPolynomial.natDegree := by
      rw [h.endpointMultiplicity_eq_natDegree_of_residual_eq_zero hres]

theorem exists_pos_normalizedPolynomial_eq_endpointPower_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    ∃ n : ℕ, 0 < n ∧
      h.normalizedPolynomial = (X + 1 : Polynomial ℝ) ^ n :=
  ⟨endpointMultiplicity h.normalizedPolynomial,
    h.endpointMultiplicity_pos,
    h.normalizedPolynomial_eq_endpointPower_of_residual_eq_zero hres⟩

theorem normalized_sublevelSet_eq_Ioo_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    sublevelSet h.normalizedPolynomial = Ioo (-2 : ℝ) 0 := by
  calc
    sublevelSet h.normalizedPolynomial =
        sublevelSet ((X + 1 : Polynomial ℝ) ^
          endpointMultiplicity h.normalizedPolynomial) :=
      congrArg sublevelSet
        (h.normalizedPolynomial_eq_endpointPower_of_residual_eq_zero hres)
    _ = Ioo (-2 : ℝ) 0 :=
      sublevelSet_X_add_one_pow h.endpointMultiplicity_pos

theorem normalized_sublevelVolume_eq_two_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    sublevelVolume h.normalizedPolynomial = ENNReal.ofReal 2 := by
  calc
    sublevelVolume h.normalizedPolynomial =
        sublevelVolume ((X + 1 : Polynomial ℝ) ^
          endpointMultiplicity h.normalizedPolynomial) :=
      congrArg sublevelVolume
        (h.normalizedPolynomial_eq_endpointPower_of_residual_eq_zero hres)
    _ = ENNReal.ofReal 2 :=
      sublevelVolume_X_add_one_pow h.endpointMultiplicity_pos

/-- Translation back from endpoint normalization preserves the value `2`. -/
theorem sublevelVolume_eq_two_of_residual_eq_zero
    (hres : endpointResidualRoots h.normalizedPolynomial = 0) :
    sublevelVolume f = ENNReal.ofReal 2 := by
  calc
    sublevelVolume f = sublevelVolume h.normalizedPolynomial :=
      h.normalized_sublevelVolume.symm
    _ = ENNReal.ofReal 2 :=
      h.normalized_sublevelVolume_eq_two_of_residual_eq_zero hres

end EndpointNormalizationHypotheses

end

end Erdos1038
