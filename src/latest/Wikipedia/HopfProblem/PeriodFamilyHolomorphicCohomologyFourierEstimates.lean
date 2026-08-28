import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierModes
import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyFourierCompact

/-!
# Locally uniform inverse-multiplier estimates

The Hermitian formulas have order minus one in the original integer frequency.
The constants below are uniform over one open neighborhood, or over any given
compact base set.  The zero mode is handled by the actual zero values of the
formulas, not by discarding it from their domains.
-/

noncomputable section

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier

open Set
open PeriodTorusLineBundleClassification

theorem modePotential_norm_le (p : PeriodDomain) (k : Fin 4 → ℤ) (a : ComplexPlane₂) :
    ‖modePotential p k a‖ ≤ 2 * ‖a‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
  FourierHermitian.potential_norm_le_two _ a

theorem modeTopInverse_norm_le (p : PeriodDomain) (k : Fin 4 → ℤ) (h : ℂ) :
    ‖modeTopInverse p k h‖ ≤ ‖h‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
  FourierHermitian.topInverse_norm_le _ h

/-- The scalar Hermitian primitive has order minus one under a symbol lower bound. -/
theorem modePotential_norm_le_of_lowerBound (p : PeriodDomain) (k : Fin 4 → ℤ)
    (c : ℝ) (hc : 0 < c)
    (hbound : c * ‖k‖ ≤ ‖dolbeaultSymbol p (integerFrequency k)‖) (a : ComplexPlane₂) :
    ‖modePotential p k a‖ ≤ 2 * ‖a‖ / (c * ‖k‖) := by
  by_cases hk : k = 0
  · subst k
    simp
  · exact (modePotential_norm_le p k a).trans
      (div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (norm_nonneg a))
        (mul_pos hc (norm_pos_iff.mpr hk)) hbound)

/-- The top-degree Hermitian inverse has order minus one under the same lower bound. -/
theorem modeTopInverse_norm_le_of_lowerBound (p : PeriodDomain) (k : Fin 4 → ℤ)
    (c : ℝ) (hc : 0 < c)
    (hbound : c * ‖k‖ ≤ ‖dolbeaultSymbol p (integerFrequency k)‖) (h : ℂ) :
    ‖modeTopInverse p k h‖ ≤ ‖h‖ / (c * ‖k‖) := by
  by_cases hk : k = 0
  · subst k
    simp
  · exact (modeTopInverse_norm_le p k h).trans
      (div_le_div_of_nonneg_left (norm_nonneg h)
        (mul_pos hc (norm_pos_iff.mpr hk)) hbound)

/-- A positive nonzero-mode gap gives a uniform bound for the scalar multiplier,
including its totalized value at the zero frequency. -/
theorem modePotential_norm_le_of_gap (p : PeriodDomain) (k : Fin 4 → ℤ)
    (c : ℝ) (hc : 0 < c)
    (hgap : k ≠ 0 → c ≤ ‖dolbeaultSymbol p (integerFrequency k)‖) (a : ComplexPlane₂) :
    ‖modePotential p k a‖ ≤ (2 / c) * ‖a‖ := by
  by_cases hk : k = 0
  · subst k
    rw [modePotential_zero_frequency, norm_zero]
    exact mul_nonneg (div_nonneg (by norm_num) hc.le) (norm_nonneg a)
  · calc
      ‖modePotential p k a‖ ≤ 2 * ‖a‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
        modePotential_norm_le p k a
      _ ≤ 2 * ‖a‖ / c :=
        div_le_div_of_nonneg_left (mul_nonneg (by norm_num) (norm_nonneg a)) hc (hgap hk)
      _ = (2 / c) * ‖a‖ := by ring

/-- A positive nonzero-mode gap gives a uniform bound for the top multiplier,
including its totalized value at the zero frequency. -/
theorem modeTopInverse_norm_le_of_gap (p : PeriodDomain) (k : Fin 4 → ℤ)
    (c : ℝ) (hc : 0 < c)
    (hgap : k ≠ 0 → c ≤ ‖dolbeaultSymbol p (integerFrequency k)‖) (h : ℂ) :
    ‖modeTopInverse p k h‖ ≤ (1 / c) * ‖h‖ := by
  by_cases hk : k = 0
  · subst k
    rw [modeTopInverse_zero_frequency, norm_zero]
    exact mul_nonneg (one_div_nonneg.mpr hc.le) (norm_nonneg h)
  · calc
      ‖modeTopInverse p k h‖ ≤ ‖h‖ / ‖dolbeaultSymbol p (integerFrequency k)‖ :=
        modeTopInverse_norm_le p k h
      _ ≤ ‖h‖ / c := div_le_div_of_nonneg_left (norm_nonneg h) hc (hgap hk)
      _ = (1 / c) * ‖h‖ := by ring

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- Locally uniform order-minus-one estimates for both actual inverse multipliers. -/
theorem exists_open_uniform_order_one_bounds (b : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b ∈ U ∧ 0 < c ∧
      ∀ b' ∈ U, ∀ k : Fin 4 → ℤ,
        (∀ a : ComplexPlane₂, ‖modePotential (P.point b') k a‖ ≤ 2 * ‖a‖ / (c * ‖k‖)) ∧
        (∀ h : ℂ, ‖modeTopInverse (P.point b') k h‖ ≤ ‖h‖ / (c * ‖k‖)) := by
  obtain ⟨U, c, hU, hb, hc, hbound⟩ := exists_open_uniform_integer_lowerBound P b
  refine ⟨U, c, hU, hb, hc, fun b' hb' k => ?_⟩
  exact ⟨modePotential_norm_le_of_lowerBound _ k c hc (hbound b' hb' k),
    modeTopInverse_norm_le_of_lowerBound _ k c hc (hbound b' hb' k)⟩

/-- Locally uniform multiplier bounds, simultaneously for every original integer mode. -/
theorem exists_open_uniform_multiplier_bounds (b : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b ∈ U ∧ 0 < c ∧
      ∀ b' ∈ U, ∀ k : Fin 4 → ℤ,
        (∀ a : ComplexPlane₂, ‖modePotential (P.point b') k a‖ ≤ (2 / c) * ‖a‖) ∧
        (∀ h : ℂ, ‖modeTopInverse (P.point b') k h‖ ≤ (1 / c) * ‖h‖) := by
  obtain ⟨U, c, hU, hb, hc, hgap⟩ := exists_open_uniform_integer_gap P b
  refine ⟨U, c, hU, hb, hc, fun b' hb' k => ?_⟩
  exact ⟨modePotential_norm_le_of_gap _ k c hc (hgap b' hb' k),
    modeTopInverse_norm_le_of_gap _ k c hc (hgap b' hb' k)⟩

/-- The order-minus-one constants can be chosen uniformly on an arbitrary compact base set. -/
theorem exists_compact_uniform_order_one_bounds (K : Set B) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ k : Fin 4 → ℤ,
      (∀ a : ComplexPlane₂, ‖modePotential (P.point b) k a‖ ≤ 2 * ‖a‖ / (c * ‖k‖)) ∧
      (∀ h : ℂ, ‖modeTopInverse (P.point b) k h‖ ≤ ‖h‖ / (c * ‖k‖)) := by
  obtain ⟨c, hc, hbound⟩ := exists_compact_uniform_integer_lowerBound P K hK
  refine ⟨c, hc, fun b hb k => ?_⟩
  exact ⟨modePotential_norm_le_of_lowerBound _ k c hc (hbound b hb k),
    modeTopInverse_norm_le_of_lowerBound _ k c hc (hbound b hb k)⟩

/-- Both multipliers have uniform bounds over a compact part of the base. -/
theorem exists_compact_uniform_multiplier_bounds (K : Set B) (hK : IsCompact K) :
    ∃ c : ℝ, 0 < c ∧ ∀ b ∈ K, ∀ k : Fin 4 → ℤ,
      (∀ a : ComplexPlane₂, ‖modePotential (P.point b) k a‖ ≤ (2 / c) * ‖a‖) ∧
      (∀ h : ℂ, ‖modeTopInverse (P.point b) k h‖ ≤ (1 / c) * ‖h‖) := by
  obtain ⟨c, hc, hgap⟩ := exists_compact_uniform_integer_gap P K hK
  refine ⟨c, hc, fun b hb k => ?_⟩
  exact ⟨modePotential_norm_le_of_gap _ k c hc (hgap b hb k),
    modeTopInverse_norm_le_of_gap _ k c hc (hgap b hb k)⟩

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.Fourier
