import Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomologyRelativeFourierContinuity
import Wikipedia.HopfProblem.PeriodTorusLineBundleClassificationFourierDbarInverseAlgebra

/-!
# A fixed-centre holomorphic denominator on one common neighborhood

For each frequency, select a coordinate of maximal norm at one fixed centre.
The selection does not vary with the base. Operator-norm continuity then
retains half the elliptic lower bound on a single open neighborhood,
simultaneously for every real frequency.
-/

noncomputable section

open scoped ContDiff

namespace Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier

open Set Topology Filter MarkedLinear PeriodTorusLineBundleClassification

/-- The choice depends on the centre and frequency, never on the varying base. -/
def centreCoordinate (p₀ : PeriodDomain) (v : Fin 4 → ℝ) : Fin 2 :=
  symbolMaxCoordinate (relativeSymbol p₀ v)

/-- The selected coefficient in the original relative symbol. -/
def centreCoefficient (p₀ p : PeriodDomain) (v : Fin 4 → ℝ) : ℂ :=
  relativeSymbol p v (centreCoordinate p₀ v)

theorem norm_centreCoefficient_self (p₀ : PeriodDomain) (v : Fin 4 → ℝ) :
    ‖centreCoefficient p₀ p₀ v‖ = ‖relativeSymbol p₀ v‖ :=
  norm_symbolMaxCoordinate _

@[simp] theorem centreCoefficient_zero (p₀ p : PeriodDomain) :
    centreCoefficient p₀ p 0 = 0 := by
  simp only [centreCoefficient, map_zero, Pi.zero_apply]

/-- Closeness in operator norm preserves the fixed selected coordinate bound. -/
theorem centreCoefficient_lowerBound_of_norm_sub_le (p₀ p : PeriodDomain) (c : ℝ)
    (h₀ : ∀ v, c * ‖v‖ ≤ ‖relativeSymbol p₀ v‖)
    (hnear : ‖symbolOperator p - symbolOperator p₀‖ ≤ c / 2) (v : Fin 4 → ℝ) :
    (c / 2) * ‖v‖ ≤ ‖centreCoefficient p₀ p v‖ := by
  have hdiff : ‖(symbolOperator p - symbolOperator p₀) v‖ ≤ (c / 2) * ‖v‖ :=
    ((symbolOperator p - symbolOperator p₀).le_opNorm v).trans
      (mul_le_mul_of_nonneg_right hnear (norm_nonneg v))
  have hcomponent := (norm_le_pi_norm
    ((symbolOperator p - symbolOperator p₀) v) (centreCoordinate p₀ v)).trans hdiff
  change ‖centreCoefficient p₀ p v - centreCoefficient p₀ p₀ v‖ ≤
    (c / 2) * ‖v‖ at hcomponent
  have htri : ‖relativeSymbol p₀ v‖ ≤ ‖centreCoefficient p₀ p v‖ +
      ‖centreCoefficient p₀ p v - centreCoefficient p₀ p₀ v‖ := by
    rw [← norm_centreCoefficient_self]
    simpa only [sub_sub_cancel] using norm_sub_le (centreCoefficient p₀ p v)
      (centreCoefficient p₀ p v - centreCoefficient p₀ p₀ v)
  nlinarith [h₀ v]

variable {V B : Type*} [NormedAddCommGroup V] [NormedSpace ℂ V]
  [TopologicalSpace B] [ChartedSpace V B] (P : HolomorphicPeriodMap V B)

/-- The fixed-centre denominator is holomorphic, including its zero mode. -/
theorem holomorphic_centreCoefficient (p₀ : PeriodDomain) (v : Fin 4 → ℝ) :
    ContMDiff (modelWithCornersSelf ℂ V) (modelWithCornersSelf ℂ ℂ) ω
      (fun b => centreCoefficient p₀ (P.point b) v) :=
  holomorphic_symbol_coordinate P v (centreCoordinate p₀ v)

/-- One open neighborhood and one positive constant work for all frequencies
and the coordinate chosen once at the centre. -/
theorem exists_open_uniform_centreCoefficient_lowerBound (b₀ : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b₀ ∈ U ∧ 0 < c ∧
      ∀ b ∈ U, ∀ v : Fin 4 → ℝ,
        c * ‖v‖ ≤ ‖centreCoefficient (P.point b₀) (P.point b) v‖ := by
  obtain ⟨c, hc, hbound⟩ := relativeSymbol_exists_pos_lowerBound (P.point b₀)
  let U : Set B :=
    {b | ‖symbolOperator (P.point b) - symbolOperator (P.point b₀)‖ < c / 2}
  have hU : IsOpen U := isOpen_lt
    (((continuous_symbolOperator P).sub continuous_const).norm) continuous_const
  have hb₀ : b₀ ∈ U := by
    simpa only [U, mem_ofPred_eq, sub_self, norm_zero] using half_pos hc
  refine ⟨U, c / 2, hU, hb₀, half_pos hc, ?_⟩
  intro b hb v
  exact centreCoefficient_lowerBound_of_norm_sub_le (P.point b₀) (P.point b) c
    hbound (le_of_lt hb) v

/-- The same common neighborhood controls the genuine integer-frequency norm. -/
theorem exists_open_uniform_integerCentreCoefficient_lowerBound (b₀ : B) :
    ∃ (U : Set B) (c : ℝ), IsOpen U ∧ b₀ ∈ U ∧ 0 < c ∧
      ∀ b ∈ U, ∀ k : Fin 4 → ℤ,
        c * ‖k‖ ≤ ‖centreCoefficient (P.point b₀) (P.point b) (integerFrequency k)‖ := by
  obtain ⟨U, c, hU, hb₀, hc, hbound⟩ :=
    exists_open_uniform_centreCoefficient_lowerBound P b₀
  refine ⟨U, c, hU, hb₀, hc, fun b hb k => ?_⟩
  simpa only [integerFrequency_norm] using hbound b hb (integerFrequency k)

end Wikipedia.HopfProblem.PeriodFamilyHolomorphicCohomology.RelativeFourier
