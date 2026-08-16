import Wikipedia.GreenTao.Transference.RelativeCountingErrorSchedule

/-!
# Small parameters for relative counting

The explicit relative-counting recurrence is continuous at the origin, but
the final transference argument also needs an order-theoretic form of this
fact: replacing any of the three nonnegative input errors by a smaller one
cannot enlarge the scheduled error.

This file first proves that monotonicity and then records a diagonal
small-parameter selector.  These lemmas are the numerical core used when the
polynomial dense-model error and the two linear-forms errors are chosen in a
single parameter package.
-/

namespace Wikipedia.SzemeredisTheorem

open Filter Topology
open scoped Polynomial

/-- The finite relative-counting schedule is monotone in each nonnegative
input error. -/
theorem relativeCountingErrorSchedule_mono
    (m : ℕ)
    {cutError₁ cutError₂ η₁ η₂ ξ₁ ξ₂ : ℝ}
    (hcut₁ : 0 ≤ cutError₁)
    (hη₁ : 0 ≤ η₁)
    (hξ₁ : 0 ≤ ξ₁) (hξ₂ : 0 ≤ ξ₂)
    (hcut : cutError₁ ≤ cutError₂)
    (hη : η₁ ≤ η₂) (hξ : ξ₁ ≤ ξ₂) :
    ∀ s : ℕ,
      relativeCountingErrorSchedule
          m cutError₁ η₁ ξ₁ s ≤
        relativeCountingErrorSchedule
          m cutError₂ η₂ ξ₂ s := by
  intro s
  induction s with
  | zero =>
      simp only [relativeCountingErrorSchedule_zero]
      exact
        mul_le_mul_of_nonneg_left hcut
          (Nat.cast_nonneg _)
  | succ s ih =>
      rw [relativeCountingErrorSchedule_succ,
        relativeCountingErrorSchedule_succ]
      apply add_le_add hcut
      apply Real.sqrt_le_sqrt
      have hs₁ :
          0 ≤
            relativeCountingErrorSchedule
              m cutError₁ η₁ ξ₁ s :=
        relativeCountingErrorSchedule_nonneg
          m hcut₁ s
      have hs₂ :
          0 ≤
            relativeCountingErrorSchedule
              m cutError₂ η₂ ξ₂ s :=
        relativeCountingErrorSchedule_nonneg
          m (hcut₁.trans hcut) s
      have hsqrt :
          Real.sqrt (3 * η₁) ≤
            Real.sqrt (3 * η₂) := by
        apply Real.sqrt_le_sqrt
        linarith
      have hleft :
          0 ≤ 1 + ξ₁ := by
        linarith
      have hright :
          0 ≤
            3 * η₁ + 2 * Real.sqrt (3 * η₁) +
              2 *
                relativeCountingErrorSchedule
                  m cutError₁ η₁ ξ₁ s +
              4 * ξ₁ := by
        positivity
      have hfirst : 1 + ξ₁ ≤ 1 + ξ₂ := by
        linarith
      have hsecond :
          3 * η₁ + 2 * Real.sqrt (3 * η₁) +
                2 *
                  relativeCountingErrorSchedule
                    m cutError₁ η₁ ξ₁ s +
                4 * ξ₁ ≤
            3 * η₂ + 2 * Real.sqrt (3 * η₂) +
                2 *
                  relativeCountingErrorSchedule
                    m cutError₂ η₂ ξ₂ s +
                4 * ξ₂ := by
        linarith
      exact
        mul_le_mul hfirst hsecond hright
          (by linarith)

/-- Along the diagonal, every fixed finite relative-counting schedule tends
to zero. -/
theorem tendsto_relativeCountingErrorSchedule_diagonal_zero
    (m s : ℕ) :
    Tendsto
      (fun t : ℝ =>
        relativeCountingErrorSchedule m t t t s)
      (𝓝 0) (𝓝 0) := by
  have hcontinuous :
      Continuous
        (fun t : ℝ =>
          relativeCountingErrorSchedule m t t t s) := by
    have hdiagonal :
        Continuous (fun t : ℝ => (t, (t, t))) := by
      fun_prop
    change
      Continuous
        ((fun p : ℝ × (ℝ × ℝ) =>
            relativeCountingErrorSchedule
              m p.1 p.2.1 p.2.2 s) ∘
          fun t : ℝ => (t, (t, t)))
    exact
      (continuous_relativeCountingErrorSchedule m s).comp
        hdiagonal
  simpa using hcontinuous.tendsto 0

/-- Given two positive reserves, choose one positive scalar below the
density reserve for which the fixed finite counting schedule is already
below the count reserve. -/
theorem exists_relativeCountingErrorSchedule_diagonal_lt
    (m s : ℕ)
    {densityReserve countReserve : ℝ}
    (hdensity : 0 < densityReserve)
    (hcount : 0 < countReserve) :
    ∃ t : ℝ,
      0 < t ∧ t < densityReserve ∧ t < 1 ∧
        relativeCountingErrorSchedule m t t t s <
          countReserve := by
  have heventually :
      ∀ᶠ t : ℝ in 𝓝 0,
        relativeCountingErrorSchedule m t t t s <
          countReserve :=
    (tendsto_relativeCountingErrorSchedule_diagonal_zero
      m s).eventually_lt_const hcount
  obtain ⟨δ, hδ, hball⟩ :=
    Metric.eventually_nhds_iff_ball.mp heventually
  let t : ℝ := min δ (min densityReserve 1) / 2
  have hmin :
      0 < min δ (min densityReserve 1) := by
    exact lt_min hδ (lt_min hdensity zero_lt_one)
  have ht : 0 < t := by
    dsimp [t]
    linarith
  have htδ : t < δ := by
    dsimp [t]
    have hle :
        min δ (min densityReserve 1) ≤ δ :=
      min_le_left _ _
    linarith
  have htdensity : t < densityReserve := by
    dsimp [t]
    have hle :
        min δ (min densityReserve 1) ≤
          min densityReserve 1 :=
      min_le_right _ _
    have hle' : min densityReserve 1 ≤ densityReserve :=
      min_le_left _ _
    linarith
  have htone : t < 1 := by
    dsimp [t]
    have hle :
        min δ (min densityReserve 1) ≤
          min densityReserve 1 :=
      min_le_right _ _
    have hle' : min densityReserve 1 ≤ 1 :=
      min_le_right _ _
    linarith
  refine ⟨t, ht, htdensity, htone, ?_⟩
  apply hball
  simpa [Real.dist_eq, abs_of_pos ht] using htδ

/-! ## Polynomial dense-model parameters below one scalar budget -/

/-- For every positive target, choose a polynomial approximation and a
positive raw cut error whose resulting dense-model discrepancy is at most
that target. -/
theorem exists_polynomialDenseModelError_le
    {target : ℝ} (htarget : 0 < target) :
    ∃ (p : ℝ[X]) (cutError approximationError : ℝ),
      0 < cutError ∧ 0 < approximationError ∧
        ApproximatesPositivePartOnUnitInterval
          p approximationError ∧
        0 ≤ polynomialDenseModelError
          p cutError approximationError ∧
        polynomialDenseModelError
            p cutError approximationError ≤ target := by
  let approximationError : ℝ := target / 16
  have happroximationError : 0 < approximationError := by
    dsimp [approximationError]
    positivity
  obtain ⟨p, hp⟩ :=
    exists_polynomial_approximating_positivePart
      happroximationError
  let L : ℝ := polynomialCoefficientL1 p
  have hL : 0 ≤ L := by
    exact polynomialCoefficientL1_nonneg p
  have hLone : 0 < L + 1 := by
    linarith
  let cutError : ℝ :=
    min 1 (target / (4 * (L + 1)))
  have hquotient :
      0 < target / (4 * (L + 1)) := by
    positivity
  have hcutError : 0 < cutError := by
    exact lt_min zero_lt_one hquotient
  have hcutError_one : cutError ≤ 1 := by
    exact min_le_left _ _
  have hcutError_quotient :
      cutError ≤ target / (4 * (L + 1)) := by
    exact min_le_right _ _
  have hratio : L / (L + 1) ≤ 1 := by
    exact (div_le_one hLone).2 (by linarith)
  have hlinear :
      L * cutError ≤ target / 4 := by
    calc
      L * cutError ≤
          L * (target / (4 * (L + 1))) :=
        mul_le_mul_of_nonneg_left
          hcutError_quotient hL
      _ = (target / 4) * (L / (L + 1)) := by
        field_simp [ne_of_gt hLone]
      _ ≤ (target / 4) * 1 :=
        mul_le_mul_of_nonneg_left hratio
          (by positivity)
      _ = target / 4 := by ring
  have happroximation :
      approximationError * (2 + cutError) ≤
        3 * target / 16 := by
    have hsum : 2 + cutError ≤ 3 := by
      linarith
    calc
      approximationError * (2 + cutError) ≤
          approximationError * 3 :=
        mul_le_mul_of_nonneg_left hsum
          happroximationError.le
      _ = 3 * target / 16 := by
        simp only [approximationError]
        ring
  have hmodel_nonneg :
      0 ≤
        polynomialDenseModelError
          p cutError approximationError := by
    unfold polynomialDenseModelError
    exact add_nonneg
      (mul_nonneg hL hcutError.le)
      (mul_nonneg happroximationError.le
        (by linarith))
  have hmodel_le :
      polynomialDenseModelError
          p cutError approximationError ≤ target := by
    unfold polynomialDenseModelError
    change
      L * cutError +
          approximationError * (2 + cutError) ≤
        target
    linarith
  exact
    ⟨p, cutError, approximationError,
      hcutError, happroximationError, hp,
      hmodel_nonneg, hmodel_le⟩

/-! ## A complete finite transference package -/

/-- All small numerical data needed to combine polynomial dense modelling
with the explicit relative-counting recurrence. -/
structure RelativeCountingTransferenceParameters
    (r : ℕ) (densityReserve countReserve : ℝ) where
  polynomial : ℝ[X]
  cutError : ℝ
  approximationError : ℝ
  linearFormsError : ℝ
  crossError : ℝ
  cutError_pos : 0 < cutError
  approximationError_pos : 0 < approximationError
  linearFormsError_pos : 0 < linearFormsError
  crossError_pos : 0 < crossError
  approximates :
    ApproximatesPositivePartOnUnitInterval
      polynomial approximationError
  denseModelError_nonneg :
    0 ≤ polynomialDenseModelError
      polynomial cutError approximationError
  denseModelError_lt :
    polynomialDenseModelError
        polynomial cutError approximationError <
      densityReserve
  denseModel_conversion :
    (2 : ℝ) ^ (2 ^ (r + 1)) * linearFormsError ≤
      cutError ^ (2 ^ (r + 1))
  cross_conversion :
    ∀ j : Fin (r + 2),
      (1 + linearFormsError) ^ (2 ^ (r + 1) - 1) *
          ((2 : ℝ) ^
            Fintype.card (DeletedCube (r + 2) j) *
              linearFormsError) ≤
        crossError ^ (2 ^ (r + 1))
  comparisonError_lt :
    relativeCountingErrorSchedule r
        (polynomialDenseModelError
          polynomial cutError approximationError)
        linearFormsError crossError (r + 2) <
      countReserve

/-- Positive density and count reserves yield a complete numerical
transference package. -/
theorem RelativeCountingTransferenceParameters.nonempty
    (r : ℕ) {densityReserve countReserve : ℝ}
    (hdensity : 0 < densityReserve)
    (hcount : 0 < countReserve) :
    Nonempty
      (RelativeCountingTransferenceParameters
        r densityReserve countReserve) := by
  obtain ⟨target, htarget, htargetDensity, htargetOne,
      htargetSchedule⟩ :=
    exists_relativeCountingErrorSchedule_diagonal_lt
      r (r + 2) hdensity hcount
  obtain ⟨p, cutError, approximationError,
      hcutError, happroximationError, hp,
      hmodel_nonneg, hmodel_le⟩ :=
    exists_polynomialDenseModelError_le htarget
  let exponent : ℕ := 2 ^ (r + 1)
  let denseCoefficient : ℝ := (2 : ℝ) ^ exponent
  let crossCoefficient : ℝ :=
    (2 : ℝ) ^ (exponent - 1) *
      (2 : ℝ) ^ exponent
  have hdenseCoefficient : 0 < denseCoefficient := by
    dsimp [denseCoefficient]
    positivity
  have hcrossCoefficient : 0 < crossCoefficient := by
    dsimp [crossCoefficient]
    positivity
  let denseQuotient : ℝ :=
    cutError ^ exponent / (denseCoefficient + 1)
  let crossQuotient : ℝ :=
    target ^ exponent / (crossCoefficient + 1)
  have hdenseQuotient : 0 < denseQuotient := by
    dsimp [denseQuotient]
    positivity
  have hcrossQuotient : 0 < crossQuotient := by
    dsimp [crossQuotient]
    positivity
  let base : ℝ :=
    min 1
      (min target
        (min denseQuotient crossQuotient))
  have hbase : 0 < base := by
    dsimp [base]
    exact
      lt_min zero_lt_one
        (lt_min htarget
          (lt_min hdenseQuotient hcrossQuotient))
  let linearFormsError : ℝ := base / 2
  let crossError : ℝ := target
  have hlinearFormsError : 0 < linearFormsError := by
    dsimp [linearFormsError]
    linarith
  have hcrossError : 0 < crossError := by
    exact htarget
  have hlinearFormsError_le_base :
      linearFormsError ≤ base := by
    dsimp [linearFormsError]
    linarith
  have hbase_one : base ≤ 1 := by
    exact min_le_left _ _
  have hbase_target : base ≤ target := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        (min_le_left target
          (min denseQuotient crossQuotient))
  have hbase_dense : base ≤ denseQuotient := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        ((min_le_right target
          (min denseQuotient crossQuotient)).trans
          (min_le_left denseQuotient crossQuotient))
  have hbase_cross : base ≤ crossQuotient := by
    exact
      (min_le_right 1
        (min target
          (min denseQuotient crossQuotient))).trans
        ((min_le_right target
          (min denseQuotient crossQuotient)).trans
          (min_le_right denseQuotient crossQuotient))
  have hlinearFormsError_one :
      linearFormsError ≤ 1 :=
    hlinearFormsError_le_base.trans hbase_one
  have hlinearFormsError_target :
      linearFormsError ≤ target :=
    hlinearFormsError_le_base.trans hbase_target
  have hlinearFormsError_dense :
      linearFormsError ≤ denseQuotient :=
    hlinearFormsError_le_base.trans hbase_dense
  have hlinearFormsError_cross :
      linearFormsError ≤ crossQuotient :=
    hlinearFormsError_le_base.trans hbase_cross
  have hdenseConversion :
      denseCoefficient * linearFormsError ≤
        cutError ^ exponent := by
    have hden :
        0 < denseCoefficient + 1 := by
      linarith
    have hmul :
        linearFormsError * (denseCoefficient + 1) ≤
          cutError ^ exponent :=
      (le_div_iff₀ hden).mp
        (by
          simpa [denseQuotient] using
            hlinearFormsError_dense)
    calc
      denseCoefficient * linearFormsError ≤
          (denseCoefficient + 1) * linearFormsError := by
        exact mul_le_mul_of_nonneg_right
          (by linarith) hlinearFormsError.le
      _ = linearFormsError *
          (denseCoefficient + 1) := by ring
      _ ≤ cutError ^ exponent := hmul
  have hcrossConversionBase :
      crossCoefficient * linearFormsError ≤
        target ^ exponent := by
    have hden :
        0 < crossCoefficient + 1 := by
      linarith
    have hmul :
        linearFormsError * (crossCoefficient + 1) ≤
          target ^ exponent :=
      (le_div_iff₀ hden).mp
        (by
          simpa [crossQuotient] using
            hlinearFormsError_cross)
    calc
      crossCoefficient * linearFormsError ≤
          (crossCoefficient + 1) *
            linearFormsError := by
        exact mul_le_mul_of_nonneg_right
          (by linarith) hlinearFormsError.le
      _ = linearFormsError *
          (crossCoefficient + 1) := by ring
      _ ≤ target ^ exponent := hmul
  have hcrossConversion :
      ∀ j : Fin (r + 2),
        (1 + linearFormsError) ^
              (2 ^ (r + 1) - 1) *
            ((2 : ℝ) ^
                Fintype.card
                  (DeletedCube (r + 2) j) *
              linearFormsError) ≤
          crossError ^ (2 ^ (r + 1)) := by
    intro j
    have hbasePow :
        (1 + linearFormsError) ^ (exponent - 1) ≤
          (2 : ℝ) ^ (exponent - 1) := by
      gcongr
      linarith
    rw [card_deletedCube]
    change
      (1 + linearFormsError) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) ≤
        crossError ^ exponent
    calc
      (1 + linearFormsError) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) ≤
          (2 : ℝ) ^ (exponent - 1) *
            ((2 : ℝ) ^ exponent *
              linearFormsError) := by
        exact mul_le_mul_of_nonneg_right hbasePow
          (mul_nonneg (by positivity)
            hlinearFormsError.le)
      _ = crossCoefficient * linearFormsError := by
        dsimp [crossCoefficient]
        ring
      _ ≤ target ^ exponent :=
        hcrossConversionBase
      _ = crossError ^ exponent := rfl
  have hschedule :
      relativeCountingErrorSchedule r
          (polynomialDenseModelError
            p cutError approximationError)
          linearFormsError crossError (r + 2) <
        countReserve := by
    have hmono :=
      relativeCountingErrorSchedule_mono r
        hmodel_nonneg hlinearFormsError.le
        hcrossError.le htarget.le
        hmodel_le hlinearFormsError_target
        (le_rfl : crossError ≤ target) (r + 2)
    exact hmono.trans_lt htargetSchedule
  refine ⟨{
    polynomial := p
    cutError := cutError
    approximationError := approximationError
    linearFormsError := linearFormsError
    crossError := crossError
    cutError_pos := hcutError
    approximationError_pos := happroximationError
    linearFormsError_pos := hlinearFormsError
    crossError_pos := hcrossError
    approximates := hp
    denseModelError_nonneg := hmodel_nonneg
    denseModelError_lt := hmodel_le.trans_lt htargetDensity
    denseModel_conversion := ?_
    cross_conversion := hcrossConversion
    comparisonError_lt := hschedule }⟩
  simpa [denseCoefficient, exponent] using
    hdenseConversion

/-! ## Instantiating the comparison callback -/

/-- A relative AP comparison remains valid after enlarging its scalar count
error. -/
theorem RelativeAPComparisonLe.mono_countError
    {r N : ℕ} [NeZero N]
    {ν : ZMod N → ℝ} {cutError countError₁ countError₂ : ℝ}
    (hcomparison :
      RelativeAPComparisonLe
        r N ν cutError countError₁)
    (hcount : countError₁ ≤ countError₂) :
    RelativeAPComparisonLe
      r N ν cutError countError₂ := by
  intro f g hf0 hfν hg hcut
  exact
    (hcomparison f g hf0 hfν hg hcut).trans hcount

/-- The selected package turns a linear-forms condition at its chosen error
into the comparison callback needed by cofinal prime transference. -/
theorem RelativeCountingTransferenceParameters.relativeAPComparisonLe
    {r N : ℕ} [NeZero N]
    {densityReserve countReserve : ℝ}
    (P : RelativeCountingTransferenceParameters
      r densityReserve countReserve)
    {ν : ZMod N → ℝ}
    (hLF :
      HasLinearFormsCondition
        (r + 2) N ν P.linearFormsError)
    (hν : ∀ z, 0 ≤ ν z)
    (hN : Nat.Coprime N (Nat.factorial (r + 1))) :
    RelativeAPComparisonLe r N ν
      (polynomialDenseModelError
        P.polynomial P.cutError P.approximationError)
      countReserve := by
  apply RelativeAPComparisonLe.mono_countError
    (hLF.relativeAPComparisonLe_of_errorSchedule
      hν P.denseModelError_nonneg
      P.linearFormsError_pos.le
      P.crossError_pos.le
      P.cross_conversion hN)
  exact P.comparisonError_lt.le

end Wikipedia.SzemeredisTheorem
