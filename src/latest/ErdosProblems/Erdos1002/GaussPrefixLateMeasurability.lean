import ErdosProblems.Erdos1002.GaussPrefixMarkedCarrierGoodEvent
import ErdosProblems.Erdos1002.GaussPrefixFutureMixing
import ErdosProblems.Erdos1002.GaussDigitQuasiBernoulli
import ErdosProblems.Erdos1002.PrefixFreezingPointwise
import ErdosProblems.Erdos1002.PrefixFreezingAggregate
import ErdosProblems.Erdos1002.GaussSignedApproximationWindows
import ErdosProblems.Erdos1002.GaussHeterogeneousTupleBounds
import ErdosProblems.Erdos1002.GaussHeterogeneousTupleReplacement

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Genuine prefix measurability in the late marked-Fourier case

The late-case mixing argument must not pass a future denominator condition
through `psi`-mixing.  This file therefore defines the truncated denominator
good event as the inverse image of a set of complete depth-`m` words.  Its
measurability with respect to `sigma(a₁,...,a_m)` is then literal.  On the
common nonterminating full-measure set it is exactly the simultaneous
denominator estimate at every depth `n ≤ m`.

We also package the representative-point frozen prefix character as an
actual function of the selected depth-`m` word, prove its prefix
measurability and unit bound, and specialize the already-proved functional
prefix--future mixing theorem to this frozen factor and a finite future
digit block.
-/

open Filter MeasureTheory Set ProbabilityTheory
open scoped BigOperators ENNReal Topology

namespace Erdos1002

noncomputable section

local instance gaussPrefixLateMeasurabilityPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

variable {ι : Type*} [Fintype ι]

/-- Complete depth-`m` words satisfying the simultaneous denominator
deviation bound through `m`, with the ambient scale `L` kept separate from
the cutoff depth. -/
def gaussDenominatorPrefixGoodWords
    (m L : ℕ) (Delta : ℝ) : Set (PositiveDigitWord m) :=
  {w | ∀ (n : ℕ) (hn : n ≤ m),
    |Real.log
        (cfTerminalDenominator
          (positiveDigitWordTake n hn w).1 : ℝ) -
      (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ)}

/-- The genuinely prefix-measurable denominator good event used at a late
split. -/
def gaussDenominatorPrefixGoodEvent
    (m L : ℕ) (Delta : ℝ) : Set ℝ :=
  (selectedGaussPrefixWord m) ⁻¹'
    gaussDenominatorPrefixGoodWords m L Delta

/-- Prefix measurability is a definition-level fact: the event is an inverse
image under the selected depth-`m` word. -/
theorem measurableSet_gaussDenominatorPrefixGoodEvent_prefix
    (m L : ℕ) (Delta : ℝ) :
    @MeasurableSet ℝ (gaussPrefixMeasurableSpace m)
      (gaussDenominatorPrefixGoodEvent m L Delta) := by
  rw [MeasurableSpace.measurableSet_comap]
  refine ⟨gaussDenominatorPrefixGoodWords m L Delta, ?_, rfl⟩
  exact MeasurableSpace.measurableSet_top

/-- The prefix good event is also an ordinary Borel event. -/
theorem measurableSet_gaussDenominatorPrefixGoodEvent
    (m L : ℕ) (Delta : ℝ) :
    MeasurableSet (gaussDenominatorPrefixGoodEvent m L Delta) := by
  exact (gaussPrefixMeasurableSpace_le m)
    (gaussDenominatorPrefixGoodEvent m L Delta)
    (measurableSet_gaussDenominatorPrefixGoodEvent_prefix m L Delta)

/-- On every nonterminating unit-interval point, the word-based prefix event
is exactly the pointwise simultaneous selected-denominator condition. -/
theorem mem_gaussDenominatorPrefixGoodEvent_iff
    {m L : ℕ} {Delta x : ℝ}
    (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0) :
    x ∈ gaussDenominatorPrefixGoodEvent m L Delta ↔
      ∀ n : ℕ, n ≤ m →
        |Real.log
            (cfTerminalDenominator
              (selectedGaussPrefixWord n x).1 : ℝ) -
          (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ) := by
  let w : PositiveDigitWord m := selectedGaussPrefixWord m x
  have hdomain : x ∈ positivePrefixDomain m :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hxCell : x ∈ positivePrefixCylinder m w :=
    selectedGaussPrefixWord_mem hdomain
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hxUnit.1.le, hxUnit.2⟩
  change
    (∀ (n : ℕ) (hn : n ≤ m),
      |Real.log
          (cfTerminalDenominator
            (positiveDigitWordTake n hn w).1 : ℝ) -
        (n : ℝ) * gaussRoofMean| ≤ Delta * (L : ℝ)) ↔ _
  constructor
  · intro hall n hn
    have hselected := selectedGaussPrefixWord_eq_positiveDigitWordTake
      hn w hxIco hxCell
    rw [hselected]
    exact hall n hn
  · intro hall n hn
    have hselected := selectedGaussPrefixWord_eq_positiveDigitWordTake
      hn w hxIco hxCell
    rw [← hselected]
    exact hall n hn

/-- Exponentiated denominator bounds encoded directly by one prefix-good
word.  This word-level version avoids reintroducing any future-dependent
point when the frozen-coordinate radii are estimated. -/
theorem positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
    {m L n : ℕ} {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (hn : n ≤ m) :
    Real.exp ((n : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ≤
        (cfTerminalDenominator
          (positiveDigitWordTake n hn w).1 : ℝ) ∧
      (cfTerminalDenominator
          (positiveDigitWordTake n hn w).1 : ℝ) ≤
        Real.exp ((n : ℝ) * gaussRoofMean + Delta * (L : ℝ)) := by
  have hlog := abs_le.mp (hw n hn)
  have hdenPos : (0 : ℝ) <
      cfTerminalDenominator
        (positiveDigitWordTake n hn w).1 := by
    exact_mod_cast cfTerminalDenominator_pos
      (positiveDigitWordTake n hn w).2.2
  constructor
  · calc
      Real.exp ((n : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ≤
          Real.exp (Real.log
            (cfTerminalDenominator
              (positiveDigitWordTake n hn w).1 : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith [hlog.1])
      _ = (cfTerminalDenominator
          (positiveDigitWordTake n hn w).1 : ℝ) :=
        Real.exp_log hdenPos
  · calc
      (cfTerminalDenominator
          (positiveDigitWordTake n hn w).1 : ℝ) =
          Real.exp (Real.log
            (cfTerminalDenominator
              (positiveDigitWordTake n hn w).1 : ℝ)) :=
        (Real.exp_log hdenPos).symm
      _ ≤ Real.exp ((n : ℝ) * gaussRoofMean + Delta * (L : ℝ)) :=
        Real.exp_le_exp.mpr (by linarith [hlog.2])

/-- At the product cutoff `m = C L`, the genuine prefix event agrees almost
everywhere with the global denominator event already proved to have
probability tending to one. -/
theorem gaussDenominatorPrefixGoodEvent_ae_eq_linearGoodEvent
    (C L : ℕ) (Delta : ℝ) :
    gaussDenominatorPrefixGoodEvent (C * L) L Delta
        =ᵐ[uniform01Measure]
      gaussDenominatorLinearGoodEvent C L Delta := by
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  apply propext
  change
    (x ∈ gaussDenominatorPrefixGoodEvent (C * L) L Delta) ↔
      x ∈ gaussDenominatorLinearGoodEvent C L Delta
  rw [mem_gaussDenominatorPrefixGoodEvent_iff hxgood.1 hxgood.2]
  rfl

/-- Every global good point is, almost everywhere, a truncated prefix-good
point at any deterministic cutoff `m ≤ C L`. -/
theorem gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent
    {C L m : ℕ} {Delta : ℝ} (hm : m ≤ C * L) :
    gaussDenominatorLinearGoodEvent C L Delta
      ≤ᵐ[uniform01Measure]
        gaussDenominatorPrefixGoodEvent m L Delta := by
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  intro hxGlobal
  apply (mem_gaussDenominatorPrefixGoodEvent_iff
    hxgood.1 hxgood.2).2
  intro n hn
  exact hxGlobal n (hn.trans hm)

/-- Hence the truncated prefix-good complement is no larger, in measure,
than the already-controlled global bad event. -/
theorem uniform01Measure_prefixGoodEvent_compl_le_linearGoodEvent_compl
    {C L m : ℕ} {Delta : ℝ} (hm : m ≤ C * L) :
    uniform01Measure.real
        (gaussDenominatorPrefixGoodEvent m L Delta)ᶜ ≤
      uniform01Measure.real
        (gaussDenominatorLinearGoodEvent C L Delta)ᶜ := by
  have hsubset :=
    (gaussDenominatorLinearGoodEvent_ae_subset_prefixGoodEvent
      (Delta := Delta) hm).compl
  have hmeasure := measure_mono_ae hsubset
  exact ENNReal.toReal_mono (measure_ne_top uniform01Measure _) hmeasure

/-- Process-level high probability for every deterministic prefix cutoff
eventually bounded by one fixed linear window. -/
theorem tendsto_gaussDenominatorPrefixGoodEvent_compl_uniform_zero
    {C : ℕ} (hC : 0 < C) {Delta : ℝ} (hDelta : 0 < Delta)
    (m : ℕ → ℕ) (hm : ∀ᶠ L : ℕ in atTop, m L ≤ C * L) :
    Tendsto
      (fun L : ℕ ↦ uniform01Measure.real
        (gaussDenominatorPrefixGoodEvent (m L) L Delta)ᶜ)
      atTop (𝓝 0) := by
  have hglobal :=
    tendsto_gaussDenominatorLinearGoodEvent_compl_uniform_zero hC hDelta
  have hupper : ∀ᶠ L : ℕ in atTop,
      uniform01Measure.real
          (gaussDenominatorPrefixGoodEvent (m L) L Delta)ᶜ ≤
        uniform01Measure.real
          (gaussDenominatorLinearGoodEvent C L Delta)ᶜ := by
    filter_upwards [hm] with L hLm
    exact uniform01Measure_prefixGoodEvent_compl_le_linearGoodEvent_compl hLm
  exact squeeze_zero'
    (Eventually.of_forall fun _ ↦ measureReal_nonneg) hupper hglobal

/-! ## Prefix-measurable Lebesgue-to-Gauss density -/

/-- The transfer density frozen at the canonical representative of the
selected depth-`b` cylinder.  Unlike an abstract conditional-expectation
notation, this is a literal function of the first `b` digits. -/
def gaussPrefixFrozenLebesgueDensity (b : ℕ) (x : ℝ) : ℝ :=
  gaussLebesguePrefixWeight
    (gaussPrefixRepresentative (selectedGaussPrefixWord b x).1)

theorem measurable_gaussPrefixFrozenLebesgueDensity_prefix (b : ℕ) :
    @Measurable ℝ ℝ (gaussPrefixMeasurableSpace b) (borel ℝ)
      (gaussPrefixFrozenLebesgueDensity b) := by
  letI : MeasurableSpace (PositiveDigitWord b) := ⊤
  let G : PositiveDigitWord b → ℝ := fun w ↦
    gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1)
  have hselected :
      @Measurable ℝ (PositiveDigitWord b)
        (gaussPrefixMeasurableSpace b) ⊤
        (selectedGaussPrefixWord b) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hG : @Measurable (PositiveDigitWord b) ℝ ⊤ (borel ℝ) G :=
    measurable_of_countable G
  have hcomp := hG.comp hselected
  simpa only [G, gaussPrefixFrozenLebesgueDensity,
    Function.comp_apply] using! hcomp

/-- Explicit uniform-on-cylinders error bound on the common
nonterminating unit-interval set. -/
theorem abs_gaussPrefixFrozenLebesgueDensity_sub_le
    {b : ℕ} {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0) :
    |gaussPrefixFrozenLebesgueDensity b x -
        gaussLebesguePrefixWeight x| ≤
      Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) := by
  have hdomain : x ∈ positivePrefixDomain b :=
    mem_positivePrefixDomain_of_nonterminating hxUnit hxNonterm
  have hxCell : x ∈ positivePrefixCylinder b
      (selectedGaussPrefixWord b x) :=
    selectedGaussPrefixWord_mem hdomain
  have heq := gaussPrefixWeightApproximation_eq_on_cell
    b (selectedGaussPrefixWord b x) hxCell
  unfold gaussPrefixFrozenLebesgueDensity
  rw [← heq]
  exact abs_gaussPrefixWeightApproximation_sub_le b hdomain

/-- The same density approximation as an almost-everywhere uniform bound,
ready for multiplication by an entire finite factorial sum. -/
theorem ae_abs_gaussPrefixFrozenLebesgueDensity_sub_le (b : ℕ) :
    ∀ᵐ x ∂uniform01Measure,
      |gaussPrefixFrozenLebesgueDensity b x -
          gaussLebesguePrefixWeight x| ≤
        Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) := by
  filter_upwards [ae_nonterminating_uniform01] with x hxgood
  exact abs_gaussPrefixFrozenLebesgueDensity_sub_le hxgood.1 hxgood.2

theorem ae_gauss_abs_gaussPrefixFrozenLebesgueDensity_sub_le (b : ℕ) :
    ∀ᵐ x ∂gaussMeasure,
      |gaussPrefixFrozenLebesgueDensity b x -
          gaussLebesguePrefixWeight x| ≤
        Real.log 2 * (1 / 4 : ℝ) ^ (b / 2) := by
  filter_upwards [ae_nonterminating_gaussMeasure] with x hxgood
  exact abs_gaussPrefixFrozenLebesgueDensity_sub_le hxgood.1 hxgood.2

/-- Exact change of measure for complex expectations.  This equality is
the starting point of the density-freezing argument; in particular, the
Lebesgue density is not an informal multiplicative correction inserted
after mixing. -/
theorem integral_uniform01_eq_integral_gaussLebesguePrefixWeight_mul
    (f : ℝ → ℂ) :
    (∫ x, f x ∂uniform01Measure) =
      ∫ x, (gaussLebesguePrefixWeight x : ℂ) * f x
        ∂gaussMeasure := by
  rw [uniform01Measure_eq_gaussMeasure_withDensity,
    integral_withDensity_eq_integral_toReal_smul
      measurable_lebesgueOverGaussDensity
      (Eventually.of_forall fun _x ↦ ENNReal.ofReal_lt_top)]
  apply integral_congr_ae
  filter_upwards [gaussMeasure_unit_ae] with x hx
  have hxIcc : x ∈ Icc (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  have hnonneg : 0 ≤ lebesgueOverGaussDensityReal x :=
    (lebesgueOverGaussDensityReal_bounds hxIcc).1.trans'
      (Real.log_pos one_lt_two).le
  change (ENNReal.ofReal (lebesgueOverGaussDensityReal x)).toReal • f x =
    (gaussLebesguePrefixWeight x : ℂ) * f x
  rw [ENNReal.toReal_ofReal hnonneg]
  simp only [gaussLebesguePrefixWeight, Complex.real_smul]

/-- Finite-family density replacement with the absolute value outside the
complete sum.  This is the deterministic inequality behind the aggregate
Lebesgue-to-Gauss transfer; the cost is the uniform density error times the
whole `L¹` mass, not the number of tuples. -/
theorem norm_sum_integral_realDensityDifference_mul_le
    {Ω U : Type*} [Fintype U] [MeasurableSpace Ω]
    (mu : Measure Ω) (weight frozen : Ω → ℝ) (delta : ℝ)
    (f : U → Ω → ℂ)
    (hfi : ∀ u, Integrable (f u) mu)
    (hdiff : ∀ᵐ x ∂mu, |frozen x - weight x| ≤ delta) :
    ‖∑ u, ∫ x,
        ((frozen x - weight x : ℝ) : ℂ) * f u x ∂mu‖ ≤
      delta * ∑ u, ∫ x, ‖f u x‖ ∂mu := by
  calc
    ‖∑ u, ∫ x,
        ((frozen x - weight x : ℝ) : ℂ) * f u x ∂mu‖ ≤
        ∑ u, ‖∫ x,
          ((frozen x - weight x : ℝ) : ℂ) * f u x ∂mu‖ :=
      norm_sum_le _ _
    _ ≤ ∑ u, delta * ∫ x, ‖f u x‖ ∂mu := by
      apply Finset.sum_le_sum
      intro u _hu
      have hmajor : Integrable (fun x ↦ delta * ‖f u x‖) mu :=
        (hfi u).norm.const_mul delta
      calc
        ‖∫ x, ((frozen x - weight x : ℝ) : ℂ) * f u x ∂mu‖ ≤
            ∫ x, delta * ‖f u x‖ ∂mu := by
          apply norm_integral_le_of_norm_le hmajor
          filter_upwards [hdiff] with x hx
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul_of_nonneg_right hx (norm_nonneg _)
        _ = delta * ∫ x, ‖f u x‖ ∂mu :=
          integral_const_mul delta (fun x ↦ ‖f u x‖)
    _ = delta * ∑ u, ∫ x, ‖f u x‖ ∂mu := by
      rw [Finset.mul_sum]

/-- Concrete aggregate density replacement for the frozen depth-`b`
Lebesgue-to-Gauss weight. -/
theorem norm_sum_integral_gaussPrefixFrozenDensity_sub_le
    {U : Type*} [Fintype U] (b : ℕ) (f : U → ℝ → ℂ)
    (hfi : ∀ u, Integrable (f u) gaussMeasure) :
    ‖∑ u, ∫ x,
        ((gaussPrefixFrozenLebesgueDensity b x -
          gaussLebesguePrefixWeight x : ℝ) : ℂ) * f u x
            ∂gaussMeasure‖ ≤
      (Real.log 2 * (1 / 4 : ℝ) ^ (b / 2)) *
        ∑ u, ∫ x, ‖f u x‖ ∂gaussMeasure := by
  exact norm_sum_integral_realDensityDifference_mul_le gaussMeasure
    gaussLebesguePrefixWeight (gaussPrefixFrozenLebesgueDensity b)
      (Real.log 2 * (1 / 4 : ℝ) ^ (b / 2)) f hfi
      (ae_gauss_abs_gaussPrefixFrozenLebesgueDensity_sub_le b)

/-! ## Frozen prefix as an actual function of the selected word -/

/-- Every point of a positive closed cylinder lies within twice the inverse
square terminal-denominator scale of the canonical representative.  This
explicit arithmetic diameter estimate is the phase-freezing input; the
weaker depth-only contraction bound is not used. -/
theorem abs_sub_gaussPrefixRepresentative_le_two_div_terminalDenominator_sq
    {w : List ℕ} (hpos : IsPositiveCFWord w) {x : ℝ}
    (hx : x ∈ closedGaussPrefixCylinder w) :
    |x - gaussPrefixRepresentative w| ≤
      2 / (cfTerminalDenominator w : ℝ) ^ 2 := by
  rcases hx with ⟨y, hy, rfl⟩
  let endpoint : ℝ :=
    ((gaussPrefixMobius w).B : ℝ) / (gaussPrefixMobius w).D
  have hDpos : (0 : ℝ) < (gaussPrefixMobius w).D := by
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  have hclose (z : ℝ) (hz : z ∈ Icc (0 : ℝ) 1) :
      |gaussInverseWord w z - endpoint| ≤
        1 / (cfTerminalDenominator w : ℝ) ^ 2 := by
    have hformula := abs_gaussInverseWord_sub_terminalRatio hpos hz.1
    have hCnonneg : (0 : ℝ) ≤ (gaussPrefixMobius w).C := by positivity
    have hCznonneg :
        (0 : ℝ) ≤ ((gaussPrefixMobius w).C : ℝ) * z :=
      mul_nonneg hCnonneg hz.1
    have hdenLower :
        ((gaussPrefixMobius w).D : ℝ) ^ 2 ≤
          ((gaussPrefixMobius w).D : ℝ) *
            (((gaussPrefixMobius w).C : ℝ) * z +
              (gaussPrefixMobius w).D) := by
      rw [pow_two]
      exact mul_le_mul_of_nonneg_left
        (le_add_of_nonneg_left hCznonneg) hDpos.le
    calc
      |gaussInverseWord w z - endpoint| =
          z /
            ((gaussPrefixMobius w).D *
              (((gaussPrefixMobius w).C : ℝ) * z +
                (gaussPrefixMobius w).D)) := by
        simpa only [endpoint] using! hformula
      _ ≤ 1 / ((gaussPrefixMobius w).D : ℝ) ^ 2 := by
        apply div_le_div₀
        · norm_num
        · exact hz.2
        · positivity
        · exact hdenLower
      _ = 1 / (cfTerminalDenominator w : ℝ) ^ 2 := by
        rw [gaussPrefixMobius_D_eq_terminalDenominator]
  have hyClose := hclose y hy
  have hhalf : (1 / 2 : ℝ) ∈ Icc (0 : ℝ) 1 := by norm_num
  have hrepClose := hclose (1 / 2 : ℝ) hhalf
  unfold gaussPrefixRepresentative
  calc
    |gaussInverseWord w y - gaussInverseWord w (1 / 2)| ≤
        |gaussInverseWord w y - endpoint| +
          |endpoint - gaussInverseWord w (1 / 2)| :=
      abs_sub_le _ _ _
    _ ≤ 1 / (cfTerminalDenominator w : ℝ) ^ 2 +
        1 / (cfTerminalDenominator w : ℝ) ^ 2 := by
      gcongr
      simpa only [abs_sub_comm] using! hrepClose
    _ = 2 / (cfTerminalDenominator w : ℝ) ^ 2 := by ring

/-- Explicit phase-freezing error on one exact-depth cylinder. -/
theorem norm_oscillatoryPhase_sub_representative_le_terminalDenominator_sq
    (N : ℕ) {m : ℕ} (w : ExactDepthBoundedPositiveWord N m)
    (D : ℝ) {x : ℝ} (hx : x ∈ exactDepthBoundedCylinder w) :
    ‖oscillatoryPhase ((N : ℝ) * D) x -
        oscillatoryPhase ((N : ℝ) * D)
          (gaussPrefixRepresentative w.1.1)‖ ≤
      4 * Real.pi * (N : ℝ) * |D| /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
  have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
    gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
  have hdist :=
    abs_sub_gaussPrefixRepresentative_le_two_div_terminalDenominator_sq
      w.1.2.2.1 hxClosed
  have hphase := norm_oscillatoryPhase_sub_le
    ((N : ℝ) * D) x (gaussPrefixRepresentative w.1.1)
  calc
    ‖oscillatoryPhase ((N : ℝ) * D) x -
        oscillatoryPhase ((N : ℝ) * D)
          (gaussPrefixRepresentative w.1.1)‖ ≤
        2 * Real.pi * |(N : ℝ) * D| *
          |x - gaussPrefixRepresentative w.1.1| := hphase
    _ ≤ 2 * Real.pi * |(N : ℝ) * D| *
        (2 / (cfTerminalDenominator w.1.1 : ℝ) ^ 2) := by
      exact mul_le_mul_of_nonneg_left hdist (by positivity)
    _ = 4 * Real.pi * (N : ℝ) * |D| /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
      rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
      ring

/-- Prefix carrier computed directly from one complete depth-`m` word. -/
def gaussPrefixWordMixedPrefixCarrier
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) (m : ℕ)
    (w : PositiveDigitWord m) : ℝ :=
  ∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
    (h z.1.1 z.1.2 : ℝ) *
      (cfTerminalDenominator
        (positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w).1 : ℝ)

/-- On a denominator-bounded exact-depth word, the continuation-free word
carrier is exactly the previously named cylinder prefix carrier. -/
theorem gaussPrefixWordMixedPrefixCarrier_eq_exactDepthCylinder
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m) :
    gaussPrefixWordMixedPrefixCarrier N k h F m w.toPositive =
      exactDepthCylinderMixedPrefixCarrier N k h F w := by
  classical
  have hrepMem : gaussPrefixRepresentative w.1.1 ∈
      positivePrefixCylinder m w.toPositive :=
    gaussPrefixRepresentative_mem w.1.2.2.1
  have hrepUnit : gaussPrefixRepresentative w.1.1 ∈ Ico (0 : ℝ) 1 := by
    have hrepIoo : gaussPrefixRepresentative w.1.1 ∈ Ioo (0 : ℝ) 1 := by
      unfold gaussPrefixRepresentative
      exact gaussInverseWord_mem_Ioo w.1.2.2.1 (by norm_num)
    exact ⟨hrepIoo.1.le, hrepIoo.2⟩
  unfold gaussPrefixWordMixedPrefixCarrier
    exactDepthCylinderMixedPrefixCarrier
    gaussPrefixMarkedMixedPrefixCarrier
  rw [Finset.sum_subtype
    (p := fun z : GaussPrefixMixedOccurrence k ↦
      (F z.1 z.2 : ℕ) ≤ m)
    ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
      (fun z ↦ (F z.1 z.2 : ℕ) ≤ m))
    (by intro z; simp)
    (fun z ↦ (h z.1 z.2 : ℝ) *
      (cfTerminalDenominator
        (selectedGaussPrefixWord (F z.1 z.2)
          (gaussPrefixRepresentative w.1.1)).1 : ℝ))]
  apply Finset.sum_congr rfl
  intro z _hz
  have hselected := selectedGaussPrefixWord_eq_positiveDigitWordTake
    z.2 w.toPositive hrepUnit hrepMem
  rw [hselected]

/-- Absolute upper bound for the frozen prefix carrier in terms of the
terminal denominator at the last potentially nonzero depth. -/
theorem abs_gaussPrefixWordMixedPrefixCarrier_le_lastNonzero
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ : ℕ}
    (hn₀m : n₀ ≤ m) (w : PositiveDigitWord m)
    (hzeroAfter : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      h z.1.1 z.1.2 ≠ 0 → (F z.1.1 z.1.2 : ℕ) ≤ n₀) :
    |gaussPrefixWordMixedPrefixCarrier N k h F m w| ≤
      (∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
        |(h z.1.1 z.1.2 : ℝ)|) *
      (cfTerminalDenominator
        (positiveDigitWordTake n₀ hn₀m w).1 : ℝ) := by
  classical
  let u₀ : PositiveDigitWord n₀ := positiveDigitWordTake n₀ hn₀m w
  let q : GaussPrefixMixedPrefixOccurrence N k F m → ℝ := fun z ↦
    (cfTerminalDenominator
      (positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w).1 : ℝ)
  let weight : GaussPrefixMixedPrefixOccurrence N k F m → ℝ := fun z ↦
    |(h z.1.1 z.1.2 : ℝ)|
  have hq (z : GaussPrefixMixedPrefixOccurrence N k F m)
      (hz : h z.1.1 z.1.2 ≠ 0) :
      q z ≤ (cfTerminalDenominator u₀.1 : ℝ) := by
    have hzDepth := hzeroAfter z hz
    have hu₀val : u₀.1 = w.1.take n₀ := rfl
    have hnat := cfTerminalDenominator_take_le
      (F z.1.1 z.1.2 : ℕ) hzDepth u₀
    have hnat' :
        cfTerminalDenominator (w.1.take (F z.1.1 z.1.2 : ℕ)) ≤
          cfTerminalDenominator (w.1.take n₀) := by
      simpa only [positiveDigitWordTake_val, hu₀val, List.take_take,
        Nat.min_eq_left hzDepth] using! hnat
    dsimp only [q]
    rw [positiveDigitWordTake_val, hu₀val]
    exact_mod_cast hnat'
  unfold gaussPrefixWordMixedPrefixCarrier
  calc
    |∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
        (h z.1.1 z.1.2 : ℝ) * q z| ≤
        ∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
          |(h z.1.1 z.1.2 : ℝ) * q z| :=
      Finset.abs_sum_le_sum_abs _ _
    _ = ∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
        weight z * q z := by
      apply Finset.sum_congr rfl
      intro z _hz
      dsimp only [weight]
      rw [abs_mul]
      have hqNonneg : 0 ≤ q z := by
        dsimp only [q]
        positivity
      rw [abs_of_nonneg hqNonneg]
    _ ≤ ∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
        weight z * (cfTerminalDenominator u₀.1 : ℝ) := by
      apply Finset.sum_le_sum
      intro z _hz
      by_cases hz : h z.1.1 z.1.2 = 0
      · simp [weight, hz]
      · exact mul_le_mul_of_nonneg_left (hq z hz) (by
          dsimp only [weight]
          exact abs_nonneg _)
    _ = (∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
          |(h z.1.1 z.1.2 : ℝ)|) *
        (cfTerminalDenominator
          (positiveDigitWordTake n₀ hn₀m w).1 : ℝ) := by
      dsimp only [weight, u₀]
      rw [Finset.sum_mul]

/-- Phase-freezing error with the numerator reduced to the last nonzero
prefix denominator and the total absolute Fourier weight. -/
theorem norm_wordCarrierPhase_sub_representative_le_lastNonzero
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ : ℕ}
    (hn₀m : n₀ ≤ m) (w : ExactDepthBoundedPositiveWord N m)
    (hzeroAfter : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      h z.1.1 z.1.2 ≠ 0 → (F z.1.1 z.1.2 : ℕ) ≤ n₀)
    {x : ℝ} (hx : x ∈ exactDepthBoundedCylinder w) :
    ‖oscillatoryPhase
          ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
            N k h F m w.toPositive) x -
        oscillatoryPhase
          ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
            N k h F m w.toPositive)
          (gaussPrefixRepresentative w.1.1)‖ ≤
      4 * Real.pi * (N : ℝ) *
          ((∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
              |(h z.1.1 z.1.2 : ℝ)|) *
            (cfTerminalDenominator
              (positiveDigitWordTake n₀ hn₀m w.toPositive).1 : ℝ)) /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
  let D : ℝ :=
    gaussPrefixWordMixedPrefixCarrier N k h F m w.toPositive
  have hphase :=
    norm_oscillatoryPhase_sub_representative_le_terminalDenominator_sq
      N w D hx
  have hcarrier :=
    abs_gaussPrefixWordMixedPrefixCarrier_le_lastNonzero
      N k h F hn₀m w.toPositive hzeroAfter
  calc
    ‖oscillatoryPhase ((N : ℝ) * D) x -
        oscillatoryPhase ((N : ℝ) * D)
          (gaussPrefixRepresentative w.1.1)‖ ≤
      4 * Real.pi * (N : ℝ) * |D| /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := hphase
    _ ≤ 4 * Real.pi * (N : ℝ) *
          ((∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
              |(h z.1.1 z.1.2 : ℝ)|) *
            (cfTerminalDenominator
              (positiveDigitWordTake n₀ hn₀m w.toPositive).1 : ℝ)) /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hcarrier (by positivity)
      · positivity

/-- The absolute good-event carrier floor also applies verbatim to the
continuation-free word carrier used in the frozen formula. -/
theorem exp_half_le_abs_gaussPrefixWordMixedPrefixCarrier_of_gap_goodPoint
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k)
    {C L m gap : ℕ} {Delta x : ℝ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z₀ : GaussPrefixMixedOccurrence k)
    (hdepth : (F z₀.1 z₀.2 : ℕ) = m)
    (hcoeff : h z₀.1 z₀.2 ≠ 0)
    (hgap : ∀ z : GaussPrefixMixedOccurrence k, z ≠ z₀ →
      h z.1 z.2 ≠ 0 → (F z.1 z.2 : ℕ) + gap ≤ m)
    (hweightBudget :
      2 * (∑ z ∈
          ((Finset.univ : Finset (GaussPrefixMixedOccurrence k)).filter
            (fun z ↦ (F z.1 z.2 : ℕ) ≤ m)).erase z₀,
        |(h z.1 z.2 : ℝ)|) ≤ ((2 ^ (gap / 2) : ℕ) : ℝ))
    (hm : m ≤ C * L)
    (hxGood : x ∈ gaussDenominatorLinearGoodEvent C L Delta)
    (hxCell : x ∈ exactDepthBoundedCylinder w) :
    Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) / 2 ≤
      |gaussPrefixWordMixedPrefixCarrier
        N k h F m w.toPositive| := by
  rw [gaussPrefixWordMixedPrefixCarrier_eq_exactDepthCylinder]
  exact exp_half_le_abs_exactDepthCylinderMixedPrefixCarrier_of_gap_goodPoint
    N k h F w z₀ hdepth hcoeff hgap hweightBudget hm hxGood hxCell

/-- Affine signed value at the canonical representative, computed from the
truncated word and therefore independent of any continuation of that
representative beyond depth `m`. -/
def gaussPrefixWordFrozenMarkedValue
    (N : ℕ) (k : ι → ℕ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (w : PositiveDigitWord m)
    (z : GaussPrefixMixedPrefixOccurrence N k F m) : ℝ :=
  gaussPrefixMarkedValueSlope N
      (positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w) *
      gaussPrefixRepresentative w.1 +
    gaussPrefixMarkedValueIntercept N
      (positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w)

omit [Fintype ι] in
/-- Explicit value-coordinate freezing error on one deepest cylinder. -/
theorem abs_selectedMarkedValue_sub_wordFrozen_le
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (z : GaussPrefixMixedPrefixOccurrence N k F m)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    |(gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
        (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 -
      gaussPrefixWordFrozenMarkedValue N k F m w.toPositive z| ≤
      2 * Real.log (N : ℝ) *
          (cfTerminalDenominator
            (positiveDigitWordTake (F z.1.1 z.1.2 : ℕ)
              z.2 w.toPositive).1 : ℝ) ^ 2 /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
  let u : PositiveDigitWord (F z.1.1 z.1.2 : ℕ) :=
    positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w.toPositive
  have hvalue :=
    selectedGaussPrefixMarkedPoint_value_eq_affine_on_deeperCylinder
      (N := N) z.2 w.toPositive hxUnit hxNonterm hx
  rw [hvalue]
  have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
    gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
  have hdist :=
    abs_sub_gaussPrefixRepresentative_le_two_div_terminalDenominator_sq
      w.1.2.2.1 hxClosed
  have hlog : 0 ≤ Real.log (N : ℝ) :=
    (Real.log_pos (by exact_mod_cast hN)).le
  unfold gaussPrefixWordFrozenMarkedValue gaussPrefixMarkedValueSlope
  change
    |Real.log (N : ℝ) *
          (cfTerminalDenominator u.1 : ℝ) ^ 2 * x +
        gaussPrefixMarkedValueIntercept N u -
      (Real.log (N : ℝ) *
          (cfTerminalDenominator u.1 : ℝ) ^ 2 *
            gaussPrefixRepresentative w.1.1 +
        gaussPrefixMarkedValueIntercept N u)| ≤ _
  rw [show
    Real.log (N : ℝ) * (cfTerminalDenominator u.1 : ℝ) ^ 2 * x +
          gaussPrefixMarkedValueIntercept N u -
        (Real.log (N : ℝ) * (cfTerminalDenominator u.1 : ℝ) ^ 2 *
            gaussPrefixRepresentative w.1.1 +
          gaussPrefixMarkedValueIntercept N u) =
      (Real.log (N : ℝ) * (cfTerminalDenominator u.1 : ℝ) ^ 2) *
        (x - gaussPrefixRepresentative w.1.1) by ring]
  rw [abs_mul, abs_of_nonneg
    (mul_nonneg hlog (sq_nonneg (cfTerminalDenominator u.1 : ℝ)))]
  calc
    (Real.log (N : ℝ) * (cfTerminalDenominator u.1 : ℝ) ^ 2) *
        |x - gaussPrefixRepresentative w.1.1| ≤
      (Real.log (N : ℝ) * (cfTerminalDenominator u.1 : ℝ) ^ 2) *
        (2 / (cfTerminalDenominator w.1.1 : ℝ) ^ 2) :=
      mul_le_mul_of_nonneg_left hdist
        (mul_nonneg hlog (sq_nonneg _))
    _ = 2 * Real.log (N : ℝ) *
          (cfTerminalDenominator u.1 : ℝ) ^ 2 /
        (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by ring

/-- A single continuation-free radius controlling every retained value
coordinate whose depth is at most `n₀`.  The numerator uses only the
depth-`n₀` prefix denominator, while the denominator is the terminal
denominator of the deepest cylinder. -/
def gaussPrefixWordValueFreezingRadius
    (N n₀ : ℕ) {m : ℕ} (hn₀m : n₀ ≤ m)
    (w : PositiveDigitWord m) : ℝ :=
  2 * Real.log (N : ℝ) *
      (cfTerminalDenominator
      (positiveDigitWordTake n₀ hn₀m w).1 : ℝ) ^ 2 /
    (cfTerminalDenominator w.1 : ℝ) ^ 2

/-- On a prefix-good word the common value-freezing radius has the explicit
exponential gap bound dictated by the denominator large-deviation window.
The estimate is stated as a quotient of exponentials so that no hidden
algebraic simplification of the `Delta * L` loss is needed. -/
theorem gaussPrefixWordValueFreezingRadius_le_expGap
    (N : ℕ) (hN : 2 ≤ N) {m L n₀ : ℕ} (hn₀m : n₀ ≤ m)
    {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta) :
    gaussPrefixWordValueFreezingRadius N n₀ hn₀m w ≤
      2 * Real.log (N : ℝ) *
          Real.exp ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ)) ^ 2 /
        Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 := by
  have hQ₀ :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w hw hn₀m).2
  have hQm :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w hw (le_refl m)).1
  have htake : w.1.take m = w.1 := by
    exact List.take_of_length_le w.2.1.le
  have hQm' :
      Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ≤
        (cfTerminalDenominator w.1 : ℝ) := by
    simpa only [positiveDigitWordTake_val, htake] using! hQm
  have hQ₀nonneg : (0 : ℝ) ≤
      cfTerminalDenominator
        (positiveDigitWordTake n₀ hn₀m w).1 := by positivity
  have hQmNonneg : (0 : ℝ) ≤ cfTerminalDenominator w.1 := by positivity
  have hQ₀square :
      (cfTerminalDenominator
          (positiveDigitWordTake n₀ hn₀m w).1 : ℝ) ^ 2 ≤
        Real.exp
          ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ)) ^ 2 := by
    nlinarith [Real.exp_pos
      ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ))]
  have hQmsquare :
      Real.exp
          ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 ≤
        (cfTerminalDenominator w.1 : ℝ) ^ 2 := by
    nlinarith [hQm', Real.exp_pos
      ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ))]
  unfold gaussPrefixWordValueFreezingRadius
  apply div_le_div₀
  · exact mul_nonneg (mul_nonneg (by norm_num)
      (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
      (sq_nonneg _)
  · exact mul_le_mul_of_nonneg_left hQ₀square (by
      exact mul_nonneg (by norm_num)
        (Real.log_nonneg (by exact_mod_cast (show 1 ≤ N by omega))))
  · positivity
  · exact hQmsquare

/-- Equivalent single-exponential form of the value-freezing gap.  It
exhibits the negative contribution `-2 (m-n₀) gaussRoofMean` and the full
`4 Delta L` good-event loss without suppressing either constant. -/
theorem gaussPrefixWordValueFreezingRadius_le_singleExpGap
    (N : ℕ) (hN : 2 ≤ N) {m L n₀ : ℕ} (hn₀m : n₀ ≤ m)
    {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta) :
    gaussPrefixWordValueFreezingRadius N n₀ hn₀m w ≤
      2 * Real.log (N : ℝ) *
        Real.exp (2 *
          (((n₀ : ℝ) - (m : ℝ)) * gaussRoofMean +
            2 * Delta * (L : ℝ))) := by
  calc
    gaussPrefixWordValueFreezingRadius N n₀ hn₀m w ≤
        2 * Real.log (N : ℝ) *
            Real.exp
              ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ)) ^ 2 /
          Real.exp
              ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 :=
      gaussPrefixWordValueFreezingRadius_le_expGap
        N hN hn₀m w hw
    _ = 2 * Real.log (N : ℝ) *
        Real.exp (2 *
          (((n₀ : ℝ) - (m : ℝ)) * gaussRoofMean +
            2 * Delta * (L : ℝ))) := by
      rw [mul_div_assoc, ← Real.exp_nat_mul, ← Real.exp_nat_mul,
        ← Real.exp_sub]
      congr 2
      push_cast
      ring

/-- Word-independent phase radius on the prefix-good event. -/
def gaussPrefixGoodCylinderPhaseRadius
    (m L : ℕ) (Delta : ℝ) : ℝ :=
  2 /
    Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2

/-- Word-independent value-coordinate radius on the prefix-good event. -/
def gaussPrefixGoodValueFreezingRadius
    (N n₀ m L : ℕ) (Delta : ℝ) : ℝ :=
  2 * Real.log (N : ℝ) *
    Real.exp (2 *
      (((n₀ : ℝ) - (m : ℝ)) * gaussRoofMean +
        2 * Delta * (L : ℝ)))

/-- Every prefix-good word has cylinder diameter at most the common phase
radius. -/
theorem two_div_terminalDenominator_sq_le_goodPhaseRadius
    {m L : ℕ} {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta) :
    2 / (cfTerminalDenominator w.1 : ℝ) ^ 2 ≤
      gaussPrefixGoodCylinderPhaseRadius m L Delta := by
  have hQm :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w hw (le_refl m)).1
  have htake : w.1.take m = w.1 :=
    List.take_of_length_le w.2.1.le
  have hQm' :
      Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ≤
        (cfTerminalDenominator w.1 : ℝ) := by
    simpa only [positiveDigitWordTake_val, htake] using! hQm
  have hsquare :
      Real.exp ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 ≤
        (cfTerminalDenominator w.1 : ℝ) ^ 2 := by
    nlinarith [hQm',
      Real.exp_pos ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)),
      show (0 : ℝ) ≤ cfTerminalDenominator w.1 by positivity]
  unfold gaussPrefixGoodCylinderPhaseRadius
  apply div_le_div₀
  · norm_num
  · exact le_rfl
  · positivity
  · exact hsquare

/-- Every word-dependent value radius is at most the common good-event
radius. -/
theorem gaussPrefixWordValueFreezingRadius_le_goodValueRadius
    (N : ℕ) (hN : 2 ≤ N) {m L n₀ : ℕ} (hn₀m : n₀ ≤ m)
    {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta) :
    gaussPrefixWordValueFreezingRadius N n₀ hn₀m w ≤
      gaussPrefixGoodValueFreezingRadius N n₀ m L Delta := by
  exact gaussPrefixWordValueFreezingRadius_le_singleExpGap
    N hN hn₀m w hw

/-- Word-independent upper bound for the phase coefficient appearing in
the common good-event envelope. -/
theorem goodEnvelope_phaseCoefficient_le
    (N : ℕ) (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ L : ℕ}
    (hn₀m : n₀ ≤ m) {Delta : ℝ} (w : PositiveDigitWord m)
    (hw : w ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (hzeroAfter : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      h z.1.1 z.1.2 ≠ 0 → (F z.1.1 z.1.2 : ℕ) ≤ n₀) :
    2 * Real.pi *
          |(N : ℝ) * gaussPrefixWordMixedPrefixCarrier N k h F m w| *
        gaussPrefixGoodCylinderPhaseRadius m L Delta ≤
      4 * Real.pi * (N : ℝ) *
          ((∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
              |(h z.1.1 z.1.2 : ℝ)|) *
            Real.exp
              ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ))) /
        Real.exp
          ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 := by
  have hcarrier := abs_gaussPrefixWordMixedPrefixCarrier_le_lastNonzero
    N k h F hn₀m w hzeroAfter
  have hQ₀ :=
    (positiveWordTerminalDenominator_exp_bounds_of_mem_prefixGoodWords
      w hw hn₀m).2
  have hweightNonneg : 0 ≤
      ∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
        |(h z.1.1 z.1.2 : ℝ)| :=
    Finset.sum_nonneg fun _z _hz ↦ abs_nonneg _
  have hcarrierExp :
      |gaussPrefixWordMixedPrefixCarrier N k h F m w| ≤
        (∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
            |(h z.1.1 z.1.2 : ℝ)|) *
          Real.exp
            ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ)) := by
    exact hcarrier.trans (mul_le_mul_of_nonneg_left hQ₀ hweightNonneg)
  unfold gaussPrefixGoodCylinderPhaseRadius
  rw [abs_mul, abs_of_nonneg (Nat.cast_nonneg N)]
  calc
    2 * Real.pi * ((N : ℝ) *
          |gaussPrefixWordMixedPrefixCarrier N k h F m w|) *
        (2 /
          Real.exp
            ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2) =
      (4 * Real.pi * (N : ℝ) *
          |gaussPrefixWordMixedPrefixCarrier N k h F m w|) /
        Real.exp
          ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 := by ring
    _ ≤ (4 * Real.pi * (N : ℝ) *
          ((∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
              |(h z.1.1 z.1.2 : ℝ)|) *
            Real.exp
              ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ)))) /
        Real.exp
          ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hcarrierExp (by positivity)
      · positivity
    _ = 4 * Real.pi * (N : ℝ) *
          ((∑ z : GaussPrefixMixedPrefixOccurrence N k F m,
              |(h z.1.1 z.1.2 : ℝ)|) *
            Real.exp
              ((n₀ : ℝ) * gaussRoofMean + Delta * (L : ℝ))) /
        Real.exp
          ((m : ℝ) * gaussRoofMean - Delta * (L : ℝ)) ^ 2 := by ring

omit [Fintype ι] in
/-- The preceding coordinatewise estimate is uniformly bounded by the
single last-prefix radius.  This is the deterministic step needed before
the endpoint-strip errors can be summed over a fixed tuple. -/
theorem abs_selectedMarkedValue_sub_wordFrozen_le_lastPrefixRadius
    (N : ℕ) (hN : 2 ≤ N) (k : ι → ℕ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ : ℕ}
    (hn₀m : n₀ ≤ m) (w : ExactDepthBoundedPositiveWord N m)
    (z : GaussPrefixMixedPrefixOccurrence N k F m)
    (hzDepth : (F z.1.1 z.1.2 : ℕ) ≤ n₀)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    |(gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
        (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 -
      gaussPrefixWordFrozenMarkedValue N k F m w.toPositive z| ≤
      gaussPrefixWordValueFreezingRadius N n₀ hn₀m w.toPositive := by
  let u₀ : PositiveDigitWord n₀ :=
    positiveDigitWordTake n₀ hn₀m w.toPositive
  let u : PositiveDigitWord (F z.1.1 z.1.2 : ℕ) :=
    positiveDigitWordTake (F z.1.1 z.1.2 : ℕ) z.2 w.toPositive
  have hbase := abs_selectedMarkedValue_sub_wordFrozen_le
    N hN k F w z hxUnit hxNonterm hx
  have hu₀val : u₀.1 = w.1.1.take n₀ := rfl
  have hnat := cfTerminalDenominator_take_le
    (F z.1.1 z.1.2 : ℕ) hzDepth u₀
  have hQnat :
      cfTerminalDenominator u.1 ≤ cfTerminalDenominator u₀.1 := by
    simpa only [u, positiveDigitWordTake_val, hu₀val, List.take_take,
      Nat.min_eq_left hzDepth] using! hnat
  have hQ :
      (cfTerminalDenominator u.1 : ℝ) ≤
        (cfTerminalDenominator u₀.1 : ℝ) := by
    exact_mod_cast hQnat
  have hQnonneg : (0 : ℝ) ≤ cfTerminalDenominator u.1 := by positivity
  have hQ₀nonneg : (0 : ℝ) ≤ cfTerminalDenominator u₀.1 := by positivity
  have hsquare :
      (cfTerminalDenominator u.1 : ℝ) ^ 2 ≤
        (cfTerminalDenominator u₀.1 : ℝ) ^ 2 := by
    nlinarith
  calc
    |(gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
          (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 -
        gaussPrefixWordFrozenMarkedValue N k F m w.toPositive z| ≤
        2 * Real.log (N : ℝ) *
            (cfTerminalDenominator u.1 : ℝ) ^ 2 /
          (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
      simpa only [u] using! hbase
    _ ≤ 2 * Real.log (N : ℝ) *
            (cfTerminalDenominator u₀.1 : ℝ) ^ 2 /
          (cfTerminalDenominator w.1.1 : ℝ) ^ 2 := by
      apply div_le_div_of_nonneg_right
      · exact mul_le_mul_of_nonneg_left hsquare (by
          positivity)
      · positivity
    _ = gaussPrefixWordValueFreezingRadius
          N n₀ hn₀m w.toPositive := by
      rfl

/-- The paper's frozen compact-window prefix factor in a continuation-free
form: a fixed carrier phase times the finite product of affine value-window
indicators, all evaluated from the selected depth-`m` word. -/
def gaussPrefixAffineFrozenCompactCharacter
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) : ℂ :=
  let w := selectedGaussPrefixWord m x
  if w ∈ goodWords then
    oscillatoryPhase
        ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier N k h F m w)
        (gaussPrefixRepresentative w.1) *
      ((∏ z : GaussPrefixMixedPrefixOccurrence N k F m,
        closedIntervalIndicator (lower z.1.1) (upper z.1.1)
          (gaussPrefixWordFrozenMarkedValue N k F m w z) : ℝ) : ℂ)
  else 0

/-- On a nonterminating point of one deepest cylinder, the literal compact
prefix character is exactly its word carrier phase times the product of the
actual signed-value indicators. -/
theorem gaussPrefixMarkedMixedPrefixCharacter_compactValue_eq_wordPhase
    (N : ℕ) (hN : 2 ≤ N) (lower upper : ι → ℝ)
    {A : ℝ} (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ r : ℕ, (gaussMap^[r]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    gaussPrefixMarkedMixedPrefixCharacter N
        (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
        k h F m x =
      oscillatoryPhase
          ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
            N k h F m w.toPositive) x *
        ((∏ z : GaussPrefixMixedPrefixOccurrence N k F m,
          closedIntervalIndicator (lower z.1.1) (upper z.1.1)
            ((gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
              (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1) : ℝ) :
            ℂ) := by
  classical
  let B : ι → Set (ℝ × ℝ × ℝ) := fun i ↦
    compactValueMarkedRegion (lower i) (upper i)
  by_cases hall : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      x ∈ gaussPrefixMarkedEvent N (B z.1.1) (F z.1.1 z.1.2)
  · have hxEvents : ∀ z : GaussPrefixMixedOccurrence k,
        (F z.1 z.2 : ℕ) ≤ m →
          x ∈ gaussPrefixMarkedEvent N (B z.1) (F z.1 z.2) := by
      intro z hz
      exact hall ⟨z, hz⟩
    have hcharacter :=
      gaussPrefixMarkedMixedPrefixCharacter_eq_oscillatoryPhase
        (h := h) (F := F) hxUnit hxNonterm hxEvents
    have hcarrier :=
      gaussPrefixMarkedMixedPrefixCarrier_eq_exactDepthCylinder
        N k h F w ⟨hxUnit.1.le, hxUnit.2⟩ hx
    have hword :=
      gaussPrefixWordMixedPrefixCarrier_eq_exactDepthCylinder
        N k h F w
    have hindicators :
        (∏ z : GaussPrefixMixedPrefixOccurrence N k F m,
          closedIntervalIndicator (lower z.1.1) (upper z.1.1)
            ((gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
              (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1)) = 1 := by
      apply Finset.prod_eq_one
      intro z _hz
      have hvalue :=
        (mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
          hN z.2 w.toPositive (hlower z.1.1) (hupper z.1.1) hsmall
          w.1.2.2.2 hxUnit hxNonterm hx).1 (hall z)
      simp only [closedIntervalIndicator, if_pos hvalue]
    rw [hcharacter, hcarrier, ← hword, hindicators]
    simp
  · push_neg at hall
    obtain ⟨z, hzNot⟩ := hall
    have hvalueNot :
        (gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
          (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1 ∉
            Icc (lower z.1.1) (upper z.1.1) := by
      exact fun hzValue ↦ hzNot
        ((mem_gaussPrefixMarkedEvent_compactValue_iff_on_deeperCylinder
          hN z.2 w.toPositive (hlower z.1.1) (hupper z.1.1) hsmall
          w.1.2.2.2 hxUnit hxNonterm hx).2 hzValue)
    have hcharacterZero :
        gaussPrefixMarkedMixedPrefixCharacter N B k h F m x = 0 := by
      unfold gaussPrefixMarkedMixedPrefixCharacter
      apply Finset.prod_eq_zero
      · exact Finset.mem_filter.mpr ⟨Finset.mem_univ z.1, z.2⟩
      · unfold gaussPrefixMarkedDepthCharacter
        rw [if_neg hzNot]
    have hindicatorZero :
        (∏ z' : GaussPrefixMixedPrefixOccurrence N k F m,
          closedIntervalIndicator (lower z'.1.1) (upper z'.1.1)
            ((gaussPrefixMarkedPoint N (F z'.1.1 z'.1.2)
              (selectedGaussPrefixWord (F z'.1.1 z'.1.2) x) x).2.1)) = 0 := by
      apply Finset.prod_eq_zero (Finset.mem_univ z)
      simp only [closedIntervalIndicator, if_neg hvalueNot]
    rw [show gaussPrefixMarkedMixedPrefixCharacter N
      (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
        k h F m x = 0 by simpa only [B] using! hcharacterZero,
      hindicatorZero]
    simp

/-- Concrete pointwise prefix-freezing inequality.  An explicit finite
enumeration of the retained occurrences is accepted only to reuse the
generic finite-coordinate envelope; both the actual and frozen factors are
the literal functions defined above. -/
theorem norm_mixedPrefixCharacter_sub_affineFrozen_le_freezingEnvelope
    (N : ℕ) (hN : 2 ≤ N) (lower upper : ι → ℝ)
    {A : ℝ} (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m r : ℕ}
    (w : ExactDepthBoundedPositiveWord N m)
    (e : Fin r ≃ GaussPrefixMixedPrefixOccurrence N k F m)
    (goodWords : Set (PositiveDigitWord m))
    (hwGood : w.toPositive ∈ goodWords)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w)
    {phaseRadius eta : ℝ}
    (hphaseRadius : 0 ≤ phaseRadius) (heta : 0 ≤ eta)
    (halpha : |x - gaussPrefixRepresentative w.1.1| ≤ phaseRadius)
    (hcoordinate : ∀ i : Fin r,
      |(gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
          (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1 -
        gaussPrefixWordFrozenMarkedValue
          N k F m w.toPositive (e i)| ≤ eta) :
    ‖gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m x -
        gaussPrefixAffineFrozenCompactCharacter N lower upper k h F m
          goodWords x‖ ≤
      oscillatoryPrefixFreezingEnvelope
        (fun i ↦ lower (e i).1.1)
        (fun i ↦ upper (e i).1.1)
        (fun i ↦
          (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
            (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1)
        ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
          N k h F m w.toPositive) phaseRadius eta := by
  classical
  let actualCoordinate : Fin r → ℝ := fun i ↦
    (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
      (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1
  let frozenCoordinate : Fin r → ℝ := fun i ↦
    gaussPrefixWordFrozenMarkedValue N k F m w.toPositive (e i)
  let a : Fin r → ℝ := fun i ↦ lower (e i).1.1
  let b : Fin r → ℝ := fun i ↦ upper (e i).1.1
  let K : ℝ := (N : ℝ) *
    gaussPrefixWordMixedPrefixCarrier N k h F m w.toPositive
  let representative : ℝ := gaussPrefixRepresentative w.1.1
  have hprodActual := e.prod_comp (fun z ↦
    closedIntervalIndicator (lower z.1.1) (upper z.1.1)
      ((gaussPrefixMarkedPoint N (F z.1.1 z.1.2)
        (selectedGaussPrefixWord (F z.1.1 z.1.2) x) x).2.1))
  have hprodFrozen := e.prod_comp (fun z ↦
    closedIntervalIndicator (lower z.1.1) (upper z.1.1)
      (gaussPrefixWordFrozenMarkedValue N k F m w.toPositive z))
  have hactual :
      gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m x =
        oscillatoryWindowProduct a b actualCoordinate K x := by
    rw [gaussPrefixMarkedMixedPrefixCharacter_compactValue_eq_wordPhase
      N hN lower upper hlower hupper hsmall k h F w
        hxUnit hxNonterm hx]
    unfold oscillatoryWindowProduct closedIntervalIndicatorProduct
    dsimp only [a, b, actualCoordinate, K]
    rw [hprodActual]
  have hselected : selectedGaussPrefixWord m x = w.toPositive :=
    selectedGaussPrefixWord_eq_of_mem w.toPositive hx
  have hfrozen :
      gaussPrefixAffineFrozenCompactCharacter N lower upper k h F m
          goodWords x =
        oscillatoryWindowProduct a b frozenCoordinate K representative := by
    unfold gaussPrefixAffineFrozenCompactCharacter
    dsimp only
    rw [hselected, if_pos hwGood]
    unfold oscillatoryWindowProduct closedIntervalIndicatorProduct
    dsimp only [a, b, frozenCoordinate, K, representative]
    rw [show w.toPositive.1 = w.1.1 by rfl, ← hprodFrozen]
  rw [hactual, hfrozen]
  exact norm_oscillatoryWindowProduct_sub_le_freezingEnvelope
    a b actualCoordinate frozenCoordinate K x representative
      hphaseRadius heta halpha (by
        intro i
        exact hcoordinate i)

/-- Fully explicit pointwise freezing estimate on a deepest cylinder.  In
contrast with the preceding flexible form, neither a phase radius nor a
value-coordinate radius is assumed: both are forced by the cylinder
diameter and the last retained prefix depth `n₀`. -/
theorem norm_mixedPrefixCharacter_sub_affineFrozen_le_explicitEnvelope
    (N : ℕ) (hN : 2 ≤ N) (lower upper : ι → ℝ)
    {A : ℝ} (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ r : ℕ}
    (hn₀m : n₀ ≤ m)
    (hprefixDepth : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      (F z.1.1 z.1.2 : ℕ) ≤ n₀)
    (w : ExactDepthBoundedPositiveWord N m)
    (e : Fin r ≃ GaussPrefixMixedPrefixOccurrence N k F m)
    (goodWords : Set (PositiveDigitWord m))
    (hwGood : w.toPositive ∈ goodWords)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    ‖gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m x -
        gaussPrefixAffineFrozenCompactCharacter N lower upper k h F m
          goodWords x‖ ≤
      oscillatoryPrefixFreezingEnvelope
        (fun i ↦ lower (e i).1.1)
        (fun i ↦ upper (e i).1.1)
        (fun i ↦
          (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
            (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1)
        ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
          N k h F m w.toPositive)
        (2 / (cfTerminalDenominator w.1.1 : ℝ) ^ 2)
        (gaussPrefixWordValueFreezingRadius
          N n₀ hn₀m w.toPositive) := by
  apply norm_mixedPrefixCharacter_sub_affineFrozen_le_freezingEnvelope
    N hN lower upper hlower hupper hsmall k h F w e goodWords hwGood
      hxUnit hxNonterm hx
  · positivity
  · unfold gaussPrefixWordValueFreezingRadius
    positivity
  · have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
      gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
    exact abs_sub_gaussPrefixRepresentative_le_two_div_terminalDenominator_sq
      w.1.2.2.1 hxClosed
  · intro i
    exact abs_selectedMarkedValue_sub_wordFrozen_le_lastPrefixRadius
      N hN k F hn₀m w (e i) (hprefixDepth (e i))
        hxUnit hxNonterm hx

/-- Prefix-good specialization with radii independent of the individual
deepest word.  Consequently every retained cell at the same depths uses
the same enlarged windows and endpoint strips in the aggregate estimate. -/
theorem norm_mixedPrefixCharacter_sub_affineFrozen_le_commonGoodEnvelope
    (N : ℕ) (hN : 2 ≤ N) (lower upper : ι → ℝ)
    {A : ℝ} (hlower : ∀ i, |lower i| ≤ A)
    (hupper : ∀ i, |upper i| ≤ A)
    (hsmall : A / Real.log (N : ℝ) < (1 : ℝ) / 2)
    (k : ι → ℕ) (h : ∀ i, Fin (k i) → ℤ)
    (F : GaussPrefixMixedDepthTuple N k) {m n₀ L r : ℕ}
    {Delta : ℝ} (hn₀m : n₀ ≤ m)
    (hprefixDepth : ∀ z : GaussPrefixMixedPrefixOccurrence N k F m,
      (F z.1.1 z.1.2 : ℕ) ≤ n₀)
    (w : ExactDepthBoundedPositiveWord N m)
    (hwPrefixGood :
      w.toPositive ∈ gaussDenominatorPrefixGoodWords m L Delta)
    (e : Fin r ≃ GaussPrefixMixedPrefixOccurrence N k F m)
    (goodWords : Set (PositiveDigitWord m))
    (hwGood : w.toPositive ∈ goodWords)
    {x : ℝ} (hxUnit : x ∈ Ioo (0 : ℝ) 1)
    (hxNonterm : ∀ q : ℕ, (gaussMap^[q]) x ≠ 0)
    (hx : x ∈ exactDepthBoundedCylinder w) :
    ‖gaussPrefixMarkedMixedPrefixCharacter N
          (fun i ↦ compactValueMarkedRegion (lower i) (upper i))
          k h F m x -
        gaussPrefixAffineFrozenCompactCharacter N lower upper k h F m
          goodWords x‖ ≤
      oscillatoryPrefixFreezingEnvelope
        (fun i ↦ lower (e i).1.1)
        (fun i ↦ upper (e i).1.1)
        (fun i ↦
          (gaussPrefixMarkedPoint N (F (e i).1.1 (e i).1.2)
            (selectedGaussPrefixWord (F (e i).1.1 (e i).1.2) x) x).2.1)
        ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier
          N k h F m w.toPositive)
        (gaussPrefixGoodCylinderPhaseRadius m L Delta)
        (gaussPrefixGoodValueFreezingRadius N n₀ m L Delta) := by
  apply norm_mixedPrefixCharacter_sub_affineFrozen_le_freezingEnvelope
    N hN lower upper hlower hupper hsmall k h F w e goodWords hwGood
      hxUnit hxNonterm hx
  · unfold gaussPrefixGoodCylinderPhaseRadius
    positivity
  · unfold gaussPrefixGoodValueFreezingRadius
    have hlog : 0 ≤ Real.log (N : ℝ) :=
      (Real.log_pos (by exact_mod_cast hN)).le
    positivity
  · have hxClosed : x ∈ closedGaussPrefixCylinder w.1.1 :=
      gaussHalfOpenPrefixCylinder_subset_closed w.1.2.2.1 hx
    exact
      (abs_sub_gaussPrefixRepresentative_le_two_div_terminalDenominator_sq
        w.1.2.2.1 hxClosed).trans
        (two_div_terminalDenominator_sq_le_goodPhaseRadius
          w.toPositive hwPrefixGood)
  · intro i
    exact
      (abs_selectedMarkedValue_sub_wordFrozen_le_lastPrefixRadius
        N hN k F hn₀m w (e i) (hprefixDepth (e i))
          hxUnit hxNonterm hx).trans
        (gaussPrefixWordValueFreezingRadius_le_goodValueRadius
          N hN hn₀m w.toPositive hwPrefixGood)

/-- The continuation-free frozen compact factor has unit norm. -/
theorem norm_gaussPrefixAffineFrozenCompactCharacter_le_one
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) :
    ‖gaussPrefixAffineFrozenCompactCharacter
      N lower upper k h F m goodWords x‖ ≤ 1 := by
  classical
  unfold gaussPrefixAffineFrozenCompactCharacter
  dsimp only
  by_cases hw : selectedGaussPrefixWord m x ∈ goodWords
  · rw [if_pos hw, norm_mul, norm_oscillatoryPhase, one_mul,
      Complex.norm_real, Real.norm_eq_abs]
    have hnonneg : 0 ≤
        ∏ z : GaussPrefixMixedPrefixOccurrence N k F m,
          closedIntervalIndicator (lower z.1.1) (upper z.1.1)
            (gaussPrefixWordFrozenMarkedValue N k F m
              (selectedGaussPrefixWord m x) z) := by
      exact Finset.prod_nonneg fun z _hz ↦ by
        unfold closedIntervalIndicator
        split <;> norm_num
    rw [abs_of_nonneg hnonneg]
    apply Finset.prod_le_one
    · intro z _hz
      unfold closedIntervalIndicator
      split <;> norm_num
    · intro z _hz
      unfold closedIntervalIndicator
      split <;> norm_num
  · rw [if_neg hw]
    simp

/-- The continuation-free formula is genuinely prefix measurable. -/
theorem measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) :
    @Measurable ℝ ℂ (gaussPrefixMeasurableSpace m) (borel ℂ)
      (gaussPrefixAffineFrozenCompactCharacter
        N lower upper k h F m goodWords) := by
  letI : MeasurableSpace (PositiveDigitWord m) := ⊤
  let G : PositiveDigitWord m → ℂ := fun w ↦
    if w ∈ goodWords then
      oscillatoryPhase
          ((N : ℝ) * gaussPrefixWordMixedPrefixCarrier N k h F m w)
          (gaussPrefixRepresentative w.1) *
        ((∏ z : GaussPrefixMixedPrefixOccurrence N k F m,
          closedIntervalIndicator (lower z.1.1) (upper z.1.1)
            (gaussPrefixWordFrozenMarkedValue N k F m w z) : ℝ) : ℂ)
    else 0
  have hselected :
      @Measurable ℝ (PositiveDigitWord m)
        (gaussPrefixMeasurableSpace m) ⊤
        (selectedGaussPrefixWord m) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hG : @Measurable (PositiveDigitWord m) ℂ ⊤ (borel ℂ) G :=
    measurable_of_countable G
  have hcomp := hG.comp hselected
  simpa only [G, gaussPrefixAffineFrozenCompactCharacter,
    Function.comp_apply] using! hcomp

/-! ## The genuinely prefix-measurable Lebesgue-weighted factor -/

/-- The frozen compact prefix character with the frozen
Lebesgue-to-Gauss density included.  This is the literal prefix factor
which occurs after changing the original Lebesgue expectation to Gauss
measure; keeping the density inside the definition prevents it from being
silently discarded in the subsequent mixing step. -/
def gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) : ℂ :=
  (gaussPrefixFrozenLebesgueDensity m x : ℂ) *
    gaussPrefixAffineFrozenCompactCharacter
      N lower upper k h F m goodWords x

/-- The frozen density is uniformly bounded on every selected positive
prefix word. -/
theorem norm_gaussPrefixFrozenLebesgueDensity_le_two_log
    (m : ℕ) (x : ℝ) :
    ‖(gaussPrefixFrozenLebesgueDensity m x : ℂ)‖ ≤
      2 * Real.log 2 := by
  let w : PositiveDigitWord m := selectedGaussPrefixWord m x
  have hrepIoo : gaussPrefixRepresentative w.1 ∈ Ioo (0 : ℝ) 1 := by
    unfold gaussPrefixRepresentative
    exact gaussInverseWord_mem_Ioo w.2.2 (by norm_num)
  have hbounds := gaussLebesguePrefixWeight_bounds
    ⟨hrepIoo.1.le, hrepIoo.2.le⟩
  have hnonneg : 0 ≤
      gaussLebesguePrefixWeight (gaussPrefixRepresentative w.1) :=
    (Real.log_pos one_lt_two).le.trans hbounds.1
  rw [Complex.norm_real, Real.norm_eq_abs]
  change
    |gaussLebesguePrefixWeight
        (gaussPrefixRepresentative (selectedGaussPrefixWord m x).1)| ≤
      2 * Real.log 2
  simpa only [w, abs_of_nonneg hnonneg] using! hbounds.2

/-- The density-weighted affine frozen factor remains measurable with
respect to the first `m` digits. -/
theorem
    measurable_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_prefix
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) :
    @Measurable ℝ ℂ (gaussPrefixMeasurableSpace m) (borel ℂ)
      (gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
        N lower upper k h F m goodWords) := by
  exact
    (measurable_gaussPrefixFrozenLebesgueDensity_prefix m).complex_ofReal.mul
      (measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
        N lower upper k h F m goodWords)

/-- Uniform norm bound for the complete frozen prefix factor, including
the change-of-measure density. -/
theorem
    norm_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_le_two_log
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) :
    ‖gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
      N lower upper k h F m goodWords x‖ ≤ 2 * Real.log 2 := by
  rw [gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter, norm_mul]
  calc
    ‖(gaussPrefixFrozenLebesgueDensity m x : ℂ)‖ *
          ‖gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F m goodWords x‖ ≤
        ‖(gaussPrefixFrozenLebesgueDensity m x : ℂ)‖ * 1 := by
      exact mul_le_mul_of_nonneg_left
        (norm_gaussPrefixAffineFrozenCompactCharacter_le_one
          N lower upper k h F m goodWords x) (norm_nonneg _)
    _ ≤ 2 * Real.log 2 := by
      simpa using! norm_gaussPrefixFrozenLebesgueDensity_le_two_log m x

/-- Representative-point prefix character, set to zero outside a chosen
set of admissible depth-`m` words. -/
def gaussPrefixFrozenMixedPrefixCharacter
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) : ℂ :=
  let w := selectedGaussPrefixWord m x
  if w ∈ goodWords then
    gaussPrefixMarkedMixedPrefixCharacter N B k h F m
      (gaussPrefixRepresentative w.1)
  else 0

/-- The literal prefix character has norm at most one. -/
theorem norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (x : ℝ) :
    ‖gaussPrefixMarkedMixedPrefixCharacter N B k h F m x‖ ≤ 1 := by
  classical
  unfold gaussPrefixMarkedMixedPrefixCharacter
  rw [norm_prod]
  apply Finset.prod_le_one
  · intro z _hz
    exact norm_nonneg _
  · intro z _hz
    rw [norm_gaussPrefixMarkedDepthCharacter]
    split <;> norm_num

/-- The frozen prefix retains the same unit bound. -/
theorem norm_gaussPrefixFrozenMixedPrefixCharacter_le_one
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) (x : ℝ) :
    ‖gaussPrefixFrozenMixedPrefixCharacter
      N B k h F m goodWords x‖ ≤ 1 := by
  classical
  unfold gaussPrefixFrozenMixedPrefixCharacter
  dsimp only
  by_cases hw : selectedGaussPrefixWord m x ∈ goodWords
  · rw [if_pos hw]
    exact norm_gaussPrefixMarkedMixedPrefixCharacter_le_one
      N B k h F m _
  · rw [if_neg hw]
    simp

/-- The representative-point frozen factor is genuinely measurable with
respect to the first `m` digits; no approximation statement is used here. -/
theorem measurable_gaussPrefixFrozenMixedPrefixCharacter_prefix
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (m : ℕ) (goodWords : Set (PositiveDigitWord m)) :
    @Measurable ℝ ℂ (gaussPrefixMeasurableSpace m) (borel ℂ)
      (gaussPrefixFrozenMixedPrefixCharacter
        N B k h F m goodWords) := by
  letI : MeasurableSpace (PositiveDigitWord m) := ⊤
  let G : PositiveDigitWord m → ℂ := fun w ↦
    if w ∈ goodWords then
      gaussPrefixMarkedMixedPrefixCharacter N B k h F m
        (gaussPrefixRepresentative w.1)
    else 0
  have hselected :
      @Measurable ℝ (PositiveDigitWord m)
        (gaussPrefixMeasurableSpace m) ⊤
        (selectedGaussPrefixWord m) := by
    rw [measurable_iff_comap_le]
    exact le_rfl
  have hG : @Measurable (PositiveDigitWord m) ℂ ⊤ (borel ℂ) G :=
    measurable_of_countable G
  have hcomp := hG.comp hselected
  simpa only [G, gaussPrefixFrozenMixedPrefixCharacter,
    Function.comp_apply] using! hcomp

/-- A finite future digit block written as a function of the Gauss state at
the chosen future base. -/
def gaussFutureDigitBlockIndicator
    {r : ℕ} (base : ℕ) (times : Fin r → ℕ)
    (events : Fin r → Set ℝ) (x : ℝ) : ℂ :=
  ((gaussOrbit base) ⁻¹'
      shiftedGaussTailEvent base times events).indicator
    (fun _ ↦ (1 : ℂ)) x

/-- The future digit block is measurable in the future sigma-field at its
base time. -/
theorem measurable_gaussFutureDigitBlockIndicator_future
    {r : ℕ} (base : ℕ) (times : Fin r → ℕ)
    {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    @Measurable ℝ ℂ (gaussFutureMeasurableSpace base) (borel ℂ)
      (gaussFutureDigitBlockIndicator base times events) := by
  have htail : MeasurableSet (shiftedGaussTailEvent base times events) :=
    measurableSet_shiftedGaussTailEvent hEvents
  have hpre : @MeasurableSet ℝ (gaussFutureMeasurableSpace base)
      ((gaussOrbit base) ⁻¹' shiftedGaussTailEvent base times events) := by
    rw [MeasurableSpace.measurableSet_comap]
    exact ⟨shiftedGaussTailEvent base times events, htail, rfl⟩
  unfold gaussFutureDigitBlockIndicator
  exact Measurable.ite hpre measurable_const measurable_const

/-- Concrete functional `psi`-mixing for the frozen prefix and a finite
future digit block.  This is the exact covariance estimate used before the
aggregate double sum is factorized. -/
theorem gaussPrefixFrozen_futureDigitBlock_covariance_le
    (N : ℕ) (B : ι → Set (ℝ × ℝ × ℝ)) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    Integrable (fun x ↦
        gaussPrefixFrozenMixedPrefixCharacter N B k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x)
        gaussMeasure ∧
      ‖(∫ x,
          gaussPrefixFrozenMixedPrefixCharacter N B k h F b goodWords x *
            gaussFutureDigitBlockIndicator (b + gap) times events x
            ∂gaussMeasure) -
          (∫ x, gaussPrefixFrozenMixedPrefixCharacter
            N B k h F b goodWords x ∂gaussMeasure) *
          ∫ x, gaussFutureDigitBlockIndicator
            (b + gap) times events x ∂gaussMeasure‖ ≤
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (∫ x, ‖gaussPrefixFrozenMixedPrefixCharacter
            N B k h F b goodWords x‖ ∂gaussMeasure) *
          ∫ x, ‖gaussFutureDigitBlockIndicator
            (b + gap) times events x‖ ∂gaussMeasure := by
  let f : ℝ → ℂ :=
    gaussPrefixFrozenMixedPrefixCharacter N B k h F b goodWords
  let g : ℝ → ℂ :=
    gaussFutureDigitBlockIndicator (b + gap) times events
  have hfM : @Measurable ℝ ℂ (gaussPrefixMeasurableSpace b) (borel ℂ) f :=
    measurable_gaussPrefixFrozenMixedPrefixCharacter_prefix
      N B k h F b goodWords
  have hgM : @Measurable ℝ ℂ
      (gaussFutureMeasurableSpace (b + gap)) (borel ℂ) g :=
    measurable_gaussFutureDigitBlockIndicator_future
      (b + gap) times hEvents
  have hfBorel : Measurable f :=
    hfM.mono (gaussPrefixMeasurableSpace_le b) le_rfl
  have hgBorel : Measurable g :=
    hgM.mono (gaussFutureMeasurableSpace_le (b + gap)) le_rfl
  have hfi : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfBorel.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦
      norm_gaussPrefixFrozenMixedPrefixCharacter_le_one
        N B k h F b goodWords x
  have hgi : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgBorel.aestronglyMeasurable 1
    filter_upwards with x
    unfold g gaussFutureDigitBlockIndicator
    by_cases hx : x ∈
        (gaussOrbit (b + gap)) ⁻¹'
          shiftedGaussTailEvent (b + gap) times events
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  simpa only [f, g] using!
    gaussPrefixFuture_covariance_complex b gap hfM hgM hfi hgi

/-- Functional prefix--future covariance for the continuation-free affine
frozen factor used by the rigorous pointwise freezing estimate.  This
prevents an implicit substitution of the older representative-evaluation
factor in the late-case recombination. -/
theorem gaussPrefixAffineFrozen_futureDigitBlock_covariance_le
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    Integrable (fun x ↦
        gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x)
        gaussMeasure ∧
      ‖(∫ x,
          gaussPrefixAffineFrozenCompactCharacter
              N lower upper k h F b goodWords x *
            gaussFutureDigitBlockIndicator (b + gap) times events x
            ∂gaussMeasure) -
          (∫ x, gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x ∂gaussMeasure) *
          ∫ x, gaussFutureDigitBlockIndicator
            (b + gap) times events x ∂gaussMeasure‖ ≤
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (∫ x, ‖gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x‖ ∂gaussMeasure) *
          ∫ x, ‖gaussFutureDigitBlockIndicator
            (b + gap) times events x‖ ∂gaussMeasure := by
  let f : ℝ → ℂ :=
    gaussPrefixAffineFrozenCompactCharacter
      N lower upper k h F b goodWords
  let g : ℝ → ℂ :=
    gaussFutureDigitBlockIndicator (b + gap) times events
  have hfM : @Measurable ℝ ℂ (gaussPrefixMeasurableSpace b) (borel ℂ) f :=
    measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
      N lower upper k h F b goodWords
  have hgM : @Measurable ℝ ℂ
      (gaussFutureMeasurableSpace (b + gap)) (borel ℂ) g :=
    measurable_gaussFutureDigitBlockIndicator_future
      (b + gap) times hEvents
  have hfBorel : Measurable f :=
    hfM.mono (gaussPrefixMeasurableSpace_le b) le_rfl
  have hgBorel : Measurable g :=
    hgM.mono (gaussFutureMeasurableSpace_le (b + gap)) le_rfl
  have hfi : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfBorel.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦
      norm_gaussPrefixAffineFrozenCompactCharacter_le_one
        N lower upper k h F b goodWords x
  have hgi : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgBorel.aestronglyMeasurable 1
    filter_upwards with x
    unfold g gaussFutureDigitBlockIndicator
    by_cases hx : x ∈
        (gaussOrbit (b + gap)) ⁻¹'
          shiftedGaussTailEvent (b + gap) times events
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  simpa only [f, g] using!
    gaussPrefixFuture_covariance_complex b gap hfM hgM hfi hgi

/-- Unit-bound simplification of the affine frozen prefix--future
covariance. -/
theorem gaussPrefixAffineFrozen_futureDigitBlock_covariance_le_rate
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    ‖(∫ x,
        gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x
          ∂gaussMeasure) -
        (∫ x, gaussPrefixAffineFrozenCompactCharacter
          N lower upper k h F b goodWords x ∂gaussMeasure) *
        ∫ x, gaussFutureDigitBlockIndicator
          (b + gap) times events x ∂gaussMeasure‖ ≤
      192 * (527 / 540 : ℝ) ^ gap := by
  let f : ℝ → ℂ :=
    gaussPrefixAffineFrozenCompactCharacter
      N lower upper k h F b goodWords
  let g : ℝ → ℂ :=
    gaussFutureDigitBlockIndicator (b + gap) times events
  have hfM : Measurable f :=
    (measurable_gaussPrefixAffineFrozenCompactCharacter_prefix
      N lower upper k h F b goodWords).mono
        (gaussPrefixMeasurableSpace_le b) le_rfl
  have hgM : Measurable g :=
    (measurable_gaussFutureDigitBlockIndicator_future
      (b + gap) times hEvents).mono
        (gaussFutureMeasurableSpace_le (b + gap)) le_rfl
  have hfi : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfM.aestronglyMeasurable 1
    exact Eventually.of_forall fun x ↦
      norm_gaussPrefixAffineFrozenCompactCharacter_le_one
        N lower upper k h F b goodWords x
  have hgi : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgM.aestronglyMeasurable 1
    filter_upwards with x
    unfold g gaussFutureDigitBlockIndicator
    by_cases hx : x ∈
        (gaussOrbit (b + gap)) ⁻¹'
          shiftedGaussTailEvent (b + gap) times events
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  have hfIntegral : (∫ x, ‖f x‖ ∂gaussMeasure) ≤ 1 := by
    calc
      (∫ x, ‖f x‖ ∂gaussMeasure) ≤ ∫ _x, (1 : ℝ) ∂gaussMeasure := by
        apply integral_mono hfi.norm (integrable_const 1)
        intro x
        exact norm_gaussPrefixAffineFrozenCompactCharacter_le_one
          N lower upper k h F b goodWords x
      _ = 1 := by simp
  have hgIntegral : (∫ x, ‖g x‖ ∂gaussMeasure) ≤ 1 := by
    calc
      (∫ x, ‖g x‖ ∂gaussMeasure) ≤ ∫ _x, (1 : ℝ) ∂gaussMeasure := by
        apply integral_mono hgi.norm (integrable_const 1)
        intro x
        change ‖g x‖ ≤ 1
        unfold g gaussFutureDigitBlockIndicator
        by_cases hx : x ∈
            (gaussOrbit (b + gap)) ⁻¹'
              shiftedGaussTailEvent (b + gap) times events
        · rw [Set.indicator_of_mem hx]
          simp
        · rw [Set.indicator_of_notMem hx]
          simp
      _ = 1 := by simp
  have hraw :=
    (gaussPrefixAffineFrozen_futureDigitBlock_covariance_le
      N lower upper k h F b gap goodWords times hEvents).2
  calc
    ‖(∫ x, gaussPrefixAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x
          ∂gaussMeasure) -
        (∫ x, gaussPrefixAffineFrozenCompactCharacter
          N lower upper k h F b goodWords x ∂gaussMeasure) *
        ∫ x, gaussFutureDigitBlockIndicator
          (b + gap) times events x ∂gaussMeasure‖ ≤
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (∫ x, ‖f x‖ ∂gaussMeasure) *
          ∫ x, ‖g x‖ ∂gaussMeasure := by
      simpa only [f, g] using! hraw
    _ ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) * 1 * 1 := by
      have hcoef : 0 ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) := by
        positivity
      calc
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
              (∫ x, ‖f x‖ ∂gaussMeasure) *
              (∫ x, ‖g x‖ ∂gaussMeasure) ≤
            4 * (48 * (527 / 540 : ℝ) ^ gap) * 1 *
              (∫ x, ‖g x‖ ∂gaussMeasure) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfIntegral hcoef)
            (integral_nonneg fun _x ↦ norm_nonneg _)
        _ ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) * 1 * 1 := by
          exact mul_le_mul_of_nonneg_left hgIntegral
            (mul_nonneg hcoef zero_le_one)
    _ = 192 * (527 / 540 : ℝ) ^ gap := by ring

/-- Prefix--future covariance after the Lebesgue-to-Gauss density has been
frozen on the prefix cylinder.  Both functions in this statement are the
literal factors used by the late-case recombination. -/
theorem
    gaussPrefixLebesgueWeightedAffineFrozen_futureDigitBlock_covariance_le
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    Integrable (fun x ↦
        gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x)
        gaussMeasure ∧
      ‖(∫ x,
          gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
              N lower upper k h F b goodWords x *
            gaussFutureDigitBlockIndicator (b + gap) times events x
            ∂gaussMeasure) -
          (∫ x, gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x ∂gaussMeasure) *
          ∫ x, gaussFutureDigitBlockIndicator
            (b + gap) times events x ∂gaussMeasure‖ ≤
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (∫ x,
            ‖gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
              N lower upper k h F b goodWords x‖ ∂gaussMeasure) *
          ∫ x, ‖gaussFutureDigitBlockIndicator
            (b + gap) times events x‖ ∂gaussMeasure := by
  let f : ℝ → ℂ :=
    gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
      N lower upper k h F b goodWords
  let g : ℝ → ℂ :=
    gaussFutureDigitBlockIndicator (b + gap) times events
  have hfM : @Measurable ℝ ℂ
      (gaussPrefixMeasurableSpace b) (borel ℂ) f :=
    measurable_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_prefix
      N lower upper k h F b goodWords
  have hgM : @Measurable ℝ ℂ
      (gaussFutureMeasurableSpace (b + gap)) (borel ℂ) g :=
    measurable_gaussFutureDigitBlockIndicator_future
      (b + gap) times hEvents
  have hfBorel : Measurable f :=
    hfM.mono (gaussPrefixMeasurableSpace_le b) le_rfl
  have hgBorel : Measurable g :=
    hgM.mono (gaussFutureMeasurableSpace_le (b + gap)) le_rfl
  have hfi : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfBorel.aestronglyMeasurable (2 * Real.log 2)
    exact Eventually.of_forall fun x ↦
      norm_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_le_two_log
        N lower upper k h F b goodWords x
  have hgi : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgBorel.aestronglyMeasurable 1
    filter_upwards with x
    unfold g gaussFutureDigitBlockIndicator
    by_cases hx : x ∈
        (gaussOrbit (b + gap)) ⁻¹'
          shiftedGaussTailEvent (b + gap) times events
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  simpa only [f, g] using!
    gaussPrefixFuture_covariance_complex b gap hfM hgM hfi hgi

/-- Explicit rate for the preceding density-weighted covariance. -/
theorem
    gaussPrefixLebesgueWeightedAffineFrozen_futureDigitBlock_covariance_le_rate
    (N : ℕ) (lower upper : ι → ℝ) (k : ι → ℕ)
    (h : ∀ i, Fin (k i) → ℤ) (F : GaussPrefixMixedDepthTuple N k)
    (b gap : ℕ) (goodWords : Set (PositiveDigitWord b))
    {r : ℕ} (times : Fin r → ℕ) {events : Fin r → Set ℝ}
    (hEvents : ∀ i, MeasurableSet (events i)) :
    ‖(∫ x,
        gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x
          ∂gaussMeasure) -
        (∫ x, gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
          N lower upper k h F b goodWords x ∂gaussMeasure) *
        ∫ x, gaussFutureDigitBlockIndicator
          (b + gap) times events x ∂gaussMeasure‖ ≤
      (384 * Real.log 2) * (527 / 540 : ℝ) ^ gap := by
  let f : ℝ → ℂ :=
    gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
      N lower upper k h F b goodWords
  let g : ℝ → ℂ :=
    gaussFutureDigitBlockIndicator (b + gap) times events
  have hfM : Measurable f :=
    (measurable_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_prefix
      N lower upper k h F b goodWords).mono
        (gaussPrefixMeasurableSpace_le b) le_rfl
  have hgM : Measurable g :=
    (measurable_gaussFutureDigitBlockIndicator_future
      (b + gap) times hEvents).mono
        (gaussFutureMeasurableSpace_le (b + gap)) le_rfl
  have hfi : Integrable f gaussMeasure := by
    apply Integrable.of_bound hfM.aestronglyMeasurable (2 * Real.log 2)
    exact Eventually.of_forall fun x ↦
      norm_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_le_two_log
        N lower upper k h F b goodWords x
  have hgi : Integrable g gaussMeasure := by
    apply Integrable.of_bound hgM.aestronglyMeasurable 1
    filter_upwards with x
    unfold g gaussFutureDigitBlockIndicator
    by_cases hx : x ∈
        (gaussOrbit (b + gap)) ⁻¹'
          shiftedGaussTailEvent (b + gap) times events
    · rw [Set.indicator_of_mem hx]
      simp
    · rw [Set.indicator_of_notMem hx]
      simp
  have hfIntegral : (∫ x, ‖f x‖ ∂gaussMeasure) ≤
      2 * Real.log 2 := by
    calc
      (∫ x, ‖f x‖ ∂gaussMeasure) ≤
          ∫ _x, 2 * Real.log 2 ∂gaussMeasure := by
        apply integral_mono hfi.norm (integrable_const (2 * Real.log 2))
        intro x
        exact
          norm_gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter_le_two_log
            N lower upper k h F b goodWords x
      _ = 2 * Real.log 2 := by simp
  have hgIntegral : (∫ x, ‖g x‖ ∂gaussMeasure) ≤ 1 := by
    calc
      (∫ x, ‖g x‖ ∂gaussMeasure) ≤
          ∫ _x, (1 : ℝ) ∂gaussMeasure := by
        apply integral_mono hgi.norm (integrable_const 1)
        intro x
        change ‖g x‖ ≤ 1
        unfold g gaussFutureDigitBlockIndicator
        by_cases hx : x ∈
            (gaussOrbit (b + gap)) ⁻¹'
              shiftedGaussTailEvent (b + gap) times events
        · rw [Set.indicator_of_mem hx]
          simp
        · rw [Set.indicator_of_notMem hx]
          simp
      _ = 1 := by simp
  have hraw :=
    (gaussPrefixLebesgueWeightedAffineFrozen_futureDigitBlock_covariance_le
      N lower upper k h F b gap goodWords times hEvents).2
  calc
    ‖(∫ x,
        gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
            N lower upper k h F b goodWords x *
          gaussFutureDigitBlockIndicator (b + gap) times events x
          ∂gaussMeasure) -
        (∫ x, gaussPrefixLebesgueWeightedAffineFrozenCompactCharacter
          N lower upper k h F b goodWords x ∂gaussMeasure) *
        ∫ x, gaussFutureDigitBlockIndicator
          (b + gap) times events x ∂gaussMeasure‖ ≤
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (∫ x, ‖f x‖ ∂gaussMeasure) *
          ∫ x, ‖g x‖ ∂gaussMeasure := by
      simpa only [f, g] using! hraw
    _ ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) *
          (2 * Real.log 2) * 1 := by
      have hcoef : 0 ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) := by
        positivity
      calc
        4 * (48 * (527 / 540 : ℝ) ^ gap) *
              (∫ x, ‖f x‖ ∂gaussMeasure) *
              (∫ x, ‖g x‖ ∂gaussMeasure) ≤
            4 * (48 * (527 / 540 : ℝ) ^ gap) *
              (2 * Real.log 2) *
              (∫ x, ‖g x‖ ∂gaussMeasure) := by
          exact mul_le_mul_of_nonneg_right
            (mul_le_mul_of_nonneg_left hfIntegral hcoef)
            (integral_nonneg fun _x ↦ norm_nonneg _)
        _ ≤ 4 * (48 * (527 / 540 : ℝ) ^ gap) *
              (2 * Real.log 2) * 1 := by
          exact mul_le_mul_of_nonneg_left hgIntegral
            (mul_nonneg hcoef (by positivity))
    _ = (384 * Real.log 2) * (527 / 540 : ℝ) ^ gap := by ring

/-- Polynomially many covariance errors with a linear mixing gap have
vanishing absolute sum.  The tuple type may vary with the horizon. -/
theorem tendsto_norm_sum_of_card_le_natPow_inverseGeometric
    {r c : ℕ} (hc : 0 < c) {theta C : ℝ} (htheta : 1 < theta)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (z : ∀ L : ℕ, (Fin r → Fin L) → ℂ)
    (hbound : ∀ L, ∀ t ∈ tuples L,
      ‖z L t‖ ≤ C * (theta ^ (c * L))⁻¹)
    (hC : 0 ≤ C) :
    Tendsto (fun L : ℕ ↦ ‖∑ t ∈ tuples L, z L t‖)
      atTop (𝓝 0) := by
  have hcard (L : ℕ) : ((tuples L).card : ℝ) ≤ (L : ℝ) ^ r := by
    have hnat := Finset.card_le_univ (tuples L)
    have hnat' : (tuples L).card ≤ L ^ r := by
      simpa only [Fintype.card_fun, Fintype.card_fin] using! hnat
    exact_mod_cast hnat'
  have hthetaPowNonneg (L : ℕ) :
      0 ≤ (theta ^ (c * L))⁻¹ := by positivity
  have hupper (L : ℕ) :
      ‖∑ t ∈ tuples L, z L t‖ ≤
        C * ((L : ℝ) ^ r * (theta ^ (c * L))⁻¹) := by
    calc
      ‖∑ t ∈ tuples L, z L t‖ ≤
          ∑ t ∈ tuples L, ‖z L t‖ := norm_sum_le _ _
      _ ≤ ∑ _t ∈ tuples L, C * (theta ^ (c * L))⁻¹ := by
        exact Finset.sum_le_sum fun t ht ↦ hbound L t ht
      _ = ((tuples L).card : ℝ) *
          (C * (theta ^ (c * L))⁻¹) := by simp
      _ ≤ (L : ℝ) ^ r *
          (C * (theta ^ (c * L))⁻¹) := by
        exact mul_le_mul_of_nonneg_right (hcard L)
          (mul_nonneg hC (hthetaPowNonneg L))
      _ = C * ((L : ℝ) ^ r * (theta ^ (c * L))⁻¹) := by ring
  have hlimit :=
    tendsto_const_mul_natPower_mul_inverse_geometric C r c hc htheta
  exact squeeze_zero' (Eventually.of_forall fun _L ↦ norm_nonneg _)
    (Eventually.of_forall hupper) hlimit

/-- Direct specialization to the explicit Gauss prefix--future mixing
rate.  It is stated with the covariance bound in its natural
`(527/540)^(cL)` form, while the proof exposes the reciprocal geometric
base required by the polynomial-versus-exponential lemma. -/
theorem tendsto_norm_sum_of_card_le_natPow_gaussMixingRate
    {r c : ℕ} (hc : 0 < c)
    (tuples : ∀ L : ℕ, Finset (Fin r → Fin L))
    (z : ∀ L : ℕ, (Fin r → Fin L) → ℂ)
    (hbound : ∀ L, ∀ t ∈ tuples L,
      ‖z L t‖ ≤
        (384 * Real.log 2) * (527 / 540 : ℝ) ^ (c * L)) :
    Tendsto (fun L : ℕ ↦ ‖∑ t ∈ tuples L, z L t‖)
      atTop (nhds 0) := by
  apply tendsto_norm_sum_of_card_le_natPow_inverseGeometric
    hc (theta := (540 / 527 : ℝ)) (C := 384 * Real.log 2)
      (by norm_num) tuples z
  · intro L t ht
    calc
      ‖z L t‖ ≤
          (384 * Real.log 2) * (527 / 540 : ℝ) ^ (c * L) :=
        hbound L t ht
      _ = (384 * Real.log 2) *
          ((540 / 527 : ℝ) ^ (c * L))⁻¹ := by
        congr 1
        rw [← inv_pow]
        congr 1
        norm_num
  · positivity

end

end Erdos1002
