import ErdosProblems.Erdos1002.GaussHeterogeneousMovingScaleLimit
import ErdosProblems.Erdos1002.GaussPrefixLateMeasurability

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Moving-scale signed marked Fourier coefficients

This file separates the two roles which must not be conflated in the
marked factorial argument:

* the base event contains only the exact signed approximation-coordinate
  windows;
* the torus coordinate occurs only through an explicit Fourier character.

Consequently the zero mode is literally the already proved moving-scale
unmarked tuple sum.  A torus-cell indicator will later be inserted by a
finite trigonometric approximation, rather than being hidden inside the
base event at zero frequency.
-/

open Filter MeasureTheory Set
open scoped BigOperators ENNReal Topology

namespace Erdos1002

noncomputable section

local instance gaussMovingSignedMarkedFourierPropDecidable (P : Prop) :
    Decidable P := Classical.propDecidable P

/-! ## Literal selected torus marks -/

/-- The torus coordinate attached to the selected depth-`n` prefix. -/
def gaussSelectedPrefixTorusMark (N n : ℕ) (x : ℝ) : ℝ :=
  (gaussPrefixMarkedPoint N n (selectedGaussPrefixWord n x) x).2.2

/-- Measurability of the selected torus mark, including the measurable
selection of the unique positive prefix word. -/
theorem measurable_gaussSelectedPrefixTorusMark (N n : ℕ) :
    Measurable (gaussSelectedPrefixTorusMark N n) := by
  let : MeasurableSpace (PositiveDigitWord n) := ⊤
  let G : PositiveDigitWord n × ℝ → ℝ := fun z ↦
    (gaussPrefixMarkedPoint N n z.1 z.2).2.2
  have hG : Measurable G := by
    apply measurable_from_prod_countable_right
    intro w
    dsimp only [G]
    exact (measurable_gaussPrefixMarkedPoint N n w).snd.snd
  change Measurable
    (G ∘ fun x : ℝ ↦ (selectedGaussPrefixWord n x, x))
  exact hG.comp
    ((measurable_selectedGaussPrefixWord n).prodMk measurable_id)

private theorem measurable_paperExp_movingMarked : Measurable paperExp := by
  unfold paperExp
  fun_prop

private theorem norm_paperExp_movingMarked (t : ℝ) :
    ‖paperExp t‖ = 1 := by
  rw [paperExp, Complex.norm_exp]
  simp

/-! ## One exact tuple and its character -/

/-- Product character of the selected torus marks at a natural-valued
tuple of depths. -/
def gaussMovingMarkedTupleCharacter
    {r : ℕ} (N : ℕ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) : ℂ :=
  ∏ i, paperExp ((h i : ℝ) *
    gaussSelectedPrefixTorusMark N (times i) x)

theorem measurable_gaussMovingMarkedTupleCharacter
    {r : ℕ} (N : ℕ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) :
    Measurable (gaussMovingMarkedTupleCharacter N h times) := by
  unfold gaussMovingMarkedTupleCharacter
  apply Finset.measurable_fun_prod
  intro i _hi
  exact measurable_paperExp_movingMarked.comp
    (measurable_const.mul
      (measurable_gaussSelectedPrefixTorusMark N (times i)))

theorem norm_gaussMovingMarkedTupleCharacter
    {r : ℕ} (N : ℕ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) :
    ‖gaussMovingMarkedTupleCharacter N h times x‖ = 1 := by
  classical
  unfold gaussMovingMarkedTupleCharacter
  rw [norm_prod]
  exact Finset.prod_eq_one fun i _hi ↦
    norm_paperExp_movingMarked _

@[simp] theorem gaussMovingMarkedTupleCharacter_zero
    {r : ℕ} (N : ℕ) (times : Fin r → ℕ) (x : ℝ) :
    gaussMovingMarkedTupleCharacter N (fun _i ↦ 0) times x = 1 := by
  classical
  unfold gaussMovingMarkedTupleCharacter paperExp
  simp

/-! ## Finite trigonometric polynomials on the real torus model -/

/-- The coordinatewise Fourier character on `(ℝ/ℤ)^r`, evaluated on
real representatives. -/
def realTorusFourierCharacter
    {r : ℕ} (h : Fin r → ℤ) (u : Fin r → ℝ) : ℂ :=
  ∏ i, paperExp ((h i : ℝ) * u i)

/-- A finite trigonometric polynomial represented by its finitely
supported Fourier coefficients. -/
def realTorusTrigPolynomial
    {r : ℕ} (p : (Fin r → ℤ) →₀ ℂ) (u : Fin r → ℝ) : ℂ :=
  p.sum fun h coefficient ↦
    coefficient * realTorusFourierCharacter h u

theorem gaussMovingMarkedTupleCharacter_eq_realTorusFourierCharacter
    {r : ℕ} (N : ℕ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) :
    gaussMovingMarkedTupleCharacter N h times x =
      realTorusFourierCharacter h
        (fun i ↦ gaussSelectedPrefixTorusMark N (times i) x) := by
  rfl

/-- Exact signed value-window indicator multiplied by the independent
torus Fourier character. -/
def gaussMovingSignedMarkedTupleIntegrand
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) : ℂ :=
  (gaussSignedApproximationTupleEvent scale lower upper times).indicator
    (gaussMovingMarkedTupleCharacter N h times) x

theorem measurable_gaussMovingSignedMarkedTupleIntegrand
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) :
    Measurable
      (gaussMovingSignedMarkedTupleIntegrand
        N scale lower upper h times) := by
  exact (measurable_gaussMovingMarkedTupleCharacter N h times).indicator
    (measurableSet_gaussSignedApproximationTupleEvent
      scale lower upper times)

theorem norm_gaussMovingSignedMarkedTupleIntegrand
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (x : ℝ) :
    ‖gaussMovingSignedMarkedTupleIntegrand
        N scale lower upper h times x‖ =
      (gaussSignedApproximationTupleEvent scale lower upper times).indicator
        (fun _x ↦ (1 : ℝ)) x := by
  unfold gaussMovingSignedMarkedTupleIntegrand
  by_cases hx : x ∈
      gaussSignedApproximationTupleEvent scale lower upper times
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      norm_gaussMovingMarkedTupleCharacter]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      norm_zero]

theorem integrable_gaussMovingSignedMarkedTupleIntegrand
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (times : Fin r → ℕ) (mu : Measure ℝ) [IsFiniteMeasure mu] :
    Integrable
      (gaussMovingSignedMarkedTupleIntegrand
        N scale lower upper h times) mu := by
  apply Integrable.of_bound
    (measurable_gaussMovingSignedMarkedTupleIntegrand
      N scale lower upper h times).aestronglyMeasurable 1
  filter_upwards with x
  rw [norm_gaussMovingSignedMarkedTupleIntegrand]
  unfold Set.indicator
  split <;> norm_num

@[simp] theorem gaussMovingSignedMarkedTupleIntegrand_zero
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (times : Fin r → ℕ) (x : ℝ) :
    gaussMovingSignedMarkedTupleIntegrand
        N scale lower upper (fun _i ↦ 0) times x =
      (gaussSignedApproximationTupleEvent scale lower upper times).indicator
        (fun _x ↦ (1 : ℂ)) x := by
  unfold gaussMovingSignedMarkedTupleIntegrand
  by_cases hx : x ∈
      gaussSignedApproximationTupleEvent scale lower upper times
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      gaussMovingMarkedTupleCharacter_zero]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]

/-! ## Finite tuple-family coefficients under either measure -/

/-- Marked Fourier coefficient summed over an arbitrary finite family of
natural-valued tuples. -/
def movingSignedMarkedFourierTupleSum
    {r : ℕ} (mu : Measure ℝ) (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) : ℂ :=
  ∑ times ∈ tuples,
    ∫ x, gaussMovingSignedMarkedTupleIntegrand
      N scale lower upper h times x ∂mu

/-- The same finite-family statistic tested against one finite
trigonometric polynomial in all torus coordinates. -/
def movingSignedMarkedTrigTupleSum
    {r : ℕ} (mu : Measure ℝ) (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (tuples : Finset (Fin r → ℕ)) : ℂ :=
  ∑ times ∈ tuples,
    ∫ x,
      (gaussSignedApproximationTupleEvent
        scale lower upper times).indicator
          (fun y ↦ realTorusTrigPolynomial p
            (fun i ↦ gaussSelectedPrefixTorusMark
              N (times i) y)) x ∂mu

/-- Pointwise finite Fourier expansion of the polynomial-tested tuple
integrand. -/
theorem indicator_realTorusTrigPolynomial_eq_sum_markedIntegrands
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (times : Fin r → ℕ) (x : ℝ) :
    (gaussSignedApproximationTupleEvent
        scale lower upper times).indicator
          (fun y ↦ realTorusTrigPolynomial p
            (fun i ↦ gaussSelectedPrefixTorusMark
              N (times i) y)) x =
      ∑ mode ∈ p.support,
        p mode * gaussMovingSignedMarkedTupleIntegrand
          N scale lower upper mode times x := by
  classical
  by_cases hx : x ∈
      gaussSignedApproximationTupleEvent scale lower upper times
  · rw [Set.indicator_of_mem hx]
    simp_rw [gaussMovingSignedMarkedTupleIntegrand,
      Set.indicator_of_mem hx]
    unfold realTorusTrigPolynomial Finsupp.sum
    apply Finset.sum_congr rfl
    intro mode _hmode
    rw [gaussMovingMarkedTupleCharacter_eq_realTorusFourierCharacter]
  · rw [Set.indicator_of_notMem hx]
    simp only [gaussMovingSignedMarkedTupleIntegrand,
      Set.indicator_of_notMem hx, mul_zero, Finset.sum_const_zero]

/-- A finite trigonometric test is exactly the corresponding finite
linear combination of the literal Fourier coefficients. -/
theorem movingSignedMarkedTrigTupleSum_eq_fourierSum
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ) (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (tuples : Finset (Fin r → ℕ)) :
    movingSignedMarkedTrigTupleSum
        mu N scale lower upper p tuples =
      ∑ mode ∈ p.support,
        p mode * movingSignedMarkedFourierTupleSum
          mu N scale lower upper mode tuples := by
  classical
  unfold movingSignedMarkedTrigTupleSum
    movingSignedMarkedFourierTupleSum
  calc
    (∑ times ∈ tuples,
        ∫ x,
          (gaussSignedApproximationTupleEvent
              scale lower upper times).indicator
            (fun y ↦ realTorusTrigPolynomial p
              (fun i ↦ gaussSelectedPrefixTorusMark
                N (times i) y)) x ∂mu) =
        ∑ times ∈ tuples,
          ∑ mode ∈ p.support,
            p mode *
              ∫ x, gaussMovingSignedMarkedTupleIntegrand
                N scale lower upper mode times x ∂mu := by
      apply Finset.sum_congr rfl
      intro times _htimes
      rw [show (fun x ↦
          (gaussSignedApproximationTupleEvent
              scale lower upper times).indicator
            (fun y ↦ realTorusTrigPolynomial p
              (fun i ↦ gaussSelectedPrefixTorusMark
                N (times i) y)) x) =
          fun x ↦ ∑ mode ∈ p.support,
            p mode * gaussMovingSignedMarkedTupleIntegrand
              N scale lower upper mode times x by
        funext x
        exact
          indicator_realTorusTrigPolynomial_eq_sum_markedIntegrands
            N scale lower upper p times x]
      rw [MeasureTheory.integral_finset_sum]
      · apply Finset.sum_congr rfl
        intro mode _hmode
        exact integral_const_mul
          (p mode)
          (gaussMovingSignedMarkedTupleIntegrand
            N scale lower upper mode times)
      · intro mode _hmode
        exact (integrable_gaussMovingSignedMarkedTupleIntegrand
          N scale lower upper mode times mu).const_mul _
    _ = ∑ mode ∈ p.support,
        p mode *
          ∑ times ∈ tuples,
            ∫ x, gaussMovingSignedMarkedTupleIntegrand
              N scale lower upper mode times x ∂mu := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro mode _hmode
      rw [Finset.mul_sum]

/-- The corresponding unmarked finite-family mass under an arbitrary
finite measure. -/
def movingSignedApproximationTupleMassSum
    {r : ℕ} (mu : Measure ℝ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) : ℝ :=
  ∑ times ∈ tuples,
    mu.real (gaussSignedApproximationTupleEvent scale lower upper times)

/-- At zero torus frequency, the coefficient is literally the
complexification of the unmarked mass sum. -/
theorem movingSignedMarkedFourierTupleSum_zero
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    movingSignedMarkedFourierTupleSum mu N scale lower upper
        (fun _i ↦ 0) tuples =
      (movingSignedApproximationTupleMassSum
        mu scale lower upper tuples : ℂ) := by
  classical
  unfold movingSignedMarkedFourierTupleSum
    movingSignedApproximationTupleMassSum
  calc
    (∑ times ∈ tuples,
        ∫ x, gaussMovingSignedMarkedTupleIntegrand
          N scale lower upper (fun _i ↦ 0) times x ∂mu) =
        ∑ times ∈ tuples,
          (mu.real
            (gaussSignedApproximationTupleEvent
              scale lower upper times) : ℂ) := by
      apply Finset.sum_congr rfl
      intro times _htimes
      rw [show gaussMovingSignedMarkedTupleIntegrand
          N scale lower upper (fun _i ↦ 0) times =
          (gaussSignedApproximationTupleEvent
            scale lower upper times).indicator
              (fun _x ↦ (1 : ℂ)) by
        funext x
        exact gaussMovingSignedMarkedTupleIntegrand_zero
          N scale lower upper times x]
      rw [MeasureTheory.integral_indicator_const (1 : ℂ)
        (measurableSet_gaussSignedApproximationTupleEvent
          scale lower upper times)]
      simp
    _ = ((∑ times ∈ tuples,
          mu.real (gaussSignedApproximationTupleEvent
            scale lower upper times) : ℝ) : ℂ) := by
      rw [Complex.ofReal_sum]

/-- The modulus of every finite marked coefficient is bounded by its
unmarked mass.  This is the uniform boundedness input for extending
mode convergence from trigonometric polynomials to continuous torus
tests. -/
theorem norm_movingSignedMarkedFourierTupleSum_le_mass
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) :
    ‖movingSignedMarkedFourierTupleSum
        mu N scale lower upper h tuples‖ ≤
      movingSignedApproximationTupleMassSum
        mu scale lower upper tuples := by
  classical
  unfold movingSignedMarkedFourierTupleSum
    movingSignedApproximationTupleMassSum
  calc
    ‖∑ times ∈ tuples,
        ∫ x, gaussMovingSignedMarkedTupleIntegrand
          N scale lower upper h times x ∂mu‖ ≤
        ∑ times ∈ tuples,
          ‖∫ x, gaussMovingSignedMarkedTupleIntegrand
            N scale lower upper h times x ∂mu‖ := norm_sum_le _ _
    _ ≤ ∑ times ∈ tuples,
        mu.real (gaussSignedApproximationTupleEvent
          scale lower upper times) := by
      apply Finset.sum_le_sum
      intro times _htimes
      calc
        ‖∫ x, gaussMovingSignedMarkedTupleIntegrand
            N scale lower upper h times x ∂mu‖ ≤
            ∫ x, ‖gaussMovingSignedMarkedTupleIntegrand
              N scale lower upper h times x‖ ∂mu :=
          norm_integral_le_integral_norm _
        _ = ∫ x,
            (gaussSignedApproximationTupleEvent
              scale lower upper times).indicator
                (fun _x ↦ (1 : ℝ)) x ∂mu := by
          apply integral_congr_ae
          filter_upwards with x
          exact norm_gaussMovingSignedMarkedTupleIntegrand
            N scale lower upper h times x
        _ = mu.real (gaussSignedApproximationTupleEvent
              scale lower upper times) := by
          rw [MeasureTheory.integral_indicator_const (1 : ℝ)
            (measurableSet_gaussSignedApproximationTupleEvent
              scale lower upper times)]
          simp

/-- Convergence of every Fourier coefficient on the finite support of a
trigonometric polynomial implies convergence of the polynomial-tested
factorial statistic. -/
theorem tendsto_movingSignedMarkedTrigTupleSum_of_fourier
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (limit : (Fin r → ℤ) → ℂ)
    (hmode : ∀ mode ∈ p.support,
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds (limit mode))) :
    Tendsto
      (fun n ↦ movingSignedMarkedTrigTupleSum
        mu (N n) (scale n) lower upper p (tuples n))
      atTop
      (nhds (p.sum fun mode coefficient ↦
        coefficient * limit mode)) := by
  have hsum := tendsto_finset_sum p.support fun mode hmodeSupport ↦
    (hmode mode hmodeSupport).const_mul (p mode)
  apply hsum.congr'
  filter_upwards with n
  exact
    (movingSignedMarkedTrigTupleSum_eq_fourierSum
      mu (N n) (scale n) lower upper p (tuples n)).symm

/-- Paper-facing specialization: the zero mode tends to the unmarked mass
and every supported nonzero mode vanishes.  Therefore a finite
trigonometric polynomial retains only its constant Fourier coefficient. -/
theorem tendsto_movingSignedMarkedTrigTupleSum_of_zero_and_nonzero
    {r : ℕ} (mu : Measure ℝ) [IsFiniteMeasure mu]
    (N : ℕ → ℕ) (scale : ℕ → ℝ)
    (lower upper : Fin r → ℝ)
    (p : (Fin r → ℤ) →₀ ℂ)
    (tuples : ℕ → Finset (Fin r → ℕ))
    (massLimit : ℝ)
    (hzero : Tendsto
      (fun n ↦ movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n))
      atTop (nhds massLimit))
    (hnonzero : ∀ mode ∈ p.support, mode ≠ 0 →
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds 0)) :
    Tendsto
      (fun n ↦ movingSignedMarkedTrigTupleSum
        mu (N n) (scale n) lower upper p (tuples n))
      atTop (nhds (p 0 * (massLimit : ℂ))) := by
  let modeLimit : (Fin r → ℤ) → ℂ := fun mode ↦
    if mode = 0 then (massLimit : ℂ) else 0
  have hzeroComplex : Tendsto
      (fun n ↦ (movingSignedApproximationTupleMassSum
        mu (scale n) lower upper (tuples n) : ℂ))
      atTop (nhds (massLimit : ℂ)) :=
    Complex.continuous_ofReal.continuousAt.tendsto.comp hzero
  have hmode : ∀ mode ∈ p.support,
      Tendsto
        (fun n ↦ movingSignedMarkedFourierTupleSum
          mu (N n) (scale n) lower upper mode (tuples n))
        atTop (nhds (modeLimit mode)) := by
    intro mode hmodeSupport
    by_cases hm : mode = 0
    · subst mode
      rw [show modeLimit 0 = (massLimit : ℂ) by simp [modeLimit]]
      apply hzeroComplex.congr'
      filter_upwards with n
      exact (movingSignedMarkedFourierTupleSum_zero
        mu (N n) (scale n) lower upper (tuples n)).symm
    · simpa only [modeLimit, if_neg hm] using!
        hnonzero mode hmodeSupport hm
  have htrig := tendsto_movingSignedMarkedTrigTupleSum_of_fourier
    mu N scale lower upper p tuples modeLimit hmode
  have hlimitEq :
      p.sum (fun mode coefficient ↦ coefficient * modeLimit mode) =
        p 0 * (massLimit : ℂ) := by
    classical
    unfold Finsupp.sum
    by_cases hp : 0 ∈ p.support
    · rw [Finset.sum_eq_single 0]
      · simp [modeLimit]
      · intro mode hmodeSupport hmodeNe
        simp [modeLimit, hmodeNe]
      · intro hnot
        exact (hnot hp).elim
    · have hp0 : p 0 = 0 := by
        simpa only [Finsupp.mem_support_iff, not_ne_iff] using! hp
      calc
        ∑ mode ∈ p.support,
            p mode * modeLimit mode = 0 := by
          apply Finset.sum_eq_zero
          intro mode hmodeSupport
          have hmodeNe : mode ≠ 0 := by
            intro hzeroMode
            subst mode
            exact hp hmodeSupport
          simp [modeLimit, hmodeNe]
        _ = p 0 * (massLimit : ℂ) := by simp [hp0]
  rw [hlimitEq] at htrig
  exact htrig

/-! ## Gauss and Lebesgue specializations -/

def gaussMovingSignedMarkedFourierTupleSum
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) : ℂ :=
  movingSignedMarkedFourierTupleSum
    gaussMeasure N scale lower upper h tuples

def uniformMovingSignedMarkedFourierTupleSum
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) : ℂ :=
  movingSignedMarkedFourierTupleSum
    uniform01Measure N scale lower upper h tuples

@[simp] theorem gaussMovingSignedMarkedFourierTupleSum_zero
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ)
    (tuples : Finset (Fin r → ℕ)) :
    gaussMovingSignedMarkedFourierTupleSum N scale lower upper
        (fun _i ↦ 0) tuples =
      (gaussMovingSignedApproximationTupleSum
        scale lower upper tuples : ℂ) := by
  rw [gaussMovingSignedMarkedFourierTupleSum,
    movingSignedMarkedFourierTupleSum_zero]
  rfl

/-- Exact weighted-Gauss representation of the uniform coefficient. -/
theorem uniformMovingSignedMarkedFourierTupleSum_eq_weightedGauss
    {r : ℕ} (N : ℕ) (scale : ℝ)
    (lower upper : Fin r → ℝ) (h : Fin r → ℤ)
    (tuples : Finset (Fin r → ℕ)) :
    uniformMovingSignedMarkedFourierTupleSum
        N scale lower upper h tuples =
      ∑ times ∈ tuples,
        ∫ x, (gaussLebesguePrefixWeight x : ℂ) *
          gaussMovingSignedMarkedTupleIntegrand
            N scale lower upper h times x ∂gaussMeasure := by
  classical
  unfold uniformMovingSignedMarkedFourierTupleSum
    movingSignedMarkedFourierTupleSum
  apply Finset.sum_congr rfl
  intro times _htimes
  exact integral_uniform01_eq_integral_gaussLebesguePrefixWeight_mul
    (gaussMovingSignedMarkedTupleIntegrand
      N scale lower upper h times)

end

end Erdos1002
