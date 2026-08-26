import ErdosProblems.Erdos1002.FixedAwayShiftedDyadic

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Uniform constants for compact fixed-away threshold families

The fixed-away proof eventually takes a supremum over
`t ∈ [ε₀, ε₁]`.  This file supplies the missing quantitative statement:
the `L¹` norms of every fixed derivative of the compact correction have
one explicit bound depending on the upper endpoint and the smoothing width,
but not on the moving threshold.
-/

open Filter MeasureTheory Set
open scoped BigOperators ComplexConjugate Real Topology

namespace Erdos1002

noncomputable section

/-- Complexification commutes with every real iterated derivative. -/
theorem iteratedDeriv_realCutoffComplex_eq
    (κ : ℝ → ℝ) (hκ : ContDiff ℝ (⊤ : ℕ∞) κ) (n : ℕ) :
    iteratedDeriv (𝕜 := ℝ) n (realCutoffComplex κ) =
      fun x : ℝ ↦ ((iteratedDeriv (𝕜 := ℝ) n κ x : ℝ) : ℂ) := by
  induction n with
  | zero =>
      rfl
  | succ n ih =>
      rw [show n + 1 = Nat.succ n by omega,
        iteratedDeriv_succ, iteratedDeriv_succ, ih]
      funext x
      have hd : DifferentiableAt ℝ
          (iteratedDeriv (𝕜 := ℝ) n κ : ℝ → ℝ) x :=
        (hκ.differentiable_iteratedDeriv n
          (WithTop.coe_lt_coe.mpr (ENat.coe_lt_top n))).differentiableAt
      exact hd.hasDerivAt.ofReal_comp.deriv

/-- Every iterated derivative of the smooth correction is supported in
the same closed interval as the correction itself. -/
theorem support_iteratedDeriv_fixedAwaySmoothCorrection_subset
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (n : ℕ) :
    Function.support (iteratedDeriv n (fixedAwaySmoothCorrection t δ)) ⊆
      Icc (-t) t := by
  let U : Set ℝ := Iio (-t) ∪ Ioi t
  have hUopen : IsOpen U := isOpen_Iio.union isOpen_Ioi
  have heq : Set.EqOn (fixedAwaySmoothCorrection t δ)
      (fun _x : ℝ ↦ 0) U := by
    intro x hx
    have hout : t ≤ |x| := by
      rcases hx with hx | hx
      · have hxt : x < -t := hx
        have hxnonpos : x ≤ 0 := by linarith [hδ.le.trans hδt]
        rw [abs_of_nonpos hxnonpos]
        linarith
      · have htx : t < x := hx
        have hxnonneg : 0 ≤ x := by linarith [hδ.le.trans hδt]
        rw [abs_of_nonneg hxnonneg]
        exact htx.le
    simp [fixedAwaySmoothCorrection_eq_zero_of_le_abs hδ hδt hout]
  have hderivEq := heq.iteratedDeriv_of_isOpen hUopen n
  intro x hx
  by_contra hnot
  have hxU : x ∈ U := by
    simp only [U, mem_union, mem_Iio, mem_Ioi]
    simp only [mem_Icc, not_and_or, not_le] at hnot
    exact hnot
  have hzero : iteratedDeriv n (fixedAwaySmoothCorrection t δ) x = 0 := by
    calc
      iteratedDeriv n (fixedAwaySmoothCorrection t δ) x =
          iteratedDeriv n (fun _x : ℝ ↦ 0) x := hderivEq hxU
      _ = 0 := by simp [iteratedDeriv_const]
  exact hx hzero

/-- A slightly enlarged open interval contains the support.  The unit
enlargement avoids hiding an endpoint argument when the full integral is
replaced by an interval integral. -/
theorem support_iteratedDeriv_realFixedAwayCorrection_subset
    {t δ : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t) (n : ℕ) :
    Function.support
        (iteratedDeriv n
          (realCutoffComplex (fixedAwaySmoothCorrection t δ))) ⊆
      Ioc (-t - 1) (t + 1) := by
  rw [iteratedDeriv_realCutoffComplex_eq _
    (fixedAwaySmoothCorrection_contDiff t δ) n]
  intro x hx
  have hxReal : x ∈ Function.support
      (iteratedDeriv n (fixedAwaySmoothCorrection t δ)) := by
    intro hzero
    apply hx
    simp [hzero]
  have hclosed :=
    support_iteratedDeriv_fixedAwaySmoothCorrection_subset hδ hδt n hxReal
  exact ⟨by linarith [hclosed.1], by linarith [hclosed.2]⟩

/-- Explicit common upper bound for the `n`-th correction derivative on
all thresholds `0 < t ≤ T`. -/
def fixedAwayCorrectionDerivL1UniformBound
    (T δ : ℝ) : ℕ → ℝ
  | 0 => (2 * T + 2)
  | n + 1 =>
      (2 * T + 2) *
        (2 * |δ⁻¹| ^ (n + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ n * (n.factorial : ℝ) ^ 2)))

theorem fixedAwayCorrectionDerivL1UniformBound_nonneg
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ) (n : ℕ) :
    0 ≤ fixedAwayCorrectionDerivL1UniformBound T δ n := by
  cases n with
  | zero =>
      unfold fixedAwayCorrectionDerivL1UniformBound
      linarith
  | succ n =>
      unfold fixedAwayCorrectionDerivL1UniformBound
      have hmass : 0 ≤ gevreyCompactBumpMass⁻¹ :=
        inv_nonneg.mpr gevreyCompactBumpMass_pos.le
      exact mul_nonneg (by linarith)
        (mul_nonneg
          (mul_nonneg (by norm_num) (by positivity))
          (mul_nonneg hmass (mul_nonneg (by positivity) (sq_nonneg _))))

theorem fixedAwayCorrectionDerivL1_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (n : ℕ) :
    fixedAwayCorrectionDerivL1 (fixedAwaySmoothCorrection t δ) n ≤
      fixedAwayCorrectionDerivL1UniformBound T δ n := by
  have ht0 : 0 ≤ t := hδ.le.trans hδt
  have hT0 : 0 ≤ T := ht0.trans htT
  let f : ℝ → ℝ := fun x ↦
    ‖iteratedDeriv n
      (realCutoffComplex (fixedAwaySmoothCorrection t δ)) x‖
  have hsupport : Function.support f ⊆ Ioc (-t - 1) (t + 1) := by
    intro x hx
    apply support_iteratedDeriv_realFixedAwayCorrection_subset hδ hδt n
    intro hzero
    exact hx (by simp [f, hzero])
  have hfull : (∫ x : ℝ, f x) = ∫ x in (-t - 1)..(t + 1), f x := by
    exact (intervalIntegral.integral_eq_integral_of_support_subset
      hsupport).symm
  have hnonneg : 0 ≤ ∫ x in (-t - 1)..(t + 1), f x := by
    exact intervalIntegral.integral_nonneg (by linarith)
      (fun x _hx ↦ norm_nonneg _)
  cases n with
  | zero =>
      let C : ℝ := 1
      have hpoint : ∀ x ∈ Set.uIoc (-t - 1) (t + 1), ‖f x‖ ≤ C := by
        intro x hx
        dsimp only [f, C]
        simp only [iteratedDeriv_zero, realCutoffComplex,
          Complex.norm_real, Real.norm_eq_abs, abs_abs]
        exact abs_fixedAwaySmoothCorrection_le_one hδ hδt x
      have hinterval :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      unfold fixedAwayCorrectionDerivL1
      rw [hfull]
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hinterval
      unfold fixedAwayCorrectionDerivL1UniformBound
      dsimp only [C] at hinterval
      have hlength : |(t + 1) - (-t - 1)| = 2 * t + 2 := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [hlength] at hinterval
      linarith
  | succ k =>
      let C : ℝ :=
        2 * |δ⁻¹| ^ (k + 1) *
          (gevreyCompactBumpMass⁻¹ *
            (96 ^ k * (k.factorial : ℝ) ^ 2))
      have hpoint : ∀ x ∈ Set.uIoc (-t - 1) (t + 1), ‖f x‖ ≤ C := by
        intro x hx
        dsimp only [f, C]
        rw [iteratedDeriv_realCutoffComplex_eq _
          (fixedAwaySmoothCorrection_contDiff t δ) (k + 1)]
        simpa only [Complex.norm_real, Real.norm_eq_abs, abs_abs] using!
          abs_iteratedDeriv_fixedAwaySmoothCorrection_succ_le k t δ x
      have hinterval :=
        intervalIntegral.norm_integral_le_of_norm_le_const hpoint
      unfold fixedAwayCorrectionDerivL1
      rw [hfull]
      rw [Real.norm_eq_abs, abs_of_nonneg hnonneg] at hinterval
      unfold fixedAwayCorrectionDerivL1UniformBound
      dsimp only [C] at hinterval
      have hlength : |(t + 1) - (-t - 1)| = 2 * t + 2 := by
        rw [abs_of_nonneg (by linarith)]
        ring
      rw [hlength] at hinterval
      have hmass : 0 ≤ gevreyCompactBumpMass⁻¹ :=
        inv_nonneg.mpr gevreyCompactBumpMass_pos.le
      have hC : 0 ≤ C := by
        dsimp only [C]
        exact mul_nonneg
          (mul_nonneg (by norm_num) (by positivity))
          (mul_nonneg hmass (mul_nonneg (by positivity) (sq_nonneg _)))
      change (∫ x in -t - 1..t + 1, f x) ≤ (2 * T + 2) * C
      calc
        (∫ x in -t - 1..t + 1, f x) ≤ (2 * t + 2) * C := by
          simpa [C, mul_comm, mul_left_comm, mul_assoc] using! hinterval
        _ ≤ (2 * T + 2) * C :=
          mul_le_mul_of_nonneg_right (by linarith) hC

/-! ## Propagation to every constant used by the dyadic argument -/

/-- Common local PV bound for `0 ≤ t ≤ T`. -/
def fixedAwayPVLocalUniformBound (T : ℝ) : ℝ :=
  Real.pi + 4 * Real.pi * T

/-- Common Fourier-derivative bound for `0 < δ ≤ t ≤ T`. -/
def fixedAwayDerivativeUniformBound (T δ : ℝ) (n : ℕ) : ℝ :=
  (2 * Real.pi) * fixedAwayCorrectionDerivL1UniformBound T δ n

theorem fixedAwayPVLocalUniformBound_nonneg
    {T : ℝ} (hT : 0 ≤ T) :
    0 ≤ fixedAwayPVLocalUniformBound T := by
  unfold fixedAwayPVLocalUniformBound
  positivity

theorem fixedAwayDerivativeUniformBound_nonneg
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ) (n : ℕ) :
    0 ≤ fixedAwayDerivativeUniformBound T δ n := by
  unfold fixedAwayDerivativeUniformBound
  exact mul_nonneg (by positivity)
    (fixedAwayCorrectionDerivL1UniformBound_nonneg hT δ n)

theorem fixedAwayPVLocalBound_le_uniform
    {t T : ℝ} (ht : 0 ≤ t) (htT : t ≤ T) :
    fixedAwayPVLocalBound t ≤ fixedAwayPVLocalUniformBound T := by
  unfold fixedAwayPVLocalBound fixedAwayPVLocalUniformBound
  rw [abs_of_nonneg ht]
  gcongr

theorem fixedAwayDerivativeBound_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (n : ℕ) :
    fixedAwayDerivativeBound t δ n ≤
      fixedAwayDerivativeUniformBound T δ n := by
  unfold fixedAwayDerivativeBound fixedAwayDerivativeUniformBound
  exact mul_le_mul_of_nonneg_left
    (fixedAwayCorrectionDerivL1_le_uniform hδ hδt htT n) (by positivity)

/-- Uniform arbitrary-order PV envelope. -/
def fixedAwayPVRapidDecayUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J *
    (fixedAwayPVLocalUniformBound T +
      fixedAwayDerivativeUniformBound T δ (J + 1) /
        ((J : ℝ) * (2 * Real.pi) ^ (J + 1)))

theorem fixedAwayPVRapidDecayUniformConstant_nonneg
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayPVRapidDecayUniformConstant T δ J := by
  unfold fixedAwayPVRapidDecayUniformConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (fixedAwayPVLocalUniformBound_nonneg hT)
    (div_nonneg (fixedAwayDerivativeUniformBound_nonneg hT δ (J + 1))
      (mul_nonneg (Nat.cast_nonneg J) (by positivity))))

/-- The rapid constant is nonnegative also at order zero (where Lean's
division convention makes the second summand zero).  Keeping this endpoint
explicit prevents later monotonicity proofs from silently assuming `J > 0`. -/
theorem fixedAwayPVRapidDecayConstant_nonneg_all
    (t δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayPVRapidDecayConstant t δ J := by
  unfold fixedAwayPVRapidDecayConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (fixedAwayPVLocalBound_nonneg t)
    (div_nonneg (fixedAwayDerivativeBound_nonneg t δ (J + 1))
      (mul_nonneg (Nat.cast_nonneg J) (by positivity))))

theorem fixedAwayPVRapidDecayConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayPVRapidDecayConstant t δ J ≤
      fixedAwayPVRapidDecayUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  unfold fixedAwayPVRapidDecayConstant
    fixedAwayPVRapidDecayUniformConstant
  gcongr
  · exact fixedAwayPVLocalBound_le_uniform ht htT
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT (J + 1)

/-- Uniform arbitrary-order derivative envelope. -/
def fixedAwayDerivativeRapidDecayUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  (2 : ℝ) ^ J *
    (fixedAwayDerivativeUniformBound T δ 0 +
      fixedAwayDerivativeUniformBound T δ J /
        (2 * Real.pi) ^ J)

theorem fixedAwayDerivativeRapidDecayUniformConstant_nonneg
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ) (J : ℕ) :
    0 ≤ fixedAwayDerivativeRapidDecayUniformConstant T δ J := by
  unfold fixedAwayDerivativeRapidDecayUniformConstant
  exact mul_nonneg (by positivity) (add_nonneg
    (fixedAwayDerivativeUniformBound_nonneg hT δ 0)
    (div_nonneg (fixedAwayDerivativeUniformBound_nonneg hT δ J)
      (by positivity)))

theorem fixedAwayDerivativeRapidDecayConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayDerivativeRapidDecayConstant t δ J ≤
      fixedAwayDerivativeRapidDecayUniformConstant T δ J := by
  unfold fixedAwayDerivativeRapidDecayConstant
    fixedAwayDerivativeRapidDecayUniformConstant fixedAwayDerivativeBound0
  gcongr
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 0
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT J

/-- Uniform quadratic PV envelope used in the unprojected diagonal. -/
def fixedAwayPVQuadraticDecayUniformConstant (T δ : ℝ) : ℝ :=
  4 * (fixedAwayPVLocalUniformBound T +
    fixedAwayDerivativeUniformBound T δ 3 /
      (2 * (2 * Real.pi) ^ 3))

theorem fixedAwayPVQuadraticDecayUniformConstant_nonneg
    {T : ℝ} (hT : 0 ≤ T) (δ : ℝ) :
    0 ≤ fixedAwayPVQuadraticDecayUniformConstant T δ := by
  unfold fixedAwayPVQuadraticDecayUniformConstant
  exact mul_nonneg (by norm_num) (add_nonneg
    (fixedAwayPVLocalUniformBound_nonneg hT)
    (div_nonneg (fixedAwayDerivativeUniformBound_nonneg hT δ 3)
      (by positivity)))

theorem fixedAwayPVQuadraticDecayConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) :
    fixedAwayPVQuadraticDecayConstant t δ ≤
      fixedAwayPVQuadraticDecayUniformConstant T δ := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  unfold fixedAwayPVQuadraticDecayConstant
    fixedAwayPVQuadraticDecayUniformConstant
  gcongr
  · exact fixedAwayPVLocalBound_le_uniform ht htT
  · exact fixedAwayDerivativeBound_le_uniform hδ hδt htT 3

/-- Uniform version of the unprojected Hermitian variation constant. -/
def fixedAwayHermitianRapidVariationUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  5 * 8 ^ J *
      fixedAwayDerivativeRapidDecayUniformConstant T δ (J + 2) *
      fixedAwayPVRapidDecayUniformConstant T δ (J + 2) *
      fixedAwayRapidEnvelopeTwoMass * (1 + 8 ^ J) +
    4 * Real.pi * fixedAwayPVRapidDecayUniformConstant T δ J *
      (1 + 8 ^ J) +
    4 * Real.pi ^ 2

theorem fixedAwayHermitianRapidVariationConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayHermitianRapidVariationConstant t δ J ≤
      fixedAwayHermitianRapidVariationUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hDle := fixedAwayDerivativeRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hCle := fixedAwayPVRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hCJle := fixedAwayPVRapidDecayConstant_le_uniform hδ hδt htT J
  have hD0 := fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2)
  have hDu := fixedAwayDerivativeRapidDecayUniformConstant_nonneg hT δ (J + 2)
  have hC0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ (J + 2)
  have hCu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ (J + 2)
  have hCJ0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ J
  have hCJu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ J
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  unfold fixedAwayHermitianRapidVariationConstant
    fixedAwayHermitianRapidVariationUniformConstant
  gcongr

/-- Uniform version of the unprojected BV--Abel constant. -/
def fixedAwayHermitianRapidBVUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  2 * fixedAwayPVRapidDecayUniformConstant T δ (J + 2) ^ 2 * 8 ^ J +
    fixedAwayHermitianRapidVariationUniformConstant T δ J

theorem fixedAwayHermitianRapidBVConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayHermitianRapidBVConstant t δ J ≤
      fixedAwayHermitianRapidBVUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hCle := fixedAwayPVRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hVle := fixedAwayHermitianRapidVariationConstant_le_uniform
    hδ hδt htT J
  have hC0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ (J + 2)
  have hCu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ (J + 2)
  unfold fixedAwayHermitianRapidBVConstant
    fixedAwayHermitianRapidBVUniformConstant
  gcongr

/-- Uniform version of the projected variation constant, including both
projection endpoint jumps. -/
def fixedAwayProjectedRapidVariationUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  2 * (fixedAwayDerivativeRapidDecayUniformConstant T δ (J + 2) *
      fixedAwayPVRapidDecayUniformConstant T δ (J + 2)) *
      fixedAwayRapidEnvelopeTwoMass +
    2 * fixedAwayPVRapidDecayUniformConstant T δ J ^ 2

theorem fixedAwayProjectedRapidVariationConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayProjectedRapidVariationConstant t δ J ≤
      fixedAwayProjectedRapidVariationUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hDle := fixedAwayDerivativeRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hCle := fixedAwayPVRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hCJle := fixedAwayPVRapidDecayConstant_le_uniform hδ hδt htT J
  have hD0 := fixedAwayDerivativeRapidDecayConstant_nonneg t δ (J + 2)
  have hDu := fixedAwayDerivativeRapidDecayUniformConstant_nonneg hT δ (J + 2)
  have hC0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ (J + 2)
  have hCu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ (J + 2)
  have hCJ0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ J
  have hCJu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ J
  have hmass := fixedAwayRapidEnvelopeTwoMass_nonneg
  unfold fixedAwayProjectedRapidVariationConstant
    fixedAwayProjectedRapidVariationUniformConstant
  gcongr

/-- Uniform version of the projected BV--Abel constant. -/
def fixedAwayProjectedRapidBVUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  fixedAwayPVRapidDecayUniformConstant T δ J ^ 2 +
    fixedAwayProjectedRapidVariationUniformConstant T δ J

theorem fixedAwayProjectedRapidBVConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayProjectedRapidBVConstant t δ J ≤
      fixedAwayProjectedRapidBVUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hCle := fixedAwayPVRapidDecayConstant_le_uniform hδ hδt htT J
  have hVle := fixedAwayProjectedRapidVariationConstant_le_uniform
    hδ hδt htT J
  have hC0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ J
  have hCu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ J
  unfold fixedAwayProjectedRapidBVConstant
    fixedAwayProjectedRapidBVUniformConstant
  gcongr

/-- Common diagonal energy for the unprojected shifted multiplier. -/
def fixedAwayShiftedDiagonalUniformConstant (T δ : ℝ) : ℝ :=
  16 * fixedAwayPVQuadraticDecayUniformConstant T δ ^ 2 *
    fixedAwayIntegerQuadraticEnvelopeMass

theorem fixedAwayShiftedDiagonalConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) :
    fixedAwayShiftedDiagonalConstant t δ ≤
      fixedAwayShiftedDiagonalUniformConstant T δ := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hQle := fixedAwayPVQuadraticDecayConstant_le_uniform hδ hδt htT
  have hQ0 := fixedAwayPVQuadraticDecayConstant_nonneg t δ
  have hQu := fixedAwayPVQuadraticDecayUniformConstant_nonneg hT δ
  have hmass := fixedAwayIntegerQuadraticEnvelopeMass_nonneg
  unfold fixedAwayShiftedDiagonalConstant
    fixedAwayShiftedDiagonalUniformConstant
  gcongr

/-- Common one-block energy for the unprojected shifted multiplier. -/
def fixedAwayShiftedDyadicEnergyUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  2 * fixedAwayShiftedDiagonalUniformConstant T δ +
    32 * fixedAwayHermitianRapidBVUniformConstant T δ J

theorem fixedAwayShiftedDyadicEnergyConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayShiftedDyadicEnergyConstant t δ J ≤
      fixedAwayShiftedDyadicEnergyUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hQle := fixedAwayPVQuadraticDecayConstant_le_uniform hδ hδt htT
  have hBVle := fixedAwayHermitianRapidBVConstant_le_uniform
    hδ hδt htT J
  have hQ0 := fixedAwayPVQuadraticDecayConstant_nonneg t δ
  have hQu := fixedAwayPVQuadraticDecayUniformConstant_nonneg hT δ
  have hmass := fixedAwayIntegerQuadraticEnvelopeMass_nonneg
  unfold fixedAwayShiftedDyadicEnergyConstant
    fixedAwayShiftedDyadicEnergyUniformConstant
    fixedAwayShiftedDiagonalConstant
    fixedAwayShiftedDiagonalUniformConstant
  gcongr

/-- Common one-block energy for the projected shifted multiplier. -/
def fixedAwayProjectedDyadicEnergyUniformConstant
    (T δ : ℝ) (J : ℕ) : ℝ :=
  2 * (16 * fixedAwayPVRapidDecayUniformConstant T δ (J + 2) ^ 2 *
      fixedAwayIntegerQuadraticEnvelopeMass) +
    32 * fixedAwayProjectedRapidBVUniformConstant T δ J

theorem fixedAwayProjectedDyadicEnergyConstant_le_uniform
    {t δ T : ℝ} (hδ : 0 < δ) (hδt : δ ≤ t)
    (htT : t ≤ T) (J : ℕ) :
    fixedAwayProjectedDyadicEnergyConstant t δ J ≤
      fixedAwayProjectedDyadicEnergyUniformConstant T δ J := by
  have ht : 0 ≤ t := hδ.le.trans hδt
  have hT : 0 ≤ T := ht.trans htT
  have hCle := fixedAwayPVRapidDecayConstant_le_uniform
    hδ hδt htT (J + 2)
  have hBVle := fixedAwayProjectedRapidBVConstant_le_uniform
    hδ hδt htT J
  have hC0 := fixedAwayPVRapidDecayConstant_nonneg_all t δ (J + 2)
  have hCu := fixedAwayPVRapidDecayUniformConstant_nonneg hT δ (J + 2)
  have hmass := fixedAwayIntegerQuadraticEnvelopeMass_nonneg
  unfold fixedAwayProjectedDyadicEnergyConstant
    fixedAwayProjectedDiagonalConstant
    fixedAwayProjectedDyadicEnergyUniformConstant
  gcongr

/-! ## Uniform forms of the low/high dyadic estimates -/

/-- The complete low-block estimate with constants independent of the moving
threshold `t ∈ [δ,T]`. -/
theorem tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff_uniform
    {t δ T R : ℝ} {N M : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hN : 0 < N) (hell : ell ≠ 0) (hR : 0 < R)
    (hcut : ∀ s ∈ nearCarrierDyadicExponents M,
      ((2 ^ s : ℕ) : ℝ) * R ≤ (N : ℝ))
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedDyadicTotalSum t δ N M ell n‖ ^ 2) ≤
      2 * (4 * M * fixedAwayShiftedDyadicEnergyUniformConstant T δ J +
        M ^ 2 * fixedAwayProjectedDyadicEnergyUniformConstant T δ J *
          fixedAwayRapidEnvelope J (R / 4)) := by
  have hbase := tsum_fixedAwayShiftedDyadicTotalSum_norm_sq_le_of_cutoff
    (t := t) (δ := δ) (R := R) (N := N) (M := M) (ell := ell)
    hδ hδt hN hell hR hcut hJ
  refine hbase.trans ?_
  have hshift := fixedAwayShiftedDyadicEnergyConstant_le_uniform
    hδ hδt.le htT J
  have hproj := fixedAwayProjectedDyadicEnergyConstant_le_uniform
    hδ hδt.le htT J
  have henv : 0 ≤ fixedAwayRapidEnvelope J (R / 4) :=
    fixedAwayRapidEnvelope_nonneg J _
  gcongr

/-- Every finite terminal collection has a threshold-uniform energy bound. -/
theorem tsum_fixedAwayShiftedExponentFinsetSum_norm_sq_le_uniform
    {S : Finset ℕ} {t δ T : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    (hs2 : ∀ s ∈ S, 2 ≤ s)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ,
      ‖fixedAwayShiftedExponentFinsetSum S t δ N ell n‖ ^ 2) ≤
      S.card ^ 2 * fixedAwayShiftedDyadicEnergyUniformConstant T δ J := by
  refine (tsum_fixedAwayShiftedExponentFinsetSum_norm_sq_le
    (t := t) (δ := δ) (N := N) (ell := ell)
    hδ hδt hs2 hJ).trans ?_
  exact mul_le_mul_of_nonneg_left
    (fixedAwayShiftedDyadicEnergyConstant_le_uniform
      hδ hδt.le htT J) (by positivity)

/-- The fixed denominators `p=1,2` are uniformly bounded as well. -/
theorem tsum_fixedAwayShiftedFinitePrefix_norm_sq_le_uniform
    {t δ T : ℝ} {N : ℕ} {ell : ℤ}
    (hδ : 0 < δ) (hδt : δ < t) (htT : t ≤ T)
    {J : ℕ} (hJ : 0 < J) :
    (∑' n : ℤ, ‖fixedAwayShiftedFinitePrefix t δ N ell n‖ ^ 2) ≤
      2 * (fixedAwayShiftedDiagonalUniformConstant T δ +
        fixedAwayShiftedDyadicEnergyUniformConstant T δ J) := by
  refine (tsum_fixedAwayShiftedFinitePrefix_norm_sq_le
    (N := N) (ell := ell) hδ hδt hJ).trans ?_
  have hdiag := fixedAwayShiftedDiagonalConstant_le_uniform
    hδ hδt.le htT
  have hblock := fixedAwayShiftedDyadicEnergyConstant_le_uniform
    hδ hδt.le htT J
  gcongr

end

end Erdos1002
