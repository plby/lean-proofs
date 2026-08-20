import ErdosProblems.Erdos525.EvenLaw

/-!
# The odd coefficient-count model

The Cook--Nguyen argument is stated for the symmetric interval `[-n,n]`.
For a degree `2n+1` Littlewood polynomial, multiplication by a unit complex
phase changes the half-integer-centered process into the integer-frequency
interval `[-n,n+1]`.  This file records that model and its exact decomposition
into the already formalized symmetric walk plus one independent Rademacher
step.  Later files use the decomposition to transfer the local limit and
anti-concentration estimates; no probabilistic assumption is introduced.
-/

open scoped BigOperators Topology ComplexConjugate RealInnerProductSpace

namespace Erdos525

open Classical Filter Finset Set MeasureTheory

namespace Odd

/-- Restriction of an odd-degree sign vector to its first `2n+1` entries. -/
def initialSegment (n : ℕ) (e : SignVector (2 * n + 1)) : SignVector (2 * n) :=
  fun j ↦ e j.castSucc

/-- The final, independent sign in the interval `[-n,n+1]`. -/
def lastSign (n : ℕ) (e : SignVector (2 * n + 1)) : Bool :=
  e (Fin.last (2 * n + 1))

/-- Reassemble a prefix and its final sign. -/
def appendSign (n : ℕ) (e : SignVector (2 * n)) (b : Bool) :
    SignVector (2 * n + 1) :=
  Fin.lastCases b e

@[simp] lemma initialSegment_appendSign (n : ℕ) (e : SignVector (2 * n)) (b : Bool) :
    initialSegment n (appendSign n e b) = e := by
  funext j
  simp [initialSegment, appendSign]

@[simp] lemma lastSign_appendSign (n : ℕ) (e : SignVector (2 * n)) (b : Bool) :
    lastSign n (appendSign n e b) = b := by
  simp [lastSign, appendSign]

@[simp] lemma appendSign_initialSegment_lastSign (n : ℕ)
    (e : SignVector (2 * n + 1)) :
    appendSign n (initialSegment n e) (lastSign n e) = e := by
  funext j
  refine Fin.lastCases ?_ (fun i ↦ ?_) j
  · simp [appendSign, lastSign]
  · simp [appendSign, initialSegment]

/-- The exact equivalence which exhibits the last coefficient as independent. -/
def splitEquiv (n : ℕ) :
    SignVector (2 * n + 1) ≃ SignVector (2 * n) × Bool where
  toFun e := (initialSegment n e, lastSign n e)
  invFun p := appendSign n p.1 p.2
  left_inv := appendSign_initialSegment_lastSign n
  right_inv p := by ext <;> simp

/-- Normalization of the symmetric `2n+1`-term prefix inside the
`2n+2`-term odd model. -/
noncomputable def prefixScale (n : ℕ) : ℝ :=
  Real.sqrt (2 * n + 1 : ℝ) / Real.sqrt (2 * n + 2 : ℝ)

lemma prefixScale_pos (n : ℕ) : 0 < prefixScale n := by
  exact div_pos (by positivity) (by positivity)

lemma prefixScale_le_one (n : ℕ) : prefixScale n ≤ 1 := by
  unfold prefixScale
  rw [div_le_one (by positivity : 0 < Real.sqrt (2 * n + 2 : ℝ))]
  exact Real.sqrt_le_sqrt (by norm_num)

lemma prefixScale_tendsto_one :
    Tendsto prefixScale atTop (𝓝 1) := by
  have hinv : Tendsto (fun n : ℕ ↦ ((n : ℝ))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop
  have hratio : Tendsto (fun n : ℕ ↦
      (2 + ((n : ℝ))⁻¹) / (2 + 2 * ((n : ℝ))⁻¹)) atTop (𝓝 1) := by
    have hnum : Tendsto (fun n : ℕ ↦ 2 + ((n : ℝ))⁻¹) atTop (𝓝 2) := by
      simpa using tendsto_const_nhds.add hinv
    have hden : Tendsto (fun n : ℕ ↦ 2 + 2 * ((n : ℝ))⁻¹) atTop (𝓝 2) := by
      simpa using tendsto_const_nhds.add (hinv.const_mul 2)
    have h := hnum.div hden (by norm_num)
    convert h using 1
    · funext n
      rfl
    · norm_num
  have hsqrt : Tendsto (fun n : ℕ ↦ Real.sqrt
      ((2 + ((n : ℝ))⁻¹) / (2 + 2 * ((n : ℝ))⁻¹))) atTop (𝓝 1) := by
    simpa only [Real.sqrt_one] using hratio.sqrt
  apply hsqrt.congr'
  filter_upwards [Nat.eventually_pos] with n hn
  have hn0 : (n : ℝ) ≠ 0 := by exact_mod_cast hn.ne'
  have hnum0 : 0 ≤ (2 * n + 1 : ℝ) := by positivity
  have hden0 : 0 ≤ (2 * n + 2 : ℝ) := by positivity
  have hdenpos : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
  rw [show prefixScale n = Real.sqrt
      ((2 * n + 1 : ℝ) / (2 * n + 2 : ℝ)) by
    rw [prefixScale, Real.sqrt_div hnum0]]
  congr 1
  field_simp

/-- The degree-`2n+1` process after multiplication by the harmless unit
phase `exp(ix/2)`, written in microscopic time `t = nx`.  Its integer
frequencies are `-n,...,n+1`. -/
noncomputable def eval (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) : ℂ :=
  (prefixScale n : ℂ) * rescaledCenteredEval n (initialSegment n e) t +
    (sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) *
      Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)

/-- Microscopic derivative of `Odd.eval`. -/
noncomputable def velocity (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) : ℂ :=
  (prefixScale n : ℂ) * rescaledCenteredVelocity n (initialSegment n e) t +
    (sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) *
      ((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) *
      Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)

/-- Microscopic second derivative of `Odd.eval`. -/
noncomputable def acceleration (n : ℕ) (e : SignVector (2 * n + 1))
    (t : ℝ) : ℂ :=
  (prefixScale n : ℂ) * rescaledCenteredAcceleration n (initialSegment n e) t +
    (sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) *
      ((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I) ^ 2 *
      Complex.exp ((((n + 1 : ℕ) : ℝ) * (t / n) : ℂ) * Complex.I)

lemma hasDerivAt_eval (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    HasDerivAt (eval n e) (velocity n e t) t := by
  unfold eval velocity
  apply HasDerivAt.add
  · exact (hasDerivAt_rescaledCenteredEval n (initialSegment n e) t).const_mul
      (prefixScale n : ℂ)
  · have hlinear : HasDerivAt
      (fun s : ℝ ↦ ((((n + 1 : ℕ) : ℝ) * (s / n) : ℂ) * Complex.I))
        (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I)) t := by
      have h := (((hasDerivAt_id t).div_const (n : ℝ)).ofReal_comp.const_mul
        (((n + 1 : ℕ) : ℝ) : ℂ)).mul_const Complex.I
      simpa [div_eq_mul_inv] using h
    simpa only [mul_comm, mul_left_comm, mul_assoc] using
      hlinear.cexp.const_mul
        ((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ)

lemma hasDerivAt_velocity (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    HasDerivAt (velocity n e) (acceleration n e t) t := by
  unfold velocity acceleration
  apply HasDerivAt.add
  · exact (hasDerivAt_rescaledCenteredVelocity n (initialSegment n e) t).const_mul
      (prefixScale n : ℂ)
  · have hlinear : HasDerivAt
      (fun s : ℝ ↦ ((((n + 1 : ℕ) : ℝ) * (s / n) : ℂ) * Complex.I))
        (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I)) t := by
      have h := (((hasDerivAt_id t).div_const (n : ℝ)).ofReal_comp.const_mul
        (((n + 1 : ℕ) : ℝ) : ℂ)).mul_const Complex.I
      simpa [div_eq_mul_inv] using h
    simpa only [pow_two, mul_comm, mul_left_comm, mul_assoc] using
      hlinear.cexp.const_mul
        (((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          (((((n + 1 : ℕ) : ℝ) / n : ℂ) * Complex.I)))

/-- Phase-space vector associated to the odd interval model. -/
noncomputable def normalizedPhaseWalk (n : ℕ)
    (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) : PhaseCoordinate m :=
  fun r ↦ ![(eval n e (points r)).re, (eval n e (points r)).im,
    (velocity n e (points r)).re, (velocity n e (points r)).im]

noncomputable def normalizedPhaseEuclideanWalk (n : ℕ)
    (e : SignVector (2 * n + 1)) (points : Fin m → ℝ) : PhaseEuclidean m :=
  phaseToEuclidean (normalizedPhaseWalk n e points)

/-- The one-step displacement contributed by the final coefficient. -/
noncomputable def extraPhase (n : ℕ) (b : Bool)
    (points : Fin m → ℝ) : PhaseCoordinate m := fun r ↦
  let q := ((n + 1 : ℕ) : ℝ) / n
  let c := sign b / Real.sqrt (2 * n + 2 : ℝ)
  let z : ℂ := c *
    Complex.exp ((((n + 1 : ℕ) : ℝ) * (points r / n) : ℂ) * Complex.I)
  let w : ℂ := c * ((q : ℂ) * Complex.I) *
    Complex.exp ((((n + 1 : ℕ) : ℝ) * (points r / n) : ℂ) * Complex.I)
  ![z.re, z.im, w.re, w.im]

noncomputable def extraPhaseEuclidean (n : ℕ) (b : Bool)
    (points : Fin m → ℝ) : PhaseEuclidean m :=
  phaseToEuclidean (extraPhase n b points)

lemma abs_sign (b : Bool) : |sign b| = 1 := by
  cases b <;> simp [sign]

lemma extraPhase_coordinate_bound {n : ℕ} (hn : 0 < n) (b : Bool)
    (points : Fin m → ℝ) (r : Fin m) (c : Fin 4) :
    |extraPhase n b points r c| ≤
      2 / Real.sqrt (2 * n + 2 : ℝ) := by
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hsqrt : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
  have hone : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hq : ((n + 1 : ℕ) : ℝ) / n ≤ 2 := by
    rw [div_le_iff₀ hnreal]
    push_cast
    linarith
  let q : ℝ := ((n + 1 : ℕ) : ℝ) / n
  let d : ℝ := sign b / Real.sqrt (2 * n + 2 : ℝ)
  let z : ℂ := d *
    Complex.exp ((((n + 1 : ℕ) : ℝ) * (points r / n) : ℂ) * Complex.I)
  let w : ℂ := d * ((q : ℂ) * Complex.I) *
    Complex.exp ((((n + 1 : ℕ) : ℝ) * (points r / n) : ℂ) * Complex.I)
  have hznorm : ‖z‖ = 1 / Real.sqrt (2 * n + 2 : ℝ) := by
    dsimp [z, d]
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_div, abs_sign,
      abs_of_pos hsqrt, one_div, Complex.norm_exp]
    simp [Complex.mul_re]
  have hq0 : 0 ≤ q := by dsimp [q]; positivity
  have hdabs : |d| = 1 / Real.sqrt (2 * n + 2 : ℝ) := by
    dsimp [d]
    rw [abs_div, abs_sign, abs_of_pos hsqrt, one_div]
  have hexpnorm :
      ‖Complex.exp ((((n + 1 : ℕ) : ℝ) * (points r / n) : ℂ) * Complex.I)‖ = 1 := by
    rw [Complex.norm_exp]
    simp [Complex.mul_re]
  have hwnorm : ‖w‖ ≤ 2 / Real.sqrt (2 * n + 2 : ℝ) := by
    calc
      ‖w‖ = |d| * q * 1 := by
        dsimp [w]
        rw [norm_mul, norm_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs,
          Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hq0,
          Complex.norm_I]
        simp [Complex.norm_exp, Complex.mul_re]
      _ = (1 / Real.sqrt (2 * n + 2 : ℝ)) * q := by rw [hdabs]; ring
      _ ≤ (1 / Real.sqrt (2 * n + 2 : ℝ)) * 2 :=
        mul_le_mul_of_nonneg_left hq (by positivity)
      _ = 2 / Real.sqrt (2 * n + 2 : ℝ) := by ring
  fin_cases c
  · apply (Complex.abs_re_le_norm z).trans
    rw [hznorm]
    gcongr
    norm_num
  · apply (Complex.abs_im_le_norm z).trans
    rw [hznorm]
    gcongr
    norm_num
  · exact (Complex.abs_re_le_norm w).trans hwnorm
  · exact (Complex.abs_im_le_norm w).trans hwnorm

lemma norm_extraPhaseEuclidean_sq_le {n : ℕ} (hn : 0 < n) (b : Bool)
    (points : Fin m → ℝ) :
    ‖extraPhaseEuclidean n b points‖ ^ 2 ≤
      (4 * m : ℝ) * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2 := by
  change ‖phaseToEuclidean (extraPhase n b points)‖ ^ 2 ≤ _
  rw [← phaseNormSq_eq_norm_sq]
  unfold phaseNormSq
  calc
    (∑ r : Fin m, ∑ c : Fin 4, (extraPhase n b points r c) ^ 2) ≤
        ∑ _r : Fin m, ∑ _c : Fin 4,
          (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2 := by
      apply Finset.sum_le_sum
      intro r _hr
      apply Finset.sum_le_sum
      intro c _hc
      have h := extraPhase_coordinate_bound hn b points r c
      have h0 : 0 ≤ 2 / Real.sqrt (2 * n + 2 : ℝ) := by positivity
      nlinarith [sq_abs (extraPhase n b points r c), abs_nonneg (extraPhase n b points r c)]
    _ = (4 * m : ℝ) * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2 := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      push_cast
      ring

lemma norm_extraPhaseEuclidean_tendsto_zero (b : Bool)
    (points : ∀ n, Fin m → ℝ) :
    Tendsto (fun n : ℕ ↦ ‖extraPhaseEuclidean n b (points n)‖)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ (2 * n + 2 : ℝ)) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      tendsto_atTop_add_const_right atTop 2 h
  have hinv : Tendsto (fun n : ℕ ↦ ((2 * n + 2 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hden
  have hupper : Tendsto (fun n : ℕ ↦
      (4 * m : ℝ) * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2)
      atTop (𝓝 0) := by
    have heq : ∀ n : ℕ,
        (4 * m : ℝ) * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2 =
          (16 * m : ℝ) * ((2 * n + 2 : ℝ))⁻¹ := by
      intro n
      have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n + 2)
      have hp : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
      rw [div_pow, hs, inv_eq_one_div]
      ring
    have h := hinv.const_mul (16 * m : ℝ)
    simpa only [mul_zero] using h.congr'
      (Eventually.of_forall fun n ↦ (heq n).symm)
  have hsq : Tendsto (fun n : ℕ ↦
      ‖extraPhaseEuclidean n b (points n)‖ ^ 2) atTop (𝓝 0) := by
    apply squeeze_zero'
    · exact Eventually.of_forall fun n ↦ sq_nonneg _
    · filter_upwards [Nat.eventually_pos] with n hn
      exact norm_extraPhaseEuclidean_sq_le hn b (points n)
    · exact hupper
  have hsqrt := hsq.sqrt
  simpa only [Real.sqrt_zero, Real.sqrt_sq_eq_abs, abs_norm] using hsqrt

lemma extraPhase_sq_upper_tendsto_zero :
    Tendsto (fun n : ℕ ↦
      (4 * m : ℝ) * (2 / Real.sqrt (2 * n + 2 : ℝ)) ^ 2)
      atTop (𝓝 0) := by
  have hden : Tendsto (fun n : ℕ ↦ (2 * n + 2 : ℝ)) atTop atTop := by
    have h := (tendsto_natCast_atTop_atTop.const_mul_atTop (by norm_num : (0 : ℝ) < 2))
    simpa only [Nat.cast_ofNat, Nat.cast_mul] using
      tendsto_atTop_add_const_right atTop 2 h
  have hinv : Tendsto (fun n : ℕ ↦ ((2 * n + 2 : ℝ))⁻¹)
      atTop (𝓝 0) := tendsto_inv_atTop_zero.comp hden
  have h := hinv.const_mul (16 * m : ℝ)
  simpa only [mul_zero] using h.congr' (Eventually.of_forall fun n ↦ by
    have hs := Real.sq_sqrt (by positivity : (0 : ℝ) ≤ 2 * n + 2)
    rw [div_pow, hs, inv_eq_one_div]
    ring)

lemma eventually_uniform_norm_extraPhaseEuclidean_lt
    {eps : ℝ} (heps : 0 < eps) :
    ∀ᶠ n : ℕ in atTop, ∀ (b : Bool) (points : Fin m → ℝ),
      ‖extraPhaseEuclidean n b points‖ < eps := by
  have hepssq : 0 < eps ^ 2 := sq_pos_of_pos heps
  have hupper := extraPhase_sq_upper_tendsto_zero (m := m)
  filter_upwards [Nat.eventually_pos,
      hupper.eventually (Iio_mem_nhds hepssq)] with n hn hsmall
  intro b points
  have hbound := norm_extraPhaseEuclidean_sq_le (m := m) hn b points
  nlinarith [sq_nonneg ‖extraPhaseEuclidean n b points‖,
    norm_nonneg (extraPhaseEuclidean n b points)]

lemma normalizedPhaseWalk_eq (n : ℕ) (e : SignVector (2 * n + 1))
    (points : Fin m → ℝ) :
    normalizedPhaseWalk n e points = fun r c ↦
      prefixScale n * Erdos525.normalizedPhaseWalk n (initialSegment n e) points r c +
        extraPhase n (lastSign n e) points r c := by
  funext r c
  fin_cases c
  · have h := congrArg Complex.re
      (phasePosition_normalizedPhaseWalk n (initialSegment n e) points r)
    change Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 0 = _ at h
    change normalizedPhaseWalk n e points r 0 =
      prefixScale n * Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 0 +
        extraPhase n (lastSign n e) points r 0
    rw [h]
    simp [Odd.normalizedPhaseWalk, Odd.eval, extraPhase, Complex.mul_re]
  · have h := congrArg Complex.im
      (phasePosition_normalizedPhaseWalk n (initialSegment n e) points r)
    change Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 1 = _ at h
    change normalizedPhaseWalk n e points r 1 =
      prefixScale n * Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 1 +
        extraPhase n (lastSign n e) points r 1
    rw [h]
    simp [Odd.normalizedPhaseWalk, Odd.eval, extraPhase, Complex.mul_im]
  · have h := congrArg Complex.re
      (phaseVelocity_normalizedPhaseWalk n (initialSegment n e) points r)
    change Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 2 = _ at h
    change normalizedPhaseWalk n e points r 2 =
      prefixScale n * Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 2 +
        extraPhase n (lastSign n e) points r 2
    rw [h]
    simp [Odd.normalizedPhaseWalk, Odd.velocity, extraPhase, Complex.mul_re]
  · have h := congrArg Complex.im
      (phaseVelocity_normalizedPhaseWalk n (initialSegment n e) points r)
    change Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 3 = _ at h
    change normalizedPhaseWalk n e points r 3 =
      prefixScale n * Erdos525.normalizedPhaseWalk n (initialSegment n e) points r 3 +
        extraPhase n (lastSign n e) points r 3
    rw [h]
    simp [Odd.normalizedPhaseWalk, Odd.velocity, extraPhase, Complex.mul_im]

lemma normalizedPhaseEuclideanWalk_appendSign (n : ℕ)
    (e : SignVector (2 * n)) (b : Bool) (points : Fin m → ℝ) :
    normalizedPhaseEuclideanWalk n (appendSign n e b) points =
      prefixScale n • Erdos525.normalizedPhaseEuclideanWalk n e points +
        extraPhaseEuclidean n b points := by
  ext i
  rcases i with ⟨r, c⟩
  simp only [Odd.normalizedPhaseEuclideanWalk, extraPhaseEuclidean,
    Erdos525.normalizedPhaseEuclideanWalk,
    phaseToEuclidean_apply, PiLp.add_apply, Pi.add_apply, PiLp.smul_apply,
    Pi.smul_apply, smul_eq_mul]
  rw [normalizedPhaseWalk_eq]
  simp

lemma littlewoodEval_appendSign (n : ℕ) (e : SignVector (2 * n))
    (b : Bool) (z : ℂ) :
    littlewoodEval (appendSign n e b) z =
      littlewoodEval e z + (sign b : ℂ) * z ^ (2 * n + 1) := by
  unfold littlewoodEval
  rw [Fin.sum_univ_castSucc]
  congr 1
  · apply Finset.sum_congr rfl
    intro j _hj
    simp [appendSign]
  · simp [appendSign]

/-- Exact identification with the odd centered polynomial.  The prefactor
has norm one, so it does not alter the minimum modulus. -/
lemma eval_eq_phase_mul_oddCenteredEval (n : ℕ)
    (e : SignVector (2 * n + 1)) (t : ℝ) :
    eval n e t =
      Complex.exp ((((t / n) / 2 : ℝ) : ℂ) * Complex.I) *
        oddCenteredEval n e (t / n) := by
  rw [oddCenteredEval_eq_phase_mul_littlewoodEval]
  have hpoly : littlewoodEval e (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I)) =
      littlewoodEval (initialSegment n e)
          (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I)) +
        (sign (lastSign n e) : ℂ) *
          Complex.exp (((t / n : ℝ) : ℂ) * Complex.I) ^ (2 * n + 1) := by
    rw [show e = appendSign n (initialSegment n e) (lastSign n e) by
      exact (appendSign_initialSegment_lastSign n e).symm]
    simpa using littlewoodEval_appendSign n (initialSegment n e) (lastSign n e) _
  rw [hpoly]
  unfold eval rescaledCenteredEval
  rw [centeredEval_eq_phase_mul_littlewoodEval]
  unfold prefixScale
  have hp : 0 < Real.sqrt (2 * n + 1 : ℝ) := by positivity
  have hc : 0 < Real.sqrt (2 * n + 2 : ℝ) := by positivity
  have hprefix :
      ((Real.sqrt (2 * n + 1 : ℝ) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          (Real.sqrt (2 * n + 1 : ℝ) : ℂ)⁻¹ =
        (Real.sqrt (2 * n + 2 : ℝ) : ℂ)⁻¹ := by
    have hpC : (Real.sqrt (2 * n + 1 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hp.ne'
    have hcC : (Real.sqrt (2 * n + 2 : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast hc.ne'
    push_cast
    field_simp [hpC, hcC]
  have hextra :
      (((sign (lastSign n e) / Real.sqrt (2 * n + 2 : ℝ) : ℝ)) : ℂ) =
        (Real.sqrt (2 * n + 2 : ℝ) : ℂ)⁻¹ * sign (lastSign n e) := by
    push_cast
    field_simp
  have hphasePrefix :
      Complex.exp ((((t / n) / 2 : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((-(n + 1 / 2 : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) =
        Complex.exp (((-(n : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hphaseLast :
      Complex.exp (((-(n : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) *
          Complex.exp (((t / n : ℝ) : ℂ) * Complex.I) ^ (2 * n + 1) =
        Complex.exp (((((n + 1 : ℕ) : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) := by
    rw [← Complex.exp_nat_mul, ← Complex.exp_add]
    congr 1
    push_cast
    ring
  have hactualLast :
      Complex.exp ((((n + 1 : ℕ) : ℝ) * ((t : ℂ) / n)) * Complex.I) =
        Complex.exp (((((n + 1 : ℕ) : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) := by
    congr 1
    push_cast
    ring
  rw [show
      ((Real.sqrt (2 * n + 1 : ℝ) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          ((Real.sqrt (2 * n + 1 : ℝ) : ℂ)⁻¹ *
            Complex.exp (((-(n : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) *
            littlewoodEval (initialSegment n e)
              (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I))) =
        (((Real.sqrt (2 * n + 1 : ℝ) / Real.sqrt (2 * n + 2 : ℝ) : ℝ) : ℂ) *
          (Real.sqrt (2 * n + 1 : ℝ) : ℂ)⁻¹) *
            Complex.exp (((-(n : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) *
            littlewoodEval (initialSegment n e)
              (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I)) by ring,
      hprefix, hextra, hactualLast]
  rw [← hphaseLast]
  rw [show
      Complex.exp ((((t / n) / 2 : ℝ) : ℂ) * Complex.I) *
          ((Real.sqrt (2 * n + 2 : ℝ) : ℂ)⁻¹ *
            Complex.exp (((-(n + 1 / 2 : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I) *
            (littlewoodEval (initialSegment n e)
                (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I)) +
              (sign (lastSign n e) : ℂ) *
                Complex.exp (((t / n : ℝ) : ℂ) * Complex.I) ^ (2 * n + 1))) =
        (Real.sqrt (2 * n + 2 : ℝ) : ℂ)⁻¹ *
            (Complex.exp ((((t / n) / 2 : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(n + 1 / 2 : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I)) *
            littlewoodEval (initialSegment n e)
              (Complex.exp (((t / n : ℝ) : ℂ) * Complex.I)) +
          (Real.sqrt (2 * n + 2 : ℝ) : ℂ)⁻¹ *
            (sign (lastSign n e) : ℂ) *
            (Complex.exp ((((t / n) / 2 : ℝ) : ℂ) * Complex.I) *
              Complex.exp (((-(n + 1 / 2 : ℝ) * (t / n) : ℝ) : ℂ) * Complex.I)) *
            Complex.exp (((t / n : ℝ) : ℂ) * Complex.I) ^ (2 * n + 1) by ring,
      hphasePrefix]
  ring

lemma norm_eval (n : ℕ) (e : SignVector (2 * n + 1)) (t : ℝ) :
    ‖eval n e t‖ = ‖oddCenteredEval n e (t / n)‖ := by
  rw [eval_eq_phase_mul_oddCenteredEval, norm_mul,
    Complex.norm_exp_ofReal_mul_I, one_mul]

/-- Tail in the integer-frequency odd interval, using the same microscopic
bandwidth `n` and mesh as the symmetric model. -/
noncomputable def tail (n : ℕ) (u : ℝ) : ℝ :=
  uniformProbability (fun e : SignVector (2 * n + 1) ↦
    u / (n : ℝ) < oddCenteredMin n e)

lemma oddCenteredTail_eq_tail (n : ℕ) (hn : 0 < n) (u : ℝ) :
    oddCenteredTail n u = tail n (u * n / (n + 1 / 2 : ℝ)) := by
  unfold oddCenteredTail tail
  apply congrArg uniformProbability
  funext e
  apply propext
  have hnreal : (0 : ℝ) < n := by exact_mod_cast hn
  have hband : (0 : ℝ) < n + 1 / 2 := by positivity
  rw [show (u * n / (n + 1 / 2 : ℝ)) / n = u / (n + 1 / 2 : ℝ) by
    field_simp]

lemma tail_antitone (n : ℕ) : Antitone (tail n) := by
  intro u v huv
  by_cases hn : n = 0
  · subst n
    simp [tail]
  · apply uniformProbability_mono
    intro e he
    exact lt_of_le_of_lt
      ((div_le_div_iff_of_pos_right (by exact_mod_cast Nat.pos_of_ne_zero hn)).2 huv) he

/-- The same conditioning identity for normalized expectations. -/
lemma uniformExpectation_split (n : ℕ)
    (X : SignVector (2 * n + 1) → ℝ) :
    uniformExpectation X =
      (uniformExpectation (fun e : SignVector (2 * n) ↦ X (appendSign n e false)) +
        uniformExpectation (fun e : SignVector (2 * n) ↦ X (appendSign n e true))) / 2 := by
  unfold uniformExpectation
  have hsum :
      ∑ e : SignVector (2 * n + 1), X e =
        ∑ p : SignVector (2 * n) × Bool, X (appendSign n p.1 p.2) := by
    simpa [splitEquiv] using
      (Equiv.sum_comp (splitEquiv n)
        (fun p : SignVector (2 * n) × Bool ↦ X (appendSign n p.1 p.2)))
  rw [hsum, Fintype.sum_prod_type]
  simp only [Fintype.sum_bool]
  rw [Finset.sum_add_distrib]
  simp only [card_signVector]
  push_cast
  rw [show (2 : ℝ) ^ (2 * n + 1 + 1) =
      2 * (2 : ℝ) ^ (2 * n + 1) by ring]
  field_simp
  ring

/-- Exact conditioning on the final independent Rademacher coefficient. -/
lemma uniformProbability_split (n : ℕ)
    (P : SignVector (2 * n + 1) → Prop) :
    uniformProbability P =
      (uniformProbability (fun e : SignVector (2 * n) ↦ P (appendSign n e false)) +
        uniformProbability (fun e : SignVector (2 * n) ↦ P (appendSign n e true))) / 2 := by
  rw [← uniformExpectation_indicator P,
    uniformExpectation_split]
  rw [uniformExpectation_indicator, uniformExpectation_indicator]

end Odd

end Erdos525
