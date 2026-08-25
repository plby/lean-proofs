import ErdosProblems.Erdos67.MRFiniteHalaszDyadicEndpoint

/-!
# Elementary near/medium Halasz energy integrals

The complex Halasz bound has two frequency regimes around a minimizing
frequency: a constant exponentially small bound on a central interval and a
reciprocal-distance bound on the adjacent intervals.  This file evaluates
the latter square integral exactly and packages both estimates for the
finite-polynomial proof of Appendix A, Proposition A.3.
-/

open MeasureTheory

namespace Erdos67

noncomputable section

/-- Exact integral of the inverse-square distance on one side of its pole. -/
theorem intervalIntegral_inv_sq_sub_eq
    {c a b : ℝ} (hca : c < a) (hab : a ≤ b) :
    (∫ x in a..b, ((x - c) ^ 2)⁻¹) =
      (a - c)⁻¹ - (b - c)⁻¹ := by
  have hderiv : ∀ x ∈ Set.uIcc a b,
      HasDerivAt (-(fun y : ℝ ↦ y - c)⁻¹) ((x - c) ^ 2)⁻¹ x := by
    intro x hx
    have hax : a ≤ x := by
      rw [Set.uIcc_of_le hab] at hx
      exact hx.1
    have hxc : x - c ≠ 0 := by linarith
    apply HasDerivAt.congr_deriv
      (((hasDerivAt_id x).sub_const c).inv hxc).neg
    simp [div_eq_mul_inv]
  have hint : IntervalIntegrable (fun x : ℝ ↦ ((x - c) ^ 2)⁻¹)
      MeasureTheory.volume a b := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro x hx
      have hax : a ≤ x := by
        rw [Set.uIcc_of_le hab] at hx
        exact hx.1
      exact pow_ne_zero 2 (sub_ne_zero.mpr (ne_of_gt (hca.trans_le hax)))
  have hfund := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  rw [hfund]
  simp only [Pi.neg_apply, Pi.inv_apply]
  ring

/-- A right reciprocal-distance tail has square mass at most the reciprocal
of its inner radius. -/
theorem intervalIntegral_inv_sq_sub_le_inv
    {c R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ x in c + R..c + S, ((x - c) ^ 2)⁻¹) ≤ R⁻¹ := by
  rw [intervalIntegral_inv_sq_sub_eq (by linarith) (by linarith)]
  have hSinv : 0 ≤ S⁻¹ := inv_nonneg.mpr (hR.le.trans hRS)
  simpa using sub_le_self R⁻¹ hSinv

/-- The corresponding left reciprocal-distance tail has the same bound. -/
theorem intervalIntegral_inv_sq_sub_le_inv_left
    {c R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ x in c - S..c - R, ((x - c) ^ 2)⁻¹) ≤ R⁻¹ := by
  have hnonzero : ∀ x ∈ Set.uIcc (c - S) (c - R), x - c ≠ 0 := by
    intro x hx
    rw [Set.uIcc_of_le (by linarith)] at hx
    have : x ≤ c - R := hx.2
    linarith
  have hderiv : ∀ x ∈ Set.uIcc (c - S) (c - R),
      HasDerivAt (-(fun y : ℝ ↦ y - c)⁻¹) ((x - c) ^ 2)⁻¹ x := by
    intro x hx
    apply HasDerivAt.congr_deriv
      (((hasDerivAt_id x).sub_const c).inv (hnonzero x hx)).neg
    simp [div_eq_mul_inv]
  have hint : IntervalIntegrable (fun x : ℝ ↦ ((x - c) ^ 2)⁻¹)
      MeasureTheory.volume (c - S) (c - R) := by
    apply ContinuousOn.intervalIntegrable
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro x hx
      exact pow_ne_zero 2 (hnonzero x hx)
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint]
  simp only [Pi.neg_apply, Pi.inv_apply]
  have hSinv : 0 ≤ S⁻¹ := inv_nonneg.mpr (hR.le.trans hRS)
  have heq :
      (-(c - R - c)⁻¹) - (-(c - S - c)⁻¹) = R⁻¹ - S⁻¹ := by
    rw [show c - R - c = -R by ring, show c - S - c = -S by ring,
      inv_neg, inv_neg]
    ring
  rw [heq]
  exact sub_le_self R⁻¹ hSinv

/-- The two reciprocal-distance side intervals together have square mass at
most `2/R`. -/
theorem two_sided_intervalIntegral_inv_sq_sub_le
    {c R S : ℝ} (hR : 0 < R) (hRS : R ≤ S) :
    (∫ x in c - S..c - R, ((x - c) ^ 2)⁻¹) +
        (∫ x in c + R..c + S, ((x - c) ^ 2)⁻¹) ≤
      2 * R⁻¹ := by
  have hleft := intervalIntegral_inv_sq_sub_le_inv_left
    (c := c) hR hRS
  have hright := intervalIntegral_inv_sq_sub_le_inv
    (c := c) hR hRS
  linarith

/-- A reciprocal pointwise norm bound on the right side of the minimizing
frequency integrates to at most the reciprocal inner radius. -/
theorem intervalIntegral_normSq_le_inv_right
    {F : ℝ → ℂ} (hF : Continuous F) {c R S : ℝ}
    (hR : 0 < R) (hRS : R ≤ S)
    (hbound : ∀ t ∈ Set.Icc (c + R) (c + S),
      Complex.normSq (F t) ≤ ((t - c) ^ 2)⁻¹) :
    (∫ t in c + R..c + S, Complex.normSq (F t)) ≤ R⁻¹ := by
  have hmajor : ContinuousOn (fun t : ℝ ↦ ((t - c) ^ 2)⁻¹)
      (Set.Icc (c + R) (c + S)) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.1])
  have hmajor' : ContinuousOn (fun t : ℝ ↦ ((t - c) ^ 2)⁻¹)
      (Set.uIcc (c + R) (c + S)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hmajor
  have hmono :
      (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
        ∫ t in c + R..c + S, ((t - c) ^ 2)⁻¹ := by
    exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := c + R) (b := c + S) (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hmajor'.intervalIntegrable hbound
  exact hmono.trans (intervalIntegral_inv_sq_sub_le_inv hR hRS)

/-- Left-side version of `intervalIntegral_normSq_le_inv_right`. -/
theorem intervalIntegral_normSq_le_inv_left
    {F : ℝ → ℂ} (hF : Continuous F) {c R S : ℝ}
    (hR : 0 < R) (hRS : R ≤ S)
    (hbound : ∀ t ∈ Set.Icc (c - S) (c - R),
      Complex.normSq (F t) ≤ ((t - c) ^ 2)⁻¹) :
    (∫ t in c - S..c - R, Complex.normSq (F t)) ≤ R⁻¹ := by
  have hmajor : ContinuousOn (fun t : ℝ ↦ ((t - c) ^ 2)⁻¹)
      (Set.Icc (c - S) (c - R)) := by
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.2])
  have hmajor' : ContinuousOn (fun t : ℝ ↦ ((t - c) ^ 2)⁻¹)
      (Set.uIcc (c - S) (c - R)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hmajor
  have hmono :
      (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
        ∫ t in c - S..c - R, ((t - c) ^ 2)⁻¹ := by
    exact intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := c - S) (b := c - R) (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hmajor'.intervalIntegrable hbound
  exact hmono.trans (intervalIntegral_inv_sq_sub_le_inv_left hR hRS)

/-- Central constant bound: an interval of radius `R` contributes at most
`2 R B²` to the square energy. -/
theorem intervalIntegral_normSq_le_two_mul_radius
    {F : ℝ → ℂ} (hF : Continuous F) {c R B : ℝ}
    (hR : 0 ≤ R) (hB : 0 ≤ B)
    (hbound : ∀ t ∈ Set.Icc (c - R) (c + R), ‖F t‖ ≤ B) :
    (∫ t in c - R..c + R, Complex.normSq (F t)) ≤ 2 * R * B ^ 2 := by
  have hmono :
      (∫ t in c - R..c + R, Complex.normSq (F t)) ≤
        ∫ _t in c - R..c + R, B ^ 2 := by
    apply intervalIntegral.integral_mono_on (μ := MeasureTheory.volume)
      (a := c - R) (b := c + R) (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      intervalIntegrable_const
    intro t ht
    change Complex.normSq (F t) ≤ B ^ 2
    rw [Complex.normSq_eq_norm_sq]
    exact (sq_le_sq₀ (norm_nonneg _) hB).2 (hbound t ht)
  calc
    (∫ t in c - R..c + R, Complex.normSq (F t)) ≤
        ∫ _t in c - R..c + R, B ^ 2 := hmono
    _ = 2 * R * B ^ 2 := by
      rw [intervalIntegral.integral_const]
      ring

/-- A reciprocal pointwise bound with an arbitrary numerator on the right
side of the minimizing frequency. -/
theorem intervalIntegral_normSq_le_mul_inv_right
    {F : ℝ → ℂ} (hF : Continuous F) {c R S K : ℝ}
    (hR : 0 < R) (hRS : R ≤ S)
    (hbound : ∀ t ∈ Set.Icc (c + R) (c + S),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹) :
    (∫ t in c + R..c + S, Complex.normSq (F t)) ≤ K ^ 2 * R⁻¹ := by
  have hmajor : ContinuousOn (fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (Set.Icc (c + R) (c + S)) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.1])
  have hmajor' : ContinuousOn (fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (Set.uIcc (c + R) (c + S)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hmajor
  have hmono :
      (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
        ∫ t in c + R..c + S, K ^ 2 * ((t - c) ^ 2)⁻¹ := by
    exact intervalIntegral.integral_mono_on (f := fun t : ℝ ↦
        Complex.normSq (F t)) (g := fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hmajor'.intervalIntegrable
      hbound
  calc
    (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
        ∫ t in c + R..c + S, K ^ 2 * ((t - c) ^ 2)⁻¹ := hmono
    _ = K ^ 2 * ∫ t in c + R..c + S, ((t - c) ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K ^ 2 * R⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral_inv_sq_sub_le_inv hR hRS) (sq_nonneg K)

/-- Left-side version of `intervalIntegral_normSq_le_mul_inv_right`. -/
theorem intervalIntegral_normSq_le_mul_inv_left
    {F : ℝ → ℂ} (hF : Continuous F) {c R S K : ℝ}
    (hR : 0 < R) (hRS : R ≤ S)
    (hbound : ∀ t ∈ Set.Icc (c - S) (c - R),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹) :
    (∫ t in c - S..c - R, Complex.normSq (F t)) ≤ K ^ 2 * R⁻¹ := by
  have hmajor : ContinuousOn (fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (Set.Icc (c - S) (c - R)) := by
    apply ContinuousOn.const_mul
    apply ContinuousOn.inv₀
    · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
    · intro t ht
      exact pow_ne_zero 2 (by linarith [ht.2])
  have hmajor' : ContinuousOn (fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (Set.uIcc (c - S) (c - R)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hmajor
  have hmono :
      (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
        ∫ t in c - S..c - R, K ^ 2 * ((t - c) ^ 2)⁻¹ := by
    exact intervalIntegral.integral_mono_on (f := fun t : ℝ ↦
        Complex.normSq (F t)) (g := fun t : ℝ ↦ K ^ 2 * ((t - c) ^ 2)⁻¹)
      (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hmajor'.intervalIntegrable
      hbound
  calc
    (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
        ∫ t in c - S..c - R, K ^ 2 * ((t - c) ^ 2)⁻¹ := hmono
    _ = K ^ 2 * ∫ t in c - S..c - R, ((t - c) ^ 2)⁻¹ := by
      rw [intervalIntegral.integral_const_mul]
    _ ≤ K ^ 2 * R⁻¹ := by
      exact mul_le_mul_of_nonneg_left
        (intervalIntegral_inv_sq_sub_le_inv_left hR hRS) (sq_nonneg K)

/-- Source-form near/medium energy package.  A constant central bound and
reciprocal-distance bounds on the two adjacent intervals contribute
`2 R B² + 2 K²/R` in total. -/
theorem nearMedium_intervalIntegral_normSq_le
    {F : ℝ → ℂ} (hF : Continuous F) {c R S B K : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) (hB : 0 ≤ B)
    (hcentral : ∀ t ∈ Set.Icc (c - R) (c + R), ‖F t‖ ≤ B)
    (hleft : ∀ t ∈ Set.Icc (c - S) (c - R),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹)
    (hright : ∀ t ∈ Set.Icc (c + R) (c + S),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹) :
    (∫ t in c - S..c - R, Complex.normSq (F t)) +
        (∫ t in c - R..c + R, Complex.normSq (F t)) +
        (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
      2 * R * B ^ 2 + 2 * K ^ 2 * R⁻¹ := by
  have hL := intervalIntegral_normSq_le_mul_inv_left hF hR hRS hleft
  have hC := intervalIntegral_normSq_le_two_mul_radius hF hR.le hB hcentral
  have hRt := intervalIntegral_normSq_le_mul_inv_right hF hR hRS hright
  linarith

/-- The balancing radius in the standard Halasz near/medium split. -/
def halaszCentralRadius (M : ℝ) : ℝ :=
  Real.exp M / (M + 1)

theorem halaszCentralRadius_pos {M : ℝ} (hM : 0 ≤ M) :
    0 < halaszCentralRadius M := by
  unfold halaszCentralRadius
  positivity

theorem halaszCentralRadius_inv {M : ℝ} (hM : 0 ≤ M) :
    (halaszCentralRadius M)⁻¹ = (M + 1) * Real.exp (-M) := by
  unfold halaszCentralRadius
  rw [Real.exp_neg]
  have hM1 : M + 1 ≠ 0 := by linarith
  have hexp : Real.exp M ≠ 0 := (Real.exp_pos M).ne'
  field_simp

/-- With the balanced radius `exp(M)/(M+1)`, the central Halasz bound
`K(M+1)exp(-M)` and the adjacent reciprocal bound `K/|t-t₀|`
contribute at most `4K²(M+1)exp(-M)` to the vertical square energy. -/
theorem nearMedium_intervalIntegral_normSq_le_halaszError
    {F : ℝ → ℂ} (hF : Continuous F) {c S M K : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K)
    (hRS : halaszCentralRadius M ≤ S)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M))
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      Complex.normSq (F t) ≤ K ^ 2 * ((t - c) ^ 2)⁻¹) :
    (∫ t in c - S..c - halaszCentralRadius M,
        Complex.normSq (F t)) +
        (∫ t in c - halaszCentralRadius M..
          c + halaszCentralRadius M, Complex.normSq (F t)) +
        (∫ t in c + halaszCentralRadius M..c + S,
          Complex.normSq (F t)) ≤
      4 * K ^ 2 * (M + 1) * Real.exp (-M) := by
  let R := halaszCentralRadius M
  let B := K * (M + 1) * Real.exp (-M)
  have hR : 0 < R := halaszCentralRadius_pos hM
  have hB : 0 ≤ B := by
    dsimp only [B]
    positivity
  have hbase := nearMedium_intervalIntegral_normSq_le hF hR hRS hB
    hcentral hleft hright
  suffices hscalar :
      2 * R * B ^ 2 + 2 * K ^ 2 * R⁻¹ =
        4 * K ^ 2 * (M + 1) * Real.exp (-M) by
    exact hbase.trans_eq hscalar
  dsimp only [R, B, halaszCentralRadius]
  rw [Real.exp_neg]
  have hM1 : M + 1 ≠ 0 := by linarith
  have hexp : Real.exp M ≠ 0 := (Real.exp_pos M).ne'
  field_simp
  ring

/-- The source Halasz error at any attained distance `M ≥ A` is dominated
by the uniform exponential envelope used by the quantitative MRT
consumer.  The harmless loss from exponent `1` to `1/2` makes the bound
monotone without requiring a lower threshold on `A`. -/
theorem halaszError_le_two_mul_archimedeanError
    {A M : ℝ} (hA : 0 ≤ A) (hAM : A ≤ M) :
    (M + 1) * Real.exp (-M) ≤
      2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) := by
  have hM : 0 ≤ M := hA.trans hAM
  have hexpLower : 1 + M / 2 ≤ Real.exp (M / 2) :=
    by simpa [add_comm] using Real.add_one_le_exp (M / 2)
  have hlin : M + 1 ≤ 2 * Real.exp (M / 2) := by
    nlinarith
  have hhalfPos : 0 < Real.exp (-M / 2) := Real.exp_pos _
  have hfactor : (M + 1) * Real.exp (-M / 2) ≤ 2 := by
    calc
      (M + 1) * Real.exp (-M / 2) ≤
          (2 * Real.exp (M / 2)) * Real.exp (-M / 2) :=
        mul_le_mul_of_nonneg_right hlin hhalfPos.le
      _ = 2 * (Real.exp (M / 2) * Real.exp (-M / 2)) := by ring
      _ = 2 := by rw [← Real.exp_add]; ring_nf; simp
  have hdecay : Real.exp (-M / 2) ≤ Real.exp (-A / 2) := by
    exact Real.exp_le_exp.mpr (by linarith)
  have hAone : 1 ≤ A + 1 := by linarith
  calc
    (M + 1) * Real.exp (-M) =
        ((M + 1) * Real.exp (-M / 2)) * Real.exp (-M / 2) := by
      rw [show Real.exp (-M) =
          Real.exp (-M / 2) * Real.exp (-M / 2) by
        rw [← Real.exp_add]
        congr 1
        ring]
      ring
    _ ≤ 2 * Real.exp (-M / 2) :=
      mul_le_mul_of_nonneg_right hfactor hhalfPos.le
    _ ≤ 2 * Real.exp (-A / 2) := by gcongr
    _ ≤ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) := by
      rw [show -(1 / 2 : ℝ) * A = -A / 2 by ring]
      have hdecayNonneg : 0 ≤ Real.exp (-A / 2) := (Real.exp_pos _).le
      nlinarith

/-- Right reciprocal-distance estimate with an additional uniform
pointwise error. -/
theorem intervalIntegral_normSq_le_mul_inv_add_const_right
    {F : ℝ → ℂ} (hF : Continuous F) {c R S K D : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) (hK : 0 ≤ K) (_hD : 0 ≤ D)
    (hbound : ∀ t ∈ Set.Icc (c + R) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
      2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R) := by
  let G : ℝ → ℝ := fun t ↦
    2 * K ^ 2 * ((t - c) ^ 2)⁻¹ + 2 * D ^ 2
  have hG : ContinuousOn G (Set.Icc (c + R) (c + S)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.const_mul
      apply ContinuousOn.inv₀
      · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (by linarith [ht.1])
    · exact continuousOn_const
  have hG' : ContinuousOn G (Set.uIcc (c + R) (c + S)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hG
  have hpoint : ∀ t ∈ Set.Icc (c + R) (c + S),
      Complex.normSq (F t) ≤ G t := by
    intro t ht
    have htc : 0 < t - c := by linarith [ht.1]
    have hmain := hbound t ht
    rw [abs_of_pos htc] at hmain
    have ha : 0 ≤ K * (t - c)⁻¹ := mul_nonneg hK (inv_nonneg.mpr htc.le)
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖F t‖ ^ 2 ≤ (K * (t - c)⁻¹ + D) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmain 2
      _ ≤ 2 * (K * (t - c)⁻¹) ^ 2 + 2 * D ^ 2 := by
        nlinarith [sq_nonneg (K * (t - c)⁻¹ - D)]
      _ = G t := by
        dsimp only [G]
        rw [mul_pow, inv_pow]
        ring
  have hmono :
      (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
        ∫ t in c + R..c + S, G t := by
    exact intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hG'.intervalIntegrable hpoint
  have hinv := intervalIntegral_inv_sq_sub_le_inv
    (c := c) hR hRS
  calc
    (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
        ∫ t in c + R..c + S, G t := hmono
    _ = 2 * K ^ 2 * (∫ t in c + R..c + S, ((t - c) ^ 2)⁻¹) +
        2 * D ^ 2 * (S - R) := by
      unfold G
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      · ring
      · exact (by
          have hcont : ContinuousOn
              (fun t : ℝ ↦ 2 * K ^ 2 * ((t - c) ^ 2)⁻¹)
              (Set.uIcc (c + R) (c + S)) := by
            rw [Set.uIcc_of_le (by linarith)]
            apply ContinuousOn.const_mul
            apply ContinuousOn.inv₀
            · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
            · intro t ht
              exact pow_ne_zero 2 (by linarith [ht.1])
          exact hcont.intervalIntegrable)
      · exact intervalIntegrable_const
    _ ≤ 2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R) := by
      gcongr

/-- Left reciprocal-distance estimate with an additional uniform
pointwise error. -/
theorem intervalIntegral_normSq_le_mul_inv_add_const_left
    {F : ℝ → ℂ} (hF : Continuous F) {c R S K D : ℝ}
    (hR : 0 < R) (hRS : R ≤ S) (hK : 0 ≤ K) (_hD : 0 ≤ D)
    (hbound : ∀ t ∈ Set.Icc (c - S) (c - R),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
      2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R) := by
  let G : ℝ → ℝ := fun t ↦
    2 * K ^ 2 * ((t - c) ^ 2)⁻¹ + 2 * D ^ 2
  have hG : ContinuousOn G (Set.Icc (c - S) (c - R)) := by
    apply ContinuousOn.add
    · apply ContinuousOn.const_mul
      apply ContinuousOn.inv₀
      · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
      · intro t ht
        exact pow_ne_zero 2 (by linarith [ht.2])
    · exact continuousOn_const
  have hG' : ContinuousOn G (Set.uIcc (c - S) (c - R)) := by
    rw [Set.uIcc_of_le (by linarith)]
    exact hG
  have hpoint : ∀ t ∈ Set.Icc (c - S) (c - R),
      Complex.normSq (F t) ≤ G t := by
    intro t ht
    have htc : t - c < 0 := by linarith [ht.2]
    have hmain := hbound t ht
    rw [abs_of_neg htc] at hmain
    have habs : 0 < -(t - c) := by linarith
    have ha : 0 ≤ K * (-(t - c))⁻¹ :=
      mul_nonneg hK (inv_nonneg.mpr habs.le)
    rw [Complex.normSq_eq_norm_sq]
    calc
      ‖F t‖ ^ 2 ≤ (K * (-(t - c))⁻¹ + D) ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) hmain 2
      _ ≤ 2 * (K * (-(t - c))⁻¹) ^ 2 + 2 * D ^ 2 := by
        nlinarith [sq_nonneg (K * (-(t - c))⁻¹ - D)]
      _ = G t := by
        dsimp only [G]
        rw [mul_pow, inv_pow, neg_sq]
        ring
  have hmono :
      (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
        ∫ t in c - S..c - R, G t := by
    exact intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable
        (μ := MeasureTheory.volume) _ _)
      hG'.intervalIntegrable hpoint
  have hinv := intervalIntegral_inv_sq_sub_le_inv_left
    (c := c) hR hRS
  calc
    (∫ t in c - S..c - R, Complex.normSq (F t)) ≤
        ∫ t in c - S..c - R, G t := hmono
    _ = 2 * K ^ 2 * (∫ t in c - S..c - R, ((t - c) ^ 2)⁻¹) +
        2 * D ^ 2 * (S - R) := by
      unfold G
      rw [intervalIntegral.integral_add,
        intervalIntegral.integral_const_mul,
        intervalIntegral.integral_const]
      · ring
      · exact (by
          have hcont : ContinuousOn
              (fun t : ℝ ↦ 2 * K ^ 2 * ((t - c) ^ 2)⁻¹)
              (Set.uIcc (c - S) (c - R)) := by
            rw [Set.uIcc_of_le (by linarith)]
            apply ContinuousOn.const_mul
            apply ContinuousOn.inv₀
            · exact ((continuous_id.sub continuous_const).pow 2).continuousOn
            · intro t ht
              exact pow_ne_zero 2 (by linarith [ht.2])
          exact hcont.intervalIntegrable)
      · exact intervalIntegrable_const
    _ ≤ 2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R) := by
      gcongr

/-- Balanced source Halasz energy with a uniform additive approximation
error `D`.  The main term remains `(M+1)e^{-M}` while the approximation
cost is exactly linear in the total frequency radius. -/
theorem nearMedium_intervalIntegral_normSq_le_halaszError_add
    {F : ℝ → ℂ} (hF : Continuous F) {c S M K D : ℝ}
    (hM : 0 ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hRS : halaszCentralRadius M ≤ S)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c - S..c - halaszCentralRadius M,
        Complex.normSq (F t)) +
        (∫ t in c - halaszCentralRadius M..
          c + halaszCentralRadius M, Complex.normSq (F t)) +
        (∫ t in c + halaszCentralRadius M..c + S,
          Complex.normSq (F t)) ≤
      8 * K ^ 2 * (M + 1) * Real.exp (-M) + 4 * S * D ^ 2 := by
  let R := halaszCentralRadius M
  let B := K * (M + 1) * Real.exp (-M)
  have hR : 0 < R := halaszCentralRadius_pos hM
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hL := intervalIntegral_normSq_le_mul_inv_add_const_left
    hF hR hRS hK hD hleft
  have hRt := intervalIntegral_normSq_le_mul_inv_add_const_right
    hF hR hRS hK hD hright
  have hC := intervalIntegral_normSq_le_two_mul_radius hF hR.le
    (add_nonneg hB hD) hcentral
  have hbalance :
      4 * R * B ^ 2 + 4 * K ^ 2 * R⁻¹ =
        8 * K ^ 2 * (M + 1) * Real.exp (-M) := by
    dsimp only [R, B, halaszCentralRadius]
    rw [Real.exp_neg]
    have hM1 : M + 1 ≠ 0 := by linarith
    have hexp : Real.exp M ≠ 0 := (Real.exp_pos M).ne'
    field_simp
    ring
  have hcenterExpand :
      2 * R * (B + D) ^ 2 ≤ 4 * R * B ^ 2 + 4 * R * D ^ 2 := by
    nlinarith [mul_nonneg hR.le (sq_nonneg (B - D))]
  calc
    (∫ t in c - S..c - R, Complex.normSq (F t)) +
        (∫ t in c - R..c + R, Complex.normSq (F t)) +
        (∫ t in c + R..c + S, Complex.normSq (F t)) ≤
      (2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R)) +
        (2 * R * (B + D) ^ 2) +
        (2 * K ^ 2 * R⁻¹ + 2 * D ^ 2 * (S - R)) := by
      linarith
    _ ≤ (4 * R * B ^ 2 + 4 * K ^ 2 * R⁻¹) + 4 * S * D ^ 2 := by
      nlinarith
    _ = 8 * K ^ 2 * (M + 1) * Real.exp (-M) + 4 * S * D ^ 2 := by
      rw [hbalance]

/-- Full centred-band form of the additive-error Halasz estimate.  If the
balancing radius lies inside the band, this is the three-band estimate
above.  If it lies outside, the central bound alone is stronger. -/
theorem centered_intervalIntegral_normSq_le_halaszError_add
    {F : ℝ → ℂ} (hF : Continuous F) {c S M K D : ℝ}
    (hS : 0 ≤ S) (hM : 0 ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c - S..c + S, Complex.normSq (F t)) ≤
      8 * K ^ 2 * (M + 1) * Real.exp (-M) + 4 * S * D ^ 2 := by
  let R := halaszCentralRadius M
  let B := K * (M + 1) * Real.exp (-M)
  have hR : 0 < R := halaszCentralRadius_pos hM
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  by_cases hRS : R ≤ S
  · have hbands := nearMedium_intervalIntegral_normSq_le_halaszError_add
      hF hM hK hD hRS hcentral hleft hright
    let G : ℝ → ℝ := fun t ↦ Complex.normSq (F t)
    have hG : Continuous G := Complex.continuous_normSq.comp hF
    have h₁ : IntervalIntegrable G MeasureTheory.volume (c - S) (c - R) :=
      hG.intervalIntegrable _ _
    have h₂ : IntervalIntegrable G MeasureTheory.volume (c - R) (c + R) :=
      hG.intervalIntegrable _ _
    have h₃ : IntervalIntegrable G MeasureTheory.volume (c + R) (c + S) :=
      hG.intervalIntegrable _ _
    have hsplit₁ := intervalIntegral.integral_add_adjacent_intervals h₁ h₂
    have hsplit₂ := intervalIntegral.integral_add_adjacent_intervals
      (h₁.trans h₂) h₃
    dsimp only [G, R] at hsplit₁ hsplit₂ hbands ⊢
    calc
      (∫ t in c - S..c + S, Complex.normSq (F t)) =
          (∫ t in c - S..c - halaszCentralRadius M,
            Complex.normSq (F t)) +
          (∫ t in c - halaszCentralRadius M..
            c + halaszCentralRadius M, Complex.normSq (F t)) +
          (∫ t in c + halaszCentralRadius M..c + S,
            Complex.normSq (F t)) := by
        rw [← hsplit₂, ← hsplit₁]
      _ ≤ 8 * K ^ 2 * (M + 1) * Real.exp (-M) +
          4 * S * D ^ 2 := hbands
  · have hSR : S ≤ R := le_of_not_ge hRS
    have hcentralS : ∀ t ∈ Set.Icc (c - S) (c + S),
        ‖F t‖ ≤ B + D := by
      intro t ht
      apply hcentral t
      constructor <;> linarith [ht.1, ht.2]
    have hcenter := intervalIntegral_normSq_le_two_mul_radius hF hS
      (add_nonneg hB hD) hcentralS
    have hcenterExpand :
        2 * S * (B + D) ^ 2 ≤ 4 * S * B ^ 2 + 4 * S * D ^ 2 := by
      nlinarith [mul_nonneg hS (sq_nonneg (B - D))]
    have hRB :
        R * B ^ 2 = K ^ 2 * (M + 1) * Real.exp (-M) := by
      dsimp only [R, B, halaszCentralRadius]
      rw [Real.exp_neg]
      have hM1 : M + 1 ≠ 0 := by linarith
      have hexp : Real.exp M ≠ 0 := (Real.exp_pos M).ne'
      field_simp
    have hSB : S * B ^ 2 ≤ R * B ^ 2 :=
      mul_le_mul_of_nonneg_right hSR (sq_nonneg B)
    have hmainNonneg :
        0 ≤ K ^ 2 * (M + 1) * Real.exp (-M) := by positivity
    calc
      (∫ t in c - S..c + S, Complex.normSq (F t)) ≤
          2 * S * (B + D) ^ 2 := hcenter
      _ ≤ 4 * S * B ^ 2 + 4 * S * D ^ 2 := hcenterExpand
      _ ≤ 4 * R * B ^ 2 + 4 * S * D ^ 2 := by gcongr
      _ = 4 * (R * B ^ 2) + 4 * S * D ^ 2 := by ring
      _ = 4 * (K ^ 2 * (M + 1) * Real.exp (-M)) +
          4 * S * D ^ 2 := by rw [hRB]
      _ ≤ 8 * K ^ 2 * (M + 1) * Real.exp (-M) +
          4 * S * D ^ 2 := by nlinarith

/-- The additive-error near/medium estimate in the form consumed by an
Archimedean nonpretentiousness lower bound.  The minimising distance may be
larger than the available level; its contribution is replaced uniformly by
the explicit decay at that level. -/
theorem nearMedium_intervalIntegral_normSq_le_archimedeanError_add
    {F : ℝ → ℂ} (hF : Continuous F) {c S M A K D : ℝ}
    (hA : 0 ≤ A) (hAM : A ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hRS : halaszCentralRadius M ≤ S)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c - S..c - halaszCentralRadius M,
        Complex.normSq (F t)) +
        (∫ t in c - halaszCentralRadius M..
          c + halaszCentralRadius M, Complex.normSq (F t)) +
        (∫ t in c + halaszCentralRadius M..c + S,
          Complex.normSq (F t)) ≤
      16 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * S * D ^ 2 := by
  have hM : 0 ≤ M := hA.trans hAM
  have hbase := nearMedium_intervalIntegral_normSq_le_halaszError_add
    hF hM hK hD hRS hcentral hleft hright
  have hdecay := halaszError_le_two_mul_archimedeanError hA hAM
  have hKsq : 0 ≤ 8 * K ^ 2 := by positivity
  calc
    (∫ t in c - S..c - halaszCentralRadius M,
        Complex.normSq (F t)) +
        (∫ t in c - halaszCentralRadius M..
          c + halaszCentralRadius M, Complex.normSq (F t)) +
        (∫ t in c + halaszCentralRadius M..c + S,
          Complex.normSq (F t)) ≤
      8 * K ^ 2 * (M + 1) * Real.exp (-M) + 4 * S * D ^ 2 := hbase
    _ ≤ 8 * K ^ 2 *
          (2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A)) +
        4 * S * D ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hdecay hKsq
      nlinarith
    _ = 16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * S * D ^ 2 := by
      ring

/-- Full centred-band Archimedean estimate, with no assumption that the
balancing radius fits inside the available frequency band. -/
theorem centered_intervalIntegral_normSq_le_archimedeanError_add
    {F : ℝ → ℂ} (hF : Continuous F) {c S M A K D : ℝ}
    (hS : 0 ≤ S) (hA : 0 ≤ A) (hAM : A ≤ M)
    (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in c - S..c + S, Complex.normSq (F t)) ≤
      16 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * S * D ^ 2 := by
  have hM : 0 ≤ M := hA.trans hAM
  have hbase := centered_intervalIntegral_normSq_le_halaszError_add
    hF hS hM hK hD hcentral hleft hright
  have hdecay := halaszError_le_two_mul_archimedeanError hA hAM
  have hKsq : 0 ≤ 8 * K ^ 2 := by positivity
  calc
    (∫ t in c - S..c + S, Complex.normSq (F t)) ≤
      8 * K ^ 2 * (M + 1) * Real.exp (-M) + 4 * S * D ^ 2 := hbase
    _ ≤ 8 * K ^ 2 *
          (2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A)) +
        4 * S * D ^ 2 := by
      have hscaled := mul_le_mul_of_nonneg_left hdecay hKsq
      nlinarith
    _ = 16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * S * D ^ 2 := by ring

/-- A symmetric vertical interval contained in the three Halasz bands has
the same quantitative Archimedean estimate.  This packages the endpoint
arithmetic needed when the minimizing frequency is not centred at zero. -/
theorem symmetric_intervalIntegral_normSq_le_archimedeanError_add
    {F : ℝ → ℂ} (hF : Continuous F) {c S T M A K D : ℝ}
    (hT : 0 ≤ T) (hcover : T + |c| ≤ S)
    (hA : 0 ≤ A) (hAM : A ≤ M) (hK : 0 ≤ K) (hD : 0 ≤ D)
    (hcentral : ∀ t ∈ Set.Icc
        (c - halaszCentralRadius M) (c + halaszCentralRadius M),
      ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hleft : ∀ t ∈ Set.Icc
        (c - S) (c - halaszCentralRadius M),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D)
    (hright : ∀ t ∈ Set.Icc
        (c + halaszCentralRadius M) (c + S),
      ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in -T..T, Complex.normSq (F t)) ≤
      16 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * S * D ^ 2 := by
  let G : ℝ → ℝ := fun t ↦ Complex.normSq (F t)
  have hS : 0 ≤ S := by
    have : 0 ≤ T + |c| := add_nonneg hT (abs_nonneg c)
    exact this.trans hcover
  have hleftEnd : c - S ≤ -T := by
    have hc : c ≤ |c| := le_abs_self c
    linarith
  have hrightEnd : T ≤ c + S := by
    have hc : -c ≤ |c| := neg_le_abs c
    linarith
  have hsymOrder : -T ≤ T := by linarith
  have hGcont : Continuous G := Complex.continuous_normSq.comp hF
  have hnonneg : ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Ioc (c - S) (c + S))), 0 ≤ G t :=
    Filter.Eventually.of_forall fun t ↦ Complex.normSq_nonneg _
  have hmono :
      (∫ t in -T..T, G t) ≤ ∫ t in c - S..c + S, G t :=
    intervalIntegral.integral_mono_interval hleftEnd hsymOrder hrightEnd
      hnonneg (hGcont.intervalIntegrable _ _)
  have hcentered := centered_intervalIntegral_normSq_le_archimedeanError_add
    hF hS hA hAM hK hD hcentral hleft hright
  dsimp only [G] at hmono
  calc
    (∫ t in -T..T, Complex.normSq (F t)) ≤
        ∫ t in c - S..c + S, Complex.normSq (F t) := hmono
    _ ≤ 16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * S * D ^ 2 := hcentered

/-- Local-frequency version of the symmetric estimate.  The Halasz
pointwise bounds are required only on the target interval, rather than on
the larger centred interval used to integrate the reciprocal majorant. -/
theorem symmetric_intervalIntegral_normSq_le_archimedeanError_add_of_local
    {F : ℝ → ℂ} (hF : Continuous F) {c T M A K D : ℝ}
    (hT : 0 ≤ T) (hA : 0 ≤ A) (hAM : A ≤ M)
    (hK : 0 ≤ K) (_hD : 0 ≤ D)
    (hcentral : ∀ t ∈ Set.Icc (-T) T,
      |t - c| ≤ halaszCentralRadius M →
        ‖F t‖ ≤ K * (M + 1) * Real.exp (-M) + D)
    (hside : ∀ t ∈ Set.Icc (-T) T,
      halaszCentralRadius M ≤ |t - c| →
        ‖F t‖ ≤ K * |t - c|⁻¹ + D) :
    (∫ t in -T..T, Complex.normSq (F t)) ≤
      32 * K ^ 2 * (A + 1) * Real.exp (-(1 / 2 : ℝ) * A) +
        4 * T * D ^ 2 := by
  let R := halaszCentralRadius M
  let B := K * (M + 1) * Real.exp (-M)
  let S := T + |c|
  let J : ℝ → ℝ := fun t ↦ K * (max R |t - c|)⁻¹
  let G : ℝ → ℂ := fun t ↦ (J t : ℂ)
  have hM : 0 ≤ M := hA.trans hAM
  have hR : 0 < R := halaszCentralRadius_pos hM
  have hS : 0 ≤ S := add_nonneg hT (abs_nonneg c)
  have hRinv : R⁻¹ = (M + 1) * Real.exp (-M) := by
    exact halaszCentralRadius_inv hM
  have hdenpos (t : ℝ) : 0 < max R |t - c| :=
    hR.trans_le (le_max_left _ _)
  have hJnonneg (t : ℝ) : 0 ≤ J t := by
    dsimp only [J]
    exact mul_nonneg hK (inv_nonneg.mpr (hdenpos t).le)
  have hdencont : Continuous (fun t : ℝ ↦ max R |t - c|) := by
    exact continuous_const.max (continuous_abs.comp
      (continuous_id.sub continuous_const))
  have hJcont : Continuous J := by
    dsimp only [J]
    exact continuous_const.mul
      (hdencont.inv₀ (fun t ↦ (hdenpos t).ne'))
  have hGcont : Continuous G := by
    dsimp only [G]
    exact Complex.continuous_ofReal.comp hJcont
  have hGnorm (t : ℝ) : ‖G t‖ = J t := by
    dsimp only [G]
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hJnonneg t)]
  have hpoint : ∀ t ∈ Set.Icc (-T) T, ‖F t‖ ≤ ‖G t‖ + D := by
    intro t ht
    rw [hGnorm]
    by_cases htc : |t - c| ≤ R
    · have hmax : max R |t - c| = R := max_eq_left htc
      rw [show J t = B by
        dsimp only [J, B]
        rw [hmax, hRinv]
        ring]
      exact hcentral t ht htc
    · have htc' : R ≤ |t - c| := le_of_not_ge htc
      have hmax : max R |t - c| = |t - c| := max_eq_right htc'
      rw [show J t = K * |t - c|⁻¹ by
        dsimp only [J]
        rw [hmax]]
      exact hside t ht htc'
  have henergyPoint : ∀ t ∈ Set.Icc (-T) T,
      Complex.normSq (F t) ≤
        2 * (Complex.normSq (G t) + D ^ 2) := by
    intro t ht
    rw [Complex.normSq_eq_norm_sq, Complex.normSq_eq_norm_sq]
    have hsquare : ‖F t‖ ^ 2 ≤ (‖G t‖ + D) ^ 2 :=
      pow_le_pow_left₀ (norm_nonneg _) (hpoint t ht) 2
    nlinarith [sq_nonneg (‖G t‖ - D)]
  have htarget :
      (∫ t in -T..T, Complex.normSq (F t)) ≤
        ∫ t in -T..T, 2 * (Complex.normSq (G t) + D ^ 2) := by
    exact intervalIntegral.integral_mono_on (by linarith)
      ((Complex.continuous_normSq.comp hF).intervalIntegrable _ _)
      ((continuous_const.mul
        ((Complex.continuous_normSq.comp hGcont).add
          continuous_const)).intervalIntegrable _ _)
      henergyPoint
  have hleftEnd : c - S ≤ -T := by
    dsimp only [S]
    have hc := le_abs_self c
    linarith
  have hrightEnd : T ≤ c + S := by
    dsimp only [S]
    have hc := neg_le_abs c
    linarith
  have hGnonneg : ∀ᵐ t ∂(MeasureTheory.volume.restrict
      (Set.Ioc (c - S) (c + S))), 0 ≤ Complex.normSq (G t) :=
    Filter.Eventually.of_forall fun t ↦ Complex.normSq_nonneg _
  have htargetCentered :
      (∫ t in -T..T, Complex.normSq (G t)) ≤
        ∫ t in c - S..c + S, Complex.normSq (G t) := by
    exact intervalIntegral.integral_mono_interval hleftEnd
      (by linarith) hrightEnd hGnonneg
      ((Complex.continuous_normSq.comp hGcont).intervalIntegrable _ _)
  have hcentralG : ∀ t ∈ Set.Icc (c - R) (c + R),
      ‖G t‖ ≤ K * (M + 1) * Real.exp (-M) := by
    intro t ht
    have habs : |t - c| ≤ R := by
      rw [abs_le]
      constructor <;> linarith [ht.1, ht.2]
    rw [hGnorm]
    dsimp only [J]
    rw [max_eq_left habs, hRinv]
    ring_nf
    exact le_rfl
  have hleftG : ∀ t ∈ Set.Icc (c - S) (c - R),
      ‖G t‖ ≤ K * |t - c|⁻¹ := by
    intro t ht
    have htc : t - c ≤ -R := by linarith [ht.2]
    have habs : R ≤ |t - c| := by
      rw [abs_of_nonpos (by linarith [hR])]
      linarith
    rw [hGnorm]
    dsimp only [J]
    rw [max_eq_right habs]
  have hrightG : ∀ t ∈ Set.Icc (c + R) (c + S),
      ‖G t‖ ≤ K * |t - c|⁻¹ := by
    intro t ht
    have htc : R ≤ t - c := by linarith [ht.1]
    have habs : R ≤ |t - c| := htc.trans (le_abs_self _)
    rw [hGnorm]
    dsimp only [J]
    rw [max_eq_right habs]
  have hmajor := centered_intervalIntegral_normSq_le_archimedeanError_add
    (c := c) (S := S) (M := M) (A := A) (K := K) (D := 0)
    hGcont hS hA hAM hK (show (0 : ℝ) ≤ 0 by norm_num)
      (by simpa only [R, add_zero] using hcentralG)
      (by simpa only [R, add_zero] using hleftG)
      (by simpa only [R, add_zero] using hrightG)
  have hsplit :
      (∫ t in -T..T, 2 * (Complex.normSq (G t) + D ^ 2)) =
        2 * (∫ t in -T..T, Complex.normSq (G t)) +
          4 * T * D ^ 2 := by
    calc
      (∫ t in -T..T, 2 * (Complex.normSq (G t) + D ^ 2)) =
          2 * (∫ t in -T..T, Complex.normSq (G t) + D ^ 2) := by
        rw [intervalIntegral.integral_const_mul]
      _ = 2 * ((∫ t in -T..T, Complex.normSq (G t)) +
          ∫ _t in -T..T, D ^ 2) := by
        congr 1
        exact intervalIntegral.integral_add
          ((Complex.continuous_normSq.comp hGcont).intervalIntegrable _ _)
          intervalIntegrable_const
      _ = 2 * (∫ t in -T..T, Complex.normSq (G t)) +
          4 * T * D ^ 2 := by
        rw [intervalIntegral.integral_const]
        ring
  have hcenterBound :
      (∫ t in -T..T, Complex.normSq (G t)) ≤
        16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) := by
    calc
      (∫ t in -T..T, Complex.normSq (G t)) ≤
          ∫ t in c - S..c + S, Complex.normSq (G t) := htargetCentered
      _ ≤ 16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * S * 0 ^ 2 := hmajor
      _ = 16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) := by ring
  rw [hsplit] at htarget
  calc
    (∫ t in -T..T, Complex.normSq (F t)) ≤
        2 * (∫ t in -T..T, Complex.normSq (G t)) +
          4 * T * D ^ 2 := htarget
    _ ≤ 2 * (16 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A)) + 4 * T * D ^ 2 := by
      gcongr
    _ = 32 * K ^ 2 * (A + 1) *
          Real.exp (-(1 / 2 : ℝ) * A) + 4 * T * D ^ 2 := by ring

end

end Erdos67
