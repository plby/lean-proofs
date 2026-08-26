import ErdosProblems.Erdos1002.GaussRareDigitQuantitative
import ErdosProblems.Erdos1002.GaussPrefixCylinderPartition

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact continued-fraction approximation coordinates and digit replacement

For `x` in the Gauss state space, put `x_n = T^n x`, let `a_{n+1}` be
the first digit of `x_n`, and recursively put

`y_0 = 0`, `y_{n+1} = 1 / (a_{n+1} + y_n)`.

The standard exact approximation coefficient is

`theta_n = 1 / (a_{n+1} + x_{n+1} + y_n)`.

This file makes that coordinate, including the backward variable, into an
explicit measurable function.  It then proves the deterministic replacement
`L * theta_n = L / a_{n+1} + O(L / a_{n+1}^2)` without suppressing the
terminating-rational exceptional set.  Finally, the quantitative one-digit
boundary-strip estimate turns window-membership replacement into an explicit
`O(L^-2)` one-event bound, uniformly in the time index.
-/

open Filter MeasureTheory Set
open scoped Topology ENNReal symmDiff

namespace Erdos1002

noncomputable section

/-! ## Orbit digits and the exact coordinate -/

/-- The `n`th point of the total Gauss orbit. -/
def gaussOrbit (n : ℕ) (x : ℝ) : ℝ :=
  (gaussMap^[n]) x

/-- The positive continued-fraction digit at time `n`, made total by
`Int.toNat` at terminating or off-state points. -/
def gaussDigitAt (n : ℕ) (x : ℝ) : ℕ :=
  gaussFirstDigitNat (gaussOrbit n x)

/-- The ratio of the two preceding continuants.  On a nonterminating prefix
this is `q_{n-1}/q_n`; the recursion is also a convenient total definition at
the null set of terminating points. -/
def gaussBackwardRatio : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, x => 1 / ((gaussDigitAt n x : ℝ) + gaussBackwardRatio n x)

/-- Exact continued-fraction approximation coefficient
`theta_n = 1/(a_{n+1}+x_{n+1}+y_n)`. -/
def gaussApproximationCoordinate (n : ℕ) (x : ℝ) : ℝ :=
  1 / ((gaussDigitAt n x : ℝ) + gaussOrbit (n + 1) x +
    gaussBackwardRatio n x)

/-- The digit-only surrogate `scale/a_{n+1}`. -/
def gaussScaledDigitCoordinate (scale : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  scale / (gaussDigitAt n x : ℝ)

/-- The scaled exact approximation coefficient `scale * theta_n`. -/
def gaussScaledApproximationCoordinate
    (scale : ℝ) (n : ℕ) (x : ℝ) : ℝ :=
  scale * gaussApproximationCoordinate n x

theorem gaussOrbit_zero (x : ℝ) : gaussOrbit 0 x = x := by
  simp [gaussOrbit]

theorem gaussOrbit_succ (n : ℕ) (x : ℝ) :
    gaussOrbit (n + 1) x = gaussMap (gaussOrbit n x) := by
  simp [gaussOrbit, Function.iterate_succ_apply']

theorem gaussOrbit_succ_mem_Ico (n : ℕ) (x : ℝ) :
    gaussOrbit (n + 1) x ∈ Ico (0 : ℝ) 1 := by
  rw [gaussOrbit_succ]
  exact ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩

theorem measurable_gaussOrbit (n : ℕ) : Measurable (gaussOrbit n) := by
  exact measurable_gaussMap.iterate n

theorem measurable_gaussFirstDigit : Measurable gaussFirstDigit := by
  exact Int.measurable_floor.comp measurable_inv

theorem measurable_gaussFirstDigitNat : Measurable gaussFirstDigitNat := by
  exact (measurable_of_countable Int.toNat).comp measurable_gaussFirstDigit

theorem measurable_gaussDigitAt (n : ℕ) : Measurable (gaussDigitAt n) := by
  exact measurable_gaussFirstDigitNat.comp (measurable_gaussOrbit n)

theorem measurable_gaussDigitAt_cast (n : ℕ) :
    Measurable fun x : ℝ => (gaussDigitAt n x : ℝ) := by
  exact (measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
    (measurable_gaussDigitAt n)

theorem measurable_gaussBackwardRatio (n : ℕ) :
    Measurable (gaussBackwardRatio n) := by
  induction n with
  | zero => exact measurable_const
  | succ n ih =>
      exact measurable_const.div ((measurable_gaussDigitAt_cast n).add ih)

theorem measurable_gaussApproximationCoordinate (n : ℕ) :
    Measurable (gaussApproximationCoordinate n) := by
  exact measurable_const.div
    (((measurable_gaussDigitAt_cast n).add (measurable_gaussOrbit (n + 1))).add
      (measurable_gaussBackwardRatio n))

theorem measurable_gaussScaledDigitCoordinate (scale : ℝ) (n : ℕ) :
    Measurable (gaussScaledDigitCoordinate scale n) := by
  exact measurable_const.div (measurable_gaussDigitAt_cast n)

theorem measurable_gaussScaledApproximationCoordinate (scale : ℝ) (n : ℕ) :
    Measurable (gaussScaledApproximationCoordinate scale n) := by
  exact measurable_const.mul (measurable_gaussApproximationCoordinate n)

/-! ## Removing the terminating exceptional set -/

/-- Away from the explicit prefix exceptional set, every requested orbit
point belongs to `(0,1]`. -/
theorem gaussOrbit_mem_Ioc_of_not_mem_exceptional
    {b k : ℕ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional b) (hk : k < b) :
    gaussOrbit k x ∈ Ioc (0 : ℝ) 1 := by
  have hne : gaussOrbit k x ≠ 0 := by
    intro hzero
    apply hex
    left
    refine ⟨hx, mem_iUnion.2 ⟨⟨k, hk⟩, ?_⟩⟩
    simpa only [mem_preimage, mem_singleton_iff, gaussOrbit] using! hzero
  cases k with
  | zero => simpa [gaussOrbit] using! hx
  | succ k =>
      have horbit := gaussOrbit_succ_mem_Ico k x
      exact ⟨lt_of_le_of_ne horbit.1 (Ne.symm hne), horbit.2.le⟩

theorem gaussDigitAt_pos_of_not_mem_exceptional
    {b k : ℕ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional b) (hk : k < b) :
    0 < gaussDigitAt k x := by
  exact gaussFirstDigitNat_pos
    (gaussOrbit_mem_Ioc_of_not_mem_exceptional hx hex hk)

/-- If the preceding digits are positive, the backward continuant ratio lies
in `[0,1]`.  This includes the base value `y_0=0`. -/
theorem gaussBackwardRatio_mem_Icc_of_digits_pos
    {n : ℕ} {x : ℝ} (hpos : ∀ k < n, 0 < gaussDigitAt k x) :
    gaussBackwardRatio n x ∈ Icc (0 : ℝ) 1 := by
  induction n with
  | zero => simp [gaussBackwardRatio]
  | succ n ih =>
      have hy := ih (fun k hk => hpos k (by omega))
      have hq : (1 : ℝ) ≤ gaussDigitAt n x := by
        exact_mod_cast hpos n (by omega)
      have hden : (1 : ℝ) ≤ (gaussDigitAt n x : ℝ) + gaussBackwardRatio n x := by
        linarith [hy.1]
      constructor
      · exact one_div_nonneg.mpr (le_trans (by norm_num) hden)
      · exact (div_le_one (lt_of_lt_of_le (by norm_num) hden)).2 hden

theorem gaussBackwardRatio_mem_Icc_of_not_mem_exceptional
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1)) :
    gaussBackwardRatio n x ∈ Icc (0 : ℝ) 1 := by
  apply gaussBackwardRatio_mem_Icc_of_digits_pos
  intro k hk
  exact gaussDigitAt_pos_of_not_mem_exceptional hx hex (by omega)

/-- The elementary complete-quotient identity
`x_n^-1 = a_{n+1} + x_{n+1}` with the natural-valued digit. -/
theorem gaussOrbit_inv_eq_digit_add_next
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1)) :
    (gaussOrbit n x)⁻¹ =
      (gaussDigitAt n x : ℝ) + gaussOrbit (n + 1) x := by
  have horbit := gaussOrbit_mem_Ioc_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hcastInt := gaussFirstDigitNat_cast horbit
  have hcastReal :
      (gaussFirstDigitNat (gaussOrbit n x) : ℝ) =
        (gaussFirstDigit (gaussOrbit n x) : ℝ) := by
    exact_mod_cast hcastInt
  calc
    (gaussOrbit n x)⁻¹ =
        (⌊(gaussOrbit n x)⁻¹⌋ : ℝ) + Int.fract (gaussOrbit n x)⁻¹ :=
      (Int.floor_add_fract _).symm
    _ = (gaussDigitAt n x : ℝ) + gaussOrbit (n + 1) x := by
      rw [gaussOrbit_succ]
      simp only [gaussDigitAt, gaussFirstDigitNat, gaussFirstDigit,
        gaussMap]
      exact congrArg₂ (· + ·) hcastReal.symm rfl

/-- Equivalent standard form `theta_n = x_n/(1+x_n*y_n)`.  This verifies
that the total definition above is the usual exact approximation
coefficient, rather than an abstract error proxy. -/
theorem gaussApproximationCoordinate_eq_orbit_div
    {n : ℕ} {x : ℝ} (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1)) :
    gaussApproximationCoordinate n x =
      gaussOrbit n x /
        (1 + gaussOrbit n x * gaussBackwardRatio n x) := by
  have horbit := gaussOrbit_mem_Ioc_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hy := gaussBackwardRatio_mem_Icc_of_not_mem_exceptional hx hex
  have hdecomp := gaussOrbit_inv_eq_digit_add_next hx hex
  have hx0 : gaussOrbit n x ≠ 0 := ne_of_gt horbit.1
  have hden :
      1 + gaussOrbit n x * gaussBackwardRatio n x ≠ 0 := by
    exact ne_of_gt (by
      have hmul : 0 ≤ gaussOrbit n x * gaussBackwardRatio n x :=
        mul_nonneg horbit.1.le hy.1
      linarith)
  simp only [gaussApproximationCoordinate]
  rw [← hdecomp]
  field_simp

/-! ## Deterministic digit replacement -/

/-- Algebraic core of the replacement: adding a remainder in `[0,2]` to a
positive digit changes its reciprocal by at most `2/q^2`. -/
theorem one_div_sub_one_div_add_le_two_div_sq
    {q r : ℝ} (hq : 0 < q) (hr0 : 0 ≤ r) (hr2 : r ≤ 2) :
    0 ≤ 1 / q - 1 / (q + r) ∧
      1 / q - 1 / (q + r) ≤ 2 / q ^ 2 := by
  have hqr : 0 < q + r := by linarith
  constructor
  · exact sub_nonneg.mpr (one_div_le_one_div_of_le hq (by linarith))
  · have heq : 1 / q - 1 / (q + r) = r / (q * (q + r)) := by
      field_simp
      ring
    rw [heq]
    have hqSq : 0 < q ^ 2 := sq_pos_of_pos hq
    have hden : q ^ 2 ≤ q * (q + r) := by
      nlinarith
    exact div_le_div₀ (by norm_num) hr2 hqSq (by simpa [pow_two] using! hden)

/-- Exact pointwise comparison on a nonterminating prefix.  Both the sign and
the explicit digit-dependent error are recorded. -/
theorem gaussScaledApproximation_digit_error
    {scale : ℝ} {n : ℕ} {x : ℝ}
    (hscale : 0 ≤ scale) (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1)) :
    0 ≤ gaussScaledDigitCoordinate scale n x -
        gaussScaledApproximationCoordinate scale n x ∧
      gaussScaledDigitCoordinate scale n x -
          gaussScaledApproximationCoordinate scale n x ≤
        2 * scale / (gaussDigitAt n x : ℝ) ^ 2 := by
  have hqNat := gaussDigitAt_pos_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hq : (0 : ℝ) < gaussDigitAt n x := by exact_mod_cast hqNat
  have hy := gaussBackwardRatio_mem_Icc_of_not_mem_exceptional hx hex
  have htail := gaussOrbit_succ_mem_Ico n x
  let r : ℝ := gaussOrbit (n + 1) x + gaussBackwardRatio n x
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [htail.1, hy.1]
  have hr2 : r ≤ 2 := by dsimp [r]; linarith [htail.2, hy.2]
  have hcore := one_div_sub_one_div_add_le_two_div_sq hq hr0 hr2
  have heq :
      gaussScaledDigitCoordinate scale n x -
          gaussScaledApproximationCoordinate scale n x =
        scale * (1 / (gaussDigitAt n x : ℝ) -
          1 / ((gaussDigitAt n x : ℝ) + r)) := by
    simp only [gaussScaledDigitCoordinate, gaussScaledApproximationCoordinate,
      gaussApproximationCoordinate, r]
    ring
  rw [heq]
  constructor
  · exact mul_nonneg hscale hcore.1
  · calc
      scale * (1 / (gaussDigitAt n x : ℝ) -
          1 / ((gaussDigitAt n x : ℝ) + r)) ≤
          scale * (2 / (gaussDigitAt n x : ℝ) ^ 2) :=
        mul_le_mul_of_nonneg_left hcore.2 hscale
      _ = 2 * scale / (gaussDigitAt n x : ℝ) ^ 2 := by ring

/-! ## Window mismatch is confined to endpoint strips -/

/-- Exact-value window at time `n`.  The initial state-space restriction is
kept explicit; terminating points are harmless because they form the
separately identified null exceptional set. -/
def gaussApproximationWindow
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) : Set ℝ :=
  Ioc (0 : ℝ) 1 ∩
    gaussScaledApproximationCoordinate scale n ⁻¹' Icc lower upper

/-- Digit-only window at time `n`, written as the pullback of the exact
one-digit event used by `GaussRareDigitQuantitative`. -/
def gaussDigitWindowAt
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) : Set ℝ :=
  Ioc (0 : ℝ) 1 ∩
    gaussOrbit n ⁻¹' scaledGaussFirstDigitWindow scale lower upper

theorem measurableSet_scaledGaussFirstDigitWindow
    (scale lower upper : ℝ) :
    MeasurableSet (scaledGaussFirstDigitWindow scale lower upper) := by
  have hfun : Measurable fun x : ℝ =>
      scale / (gaussFirstDigitNat x : ℝ) := by
    exact measurable_const.div
      ((measurable_of_countable (fun q : ℕ => (q : ℝ))).comp
        measurable_gaussFirstDigitNat)
  have heq :
      scaledGaussFirstDigitWindow scale lower upper =
        Ioc (0 : ℝ) 1 ∩
          (fun x : ℝ => scale / (gaussFirstDigitNat x : ℝ)) ⁻¹'
            Icc lower upper := by
    ext x
    simp only [scaledGaussFirstDigitWindow, mem_setOf_eq, mem_inter_iff,
      mem_preimage, mem_Icc]
  rw [heq]
  exact measurableSet_Ioc.inter (measurableSet_Icc.preimage hfun)

theorem measurableSet_scaledGaussFirstDigitBoundaryStrip
    (scale center width : ℝ) :
    MeasurableSet (scaledGaussFirstDigitBoundaryStrip scale center width) := by
  rw [scaledGaussFirstDigitBoundaryStrip_eq_window]
  exact measurableSet_scaledGaussFirstDigitWindow _ _ _

theorem measurableSet_gaussApproximationWindow
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) :
    MeasurableSet (gaussApproximationWindow scale n lower upper) := by
  exact measurableSet_Ioc.inter
    (measurableSet_Icc.preimage
      (measurable_gaussScaledApproximationCoordinate scale n))

theorem measurableSet_gaussDigitWindowAt
    (scale : ℝ) (n : ℕ) (lower upper : ℝ) :
    MeasurableSet (gaussDigitWindowAt scale n lower upper) := by
  exact measurableSet_Ioc.inter
    ((measurableSet_scaledGaussFirstDigitWindow scale lower upper).preimage
      (measurable_gaussOrbit n))

theorem mem_gaussApproximationWindow_iff
    {scale : ℝ} {n : ℕ} {lower upper x : ℝ} :
    x ∈ gaussApproximationWindow scale n lower upper ↔
      x ∈ Ioc (0 : ℝ) 1 ∧
        gaussScaledApproximationCoordinate scale n x ∈ Icc lower upper := by
  rfl

theorem mem_gaussDigitWindowAt_iff
    {scale : ℝ} {n : ℕ} {lower upper x : ℝ} :
    x ∈ gaussDigitWindowAt scale n lower upper ↔
      x ∈ Ioc (0 : ℝ) 1 ∧ gaussOrbit n x ∈ Ioc (0 : ℝ) 1 ∧
        gaussScaledDigitCoordinate scale n x ∈ Icc lower upper := by
  simp only [gaussDigitWindowAt, scaledGaussFirstDigitWindow,
    gaussScaledDigitCoordinate, gaussDigitAt, mem_inter_iff, mem_preimage,
    mem_setOf_eq, mem_Icc]

/-- A closed-window mismatch between an exact coordinate `e` and a larger
surrogate `d`, at distance at most `eta`, forces `d` into one of the two
endpoint strips. -/
theorem endpoint_strip_of_ordered_window_mismatch
    {e d lower upper eta : ℝ} (horder : e ≤ d) (hclose : d - e ≤ eta)
    (hmismatch :
      (e ∈ Icc lower upper ∧ d ∉ Icc lower upper) ∨
      (d ∈ Icc lower upper ∧ e ∉ Icc lower upper)) :
    |d - lower| ≤ eta ∨ |d - upper| ≤ eta := by
  rcases hmismatch with ⟨he, hd⟩ | ⟨hd, he⟩
  · right
    have hdlower : lower ≤ d := he.1.trans horder
    have hdupp : upper < d := by
      by_contra hnot
      exact hd ⟨hdlower, le_of_not_gt hnot⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hdupp.le)]
    linarith [he.2]
  · left
    have heupper : e ≤ upper := horder.trans hd.2
    have helower : e < lower := by
      by_contra hnot
      exact he ⟨le_of_not_gt hnot, heupper⟩
    rw [abs_of_nonneg (sub_nonneg.mpr hd.1)]
    linarith

/-- If either the exact or the digit coordinate lies in a window with upper
endpoint `upper`, a scale at least `4*upper` makes the replacement error
uniformly at most `8*upper^2/scale`. -/
theorem gaussScaledApproximation_digit_error_uniform
    {scale lower upper : ℝ} {n : ℕ} {x : ℝ}
    (hscale : 0 < scale) (hupper : 0 < upper)
    (hlarge : 4 * upper ≤ scale)
    (hx : x ∈ Ioc (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1))
    (hwindow :
      gaussScaledApproximationCoordinate scale n x ∈ Icc lower upper ∨
      gaussScaledDigitCoordinate scale n x ∈ Icc lower upper) :
    0 ≤ gaussScaledDigitCoordinate scale n x -
        gaussScaledApproximationCoordinate scale n x ∧
      gaussScaledDigitCoordinate scale n x -
          gaussScaledApproximationCoordinate scale n x ≤
        8 * upper ^ 2 / scale := by
  have hbase := gaussScaledApproximation_digit_error hscale.le hx hex
  have hqNat := gaussDigitAt_pos_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hq : (0 : ℝ) < gaussDigitAt n x := by exact_mod_cast hqNat
  have hy := gaussBackwardRatio_mem_Icc_of_not_mem_exceptional hx hex
  have htail := gaussOrbit_succ_mem_Ico n x
  let r : ℝ := gaussOrbit (n + 1) x + gaussBackwardRatio n x
  have hr0 : 0 ≤ r := by dsimp [r]; linarith [htail.1, hy.1]
  have hr2 : r ≤ 2 := by dsimp [r]; linarith [htail.2, hy.2]
  have hden : 0 < (gaussDigitAt n x : ℝ) + r := by linarith
  have hqLower : scale / (2 * upper) ≤ (gaussDigitAt n x : ℝ) := by
    rcases hwindow with hexact | hdigit
    · have hscaleDen :
          scale ≤ upper * ((gaussDigitAt n x : ℝ) + r) := by
        apply (div_le_iff₀ hden).1
        simpa only [gaussScaledApproximationCoordinate,
          gaussApproximationCoordinate, r, div_eq_mul_inv, one_mul,
          add_assoc] using! hexact.2
      apply (div_le_iff₀ (mul_pos (by norm_num) hupper)).2
      nlinarith
    · have hscaleDigit : scale ≤ upper * (gaussDigitAt n x : ℝ) := by
        exact (div_le_iff₀ hq).1 (by
          simpa only [gaussScaledDigitCoordinate] using! hdigit.2)
      apply (div_le_iff₀ (mul_pos (by norm_num) hupper)).2
      nlinarith
  have hlowerPos : 0 < scale / (2 * upper) :=
    div_pos hscale (mul_pos (by norm_num) hupper)
  have hsq : (scale / (2 * upper)) ^ 2 ≤
      (gaussDigitAt n x : ℝ) ^ 2 := by
    simpa only [pow_two] using!
      mul_self_le_mul_self hlowerPos.le hqLower
  have hcompare :
      2 * scale / (gaussDigitAt n x : ℝ) ^ 2 ≤
        2 * scale / (scale / (2 * upper)) ^ 2 := by
    exact div_le_div_of_nonneg_left (mul_nonneg (by norm_num) hscale.le)
      (sq_pos_of_pos hlowerPos) hsq
  refine ⟨hbase.1, hbase.2.trans (hcompare.trans_eq ?_)⟩
  field_simp
  ring

/-- Set-level deterministic replacement.  The only failures are terminating
prefixes and the two explicit digit-coordinate endpoint strips. -/
theorem symmDiff_gaussApproximationWindow_gaussDigitWindowAt_subset
    {scale lower upper : ℝ} {n : ℕ}
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    gaussApproximationWindow scale n lower upper ∆
        gaussDigitWindowAt scale n lower upper ⊆
      gaussPrefixExceptional (n + 1) ∪
        ((gaussOrbit n) ⁻¹'
            scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2) ∪
          (gaussOrbit n) ⁻¹'
            scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)) := by
  intro x hdiff
  by_cases hex : x ∈ gaussPrefixExceptional (n + 1)
  · exact Or.inl hex
  right
  have hmismatch := mem_symmDiff.mp hdiff
  have hx : x ∈ Ioc (0 : ℝ) 1 := by
    rcases hmismatch with h | h
    · exact (mem_gaussApproximationWindow_iff.mp h.1).1
    · exact (mem_gaussDigitWindowAt_iff.mp h.1).1
  have horbit := gaussOrbit_mem_Ioc_of_not_mem_exceptional
    (b := n + 1) (k := n) hx hex (by omega)
  have hlarge' : 4 * upper ≤ scale := by
    have hupper0 : 0 < upper := hlower.trans hupper
    have hlowle : lower ≤ upper := hupper.le
    have hmul : lower * scale ≤ upper * scale :=
      mul_le_mul_of_nonneg_right hlowle hscale.le
    nlinarith
  have hwindow :
      gaussScaledApproximationCoordinate scale n x ∈ Icc lower upper ∨
      gaussScaledDigitCoordinate scale n x ∈ Icc lower upper := by
    rcases hmismatch with h | h
    · exact Or.inl (mem_gaussApproximationWindow_iff.mp h.1).2
    · exact Or.inr (mem_gaussDigitWindowAt_iff.mp h.1).2.2
  have herr := gaussScaledApproximation_digit_error_uniform
    hscale (hlower.trans hupper) hlarge' hx hex hwindow
  have hcoordinateMismatch :
      (gaussScaledApproximationCoordinate scale n x ∈ Icc lower upper ∧
          gaussScaledDigitCoordinate scale n x ∉ Icc lower upper) ∨
        (gaussScaledDigitCoordinate scale n x ∈ Icc lower upper ∧
          gaussScaledApproximationCoordinate scale n x ∉ Icc lower upper) := by
    rcases hmismatch with h | h
    · left
      refine ⟨(mem_gaussApproximationWindow_iff.mp h.1).2, ?_⟩
      intro hd
      apply h.2
      exact mem_gaussDigitWindowAt_iff.mpr ⟨hx, horbit, hd⟩
    · right
      refine ⟨(mem_gaussDigitWindowAt_iff.mp h.1).2.2, ?_⟩
      intro he
      apply h.2
      exact mem_gaussApproximationWindow_iff.mpr ⟨hx, he⟩
  have hstrips := endpoint_strip_of_ordered_window_mismatch
    (sub_nonneg.mp herr.1) herr.2 hcoordinateMismatch
  rcases hstrips with hlowerStrip | hupperStrip
  · left
    exact ⟨horbit, by
      simpa only [gaussScaledDigitCoordinate, gaussDigitAt] using! hlowerStrip⟩
  · right
    exact ⟨horbit, by
      simpa only [gaussScaledDigitCoordinate, gaussDigitAt] using! hupperStrip⟩

/-! ## Uniform Gauss-measure bounds -/

/-- Gauss invariance at every time, in the real-valued measure interface used
by the quantitative strip estimates. -/
theorem gaussMeasure_real_gaussOrbit_preimage
    (n : ℕ) {s : Set ℝ} (hs : MeasurableSet s) :
    gaussMeasure.real ((gaussOrbit n) ⁻¹' s) = gaussMeasure.real s := by
  have hmap := congrArg (fun μ : Measure ℝ => μ s)
    (map_gaussMap_iterate_gaussMeasure n)
  change (Measure.map (gaussMap^[n]) gaussMeasure) s = gaussMeasure s at hmap
  rw [Measure.map_apply (measurable_gaussMap.iterate n) hs] at hmap
  simpa only [measureReal_def, gaussOrbit] using! congrArg ENNReal.toReal hmap

theorem gaussMeasure_real_gaussPrefixExceptional (b : ℕ) :
    gaussMeasure.real (gaussPrefixExceptional b) = 0 := by
  simp only [measureReal_def, gaussMeasure_gaussPrefixExceptional,
    ENNReal.toReal_zero]

/-- Quantitative replacement bound for one time index.  The estimate is
uniform in `n`, and the exceptional terminating prefix contributes exactly
zero. -/
theorem gaussMeasure_real_symmDiff_approximation_digit_window_le
    {scale lower upper : ℝ} (n : ℕ)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper) ≤
      (((2 * (8 * upper ^ 2) + 10 * lower ^ 2) / scale ^ 2) /
          Real.log 2) +
        (((2 * (8 * upper ^ 2) + 10 * upper ^ 2) / scale ^ 2) /
          Real.log 2) := by
  let E : Set ℝ := gaussPrefixExceptional (n + 1)
  let B₀ : Set ℝ :=
    (gaussOrbit n) ⁻¹'
      scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)
  let B₁ : Set ℝ :=
    (gaussOrbit n) ⁻¹'
      scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)
  have hsubset :
      gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper ⊆ E ∪ (B₀ ∪ B₁) := by
    simpa only [E, B₀, B₁] using!
      symmDiff_gaussApproximationWindow_gaussDigitWindowAt_subset
        hscale hlower hupper hlarge
  have hupper0 : 0 < upper := hlower.trans hupper
  have hwidth : 0 < 8 * upper ^ 2 := by positivity
  have hsizeUpper : 2 * (8 * upper ^ 2) ≤ upper * scale := by
    have hmul : lower * scale ≤ upper * scale :=
      mul_le_mul_of_nonneg_right hupper.le hscale.le
    nlinarith [hlarge.trans hmul]
  have hboundLower :=
    gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
      hscale hlower hwidth (by nlinarith [hlarge])
  have hboundUpper :=
    gaussMeasure_real_scaledGaussFirstDigitBoundaryStrip_le
      hscale hupper0 hwidth hsizeUpper
  have hB₀ :
      gaussMeasure.real B₀ =
        gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)) := by
    exact gaussMeasure_real_gaussOrbit_preimage n
      (measurableSet_scaledGaussFirstDigitBoundaryStrip _ _ _)
  have hB₁ :
      gaussMeasure.real B₁ =
        gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)) := by
    exact gaussMeasure_real_gaussOrbit_preimage n
      (measurableSet_scaledGaussFirstDigitBoundaryStrip _ _ _)
  calc
    gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper) ≤
        gaussMeasure.real (E ∪ (B₀ ∪ B₁)) :=
      measureReal_mono hsubset
    _ ≤ gaussMeasure.real E + gaussMeasure.real (B₀ ∪ B₁) :=
      measureReal_union_le E (B₀ ∪ B₁)
    _ ≤ gaussMeasure.real E +
        (gaussMeasure.real B₀ + gaussMeasure.real B₁) := by
      gcongr
      exact measureReal_union_le B₀ B₁
    _ = gaussMeasure.real B₀ + gaussMeasure.real B₁ := by
      rw [show gaussMeasure.real E = 0 by
        exact gaussMeasure_real_gaussPrefixExceptional (n + 1)]
      ring
    _ = gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale lower (8 * upper ^ 2)) +
        gaussMeasure.real
          (scaledGaussFirstDigitBoundaryStrip scale upper (8 * upper ^ 2)) := by
      rw [hB₀, hB₁]
    _ ≤ (((2 * (8 * upper ^ 2) + 10 * lower ^ 2) / scale ^ 2) /
          Real.log 2) +
        (((2 * (8 * upper ^ 2) + 10 * upper ^ 2) / scale ^ 2) /
          Real.log 2) := add_le_add hboundLower hboundUpper

/-- Simplified one-event form: window replacement costs at most
`52*upper^2/(scale^2 log 2)`. -/
theorem gaussMeasure_real_symmDiff_approximation_digit_window_le_simple
    {scale lower upper : ℝ} (n : ℕ)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper) ≤
      (52 * upper ^ 2 / scale ^ 2) / Real.log 2 := by
  have hraw := gaussMeasure_real_symmDiff_approximation_digit_window_le
    n hscale hlower hupper hlarge
  have hlowerSq : lower ^ 2 ≤ upper ^ 2 := by
    nlinarith [sq_nonneg (upper - lower), hlower, hupper]
  have hscaleSq : 0 < scale ^ 2 := sq_pos_of_pos hscale
  have hlog : 0 < Real.log 2 := Real.log_pos one_lt_two
  calc
    gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper) ≤
        (((2 * (8 * upper ^ 2) + 10 * lower ^ 2) / scale ^ 2) /
            Real.log 2) +
          (((2 * (8 * upper ^ 2) + 10 * upper ^ 2) / scale ^ 2) /
            Real.log 2) := hraw
    _ ≤ (52 * upper ^ 2 / scale ^ 2) / Real.log 2 := by
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hlog).2
      rw [← add_div]
      apply (div_le_div_iff_of_pos_right hscaleSq).2
      nlinarith

/-- Summing over any finite set of time indices retains the same explicit
`scale^-2` one-event cost. -/
theorem sum_gaussMeasure_real_symmDiff_approximation_digit_window_le
    {scale lower upper : ℝ} (indices : Finset ℕ)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale) :
    (∑ n ∈ indices,
      gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper)) ≤
      (indices.card : ℝ) * ((52 * upper ^ 2 / scale ^ 2) / Real.log 2) := by
  calc
    (∑ n ∈ indices,
      gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper)) ≤
        ∑ _n ∈ indices, ((52 * upper ^ 2 / scale ^ 2) / Real.log 2) := by
      exact Finset.sum_le_sum fun n _hn =>
        gaussMeasure_real_symmDiff_approximation_digit_window_le_simple
          n hscale hlower hupper hlarge
    _ = (indices.card : ℝ) *
        ((52 * upper ^ 2 / scale ^ 2) / Real.log 2) := by
      simp

/-- Factorial-moment time scale: for `O(scale)` possible locations, the sum
of all one-coordinate replacement probabilities is `O(scale^-1)`, hence
vanishes.  No independence or mixing hypothesis is used here. -/
theorem sum_gaussMeasure_real_symmDiff_approximation_digit_window_le_of_card
    {scale lower upper timeConstant : ℝ} (indices : Finset ℕ)
    (hscale : 0 < scale) (hlower : 0 < lower) (hupper : lower < upper)
    (hlarge : 16 * upper ^ 2 ≤ lower * scale)
    (hcard : (indices.card : ℝ) ≤ timeConstant * scale) :
    (∑ n ∈ indices,
      gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper)) ≤
      timeConstant * (52 * upper ^ 2) / (scale * Real.log 2) := by
  have hsum :=
    sum_gaussMeasure_real_symmDiff_approximation_digit_window_le
      indices hscale hlower hupper hlarge
  have hfactor : 0 ≤ (52 * upper ^ 2 / scale ^ 2) / Real.log 2 := by
    positivity
  calc
    (∑ n ∈ indices,
      gaussMeasure.real
        (gaussApproximationWindow scale n lower upper ∆
          gaussDigitWindowAt scale n lower upper)) ≤
        (indices.card : ℝ) *
          ((52 * upper ^ 2 / scale ^ 2) / Real.log 2) := hsum
    _ ≤ (timeConstant * scale) *
          ((52 * upper ^ 2 / scale ^ 2) / Real.log 2) :=
      mul_le_mul_of_nonneg_right hcard hfactor
    _ = timeConstant * (52 * upper ^ 2) / (scale * Real.log 2) := by
      field_simp

end

end Erdos1002
