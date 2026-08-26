import ErdosProblems.Erdos1002.GaussPrefixMobius
import ErdosProblems.Erdos1002.MarkedResonances

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Primitive resonance coordinates in exact Gauss-prefix form

This file closes the deterministic identification used in the marked
Poisson argument.  A primitive nearest-integer resonance in Legendre's
range is first identified with a genuine positive continued-fraction
prefix.  The determinant of that prefix then gives the exact signed error,
including its parity, its denominator, the logarithmically scaled
coordinate, and the torus mark.
-/

open Set

namespace Erdos1002

noncomputable section

/-- The marked point attached to a concrete positive Gauss prefix.  Its
three coordinates are written solely in terminal-continuant and exact
approximation-coordinate notation. -/
def gaussPrefixMarkedPoint (N n : ℕ) (w : PositiveDigitWord n)
    (x : ℝ) : ℝ × ℝ × ℝ :=
  (Real.log (cfTerminalDenominator w.1 : ℝ) / Real.log (N : ℝ),
    (-1 : ℝ) ^ n * Real.log (N : ℝ) *
      gaussApproximationCoordinate n x,
    Int.fract
      (((-1 : ℝ) ^ n * (N : ℝ) *
          gaussApproximationCoordinate n x) /
        cfTerminalDenominator w.1))

theorem measurable_gaussPrefixMarkedPoint
    (N n : ℕ) (w : PositiveDigitWord n) :
    Measurable (gaussPrefixMarkedPoint N n w) := by
  apply Measurable.prodMk measurable_const
  apply Measurable.prodMk
  · exact (measurable_const.mul measurable_const).mul
      (measurable_gaussApproximationCoordinate n)
  · exact (((measurable_const.mul measurable_const).mul
      (measurable_gaussApproximationCoordinate n)).div_const
        (cfTerminalDenominator w.1 : ℝ)).fract

/-- A nonterminating point of the open unit interval avoids every finite
prefix exceptional set. -/
theorem not_mem_gaussPrefixExceptional_of_nonterminating
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) (b : ℕ) :
    x ∉ gaussPrefixExceptional b := by
  intro hex
  rcases hex with hex | hxone
  · rcases hex with ⟨_hxIoc, hex⟩
    rcases mem_iUnion.mp hex with ⟨k, hk⟩
    exact hnonterm k.1 (by simpa only [mem_preimage, mem_singleton_iff] using! hk)
  · have : x = 1 := by simpa only [mem_singleton_iff] using! hxone
    exact hx.2.ne this

/-- Exact coordinate package for one literal primitive resonance.  No
continued-fraction numerator or denominator is left implicit: the original
nearest numerator and denominator are the terminal continuants of the
exhibited positive word. -/
theorem exists_gaussPrefix_coordinates_of_small_primitive_resonance
    {N p : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hp : 0 < p) (hprim : IsPrimitiveResonance p x)
    (hsmall : |resonanceDelta p x| < 1 / (2 * (p : ℝ)))
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) :
    ∃ (n : ℕ) (w : PositiveDigitWord n),
      x ∈ positivePrefixCylinder n w ∧
      p = cfTerminalDenominator w.1 ∧
      resonanceNumerator p x = (cfTerminalNumerator w.1 : ℤ) ∧
      resonanceDelta p x =
        (-1 : ℝ) ^ n * gaussApproximationCoordinate n x / p ∧
      scaledResonanceCoordinate N p x =
        (-1 : ℝ) ^ n * Real.log (N : ℝ) *
          gaussApproximationCoordinate n x ∧
      resonanceTorusCoordinate N p x =
        Int.fract
          (((-1 : ℝ) ^ n * (N : ℝ) *
              gaussApproximationCoordinate n x) / p) := by
  obtain ⟨n, w, hw, hpair⟩ :=
    exists_positivePrefix_resonancePair_eq_of_small hx hp hprim hsmall hnonterm
  have hlen : w.1.length = n := w.2.1
  have hpos : IsPositiveCFWord w.1 := w.2.2
  have hpDen : p = cfTerminalDenominator w.1 := by
    simpa [cfTerminalDenominator] using! congrArg Prod.snd hpair
  have hnumNat : (resonanceNumerator p x).natAbs =
      cfTerminalNumerator w.1 := by
    simpa [cfTerminalNumerator] using! congrArg Prod.fst hpair
  have hnumNonneg : 0 ≤ resonanceNumerator p x :=
    (resonanceNumerator_bounds_of_mem_unitInterval p hx).1
  have hnum : resonanceNumerator p x =
      (cfTerminalNumerator w.1 : ℤ) := by
    rw [Int.eq_natAbs_of_nonneg hnumNonneg]
    exact_mod_cast hnumNat
  have hex : x ∉ gaussPrefixExceptional (w.1.length + 1) :=
    not_mem_gaussPrefixExceptional_of_nonterminating hx hnonterm _
  have hterminal := terminalDenominator_mul_sub_terminalNumerator_eq
    hpos hx hex hw
  rw [gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_B_eq_terminalNumerator] at hterminal
  have hdelta : resonanceDelta p x =
      (-1 : ℝ) ^ n * gaussApproximationCoordinate n x / p := by
    unfold resonanceDelta
    rw [hnum, hpDen]
    simpa [hlen] using! hterminal
  have hpR : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne'
  have hscaled : scaledResonanceCoordinate N p x =
      (-1 : ℝ) ^ n * Real.log (N : ℝ) *
        gaussApproximationCoordinate n x := by
    rw [scaledResonanceCoordinate, hdelta]
    field_simp [hpR]
  have htorus : resonanceTorusCoordinate N p x =
      Int.fract
        (((-1 : ℝ) ^ n * (N : ℝ) *
            gaussApproximationCoordinate n x) / p) := by
    unfold resonanceTorusCoordinate
    rw [hdelta]
    congr 1
    ring
  exact ⟨n, w, hw, hpDen, hnum, hdelta, hscaled, htorus⟩

/-- Point-valued form of the forward coordinate package. -/
theorem exists_markedResonancePoint_eq_gaussPrefixMarkedPoint_of_small
    {N p : ℕ} {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hp : 0 < p) (hprim : IsPrimitiveResonance p x)
    (hsmall : |resonanceDelta p x| < 1 / (2 * (p : ℝ)))
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) :
    ∃ (n : ℕ) (w : PositiveDigitWord n),
      x ∈ positivePrefixCylinder n w ∧
      p = cfTerminalDenominator w.1 ∧
      markedResonancePoint N p x = gaussPrefixMarkedPoint N n w x := by
  obtain ⟨n, w, hw, hpDen, _hnum, _hdelta, hscaled, htorus⟩ :=
    exists_gaussPrefix_coordinates_of_small_primitive_resonance
      (N := N) hx hp hprim hsmall hnonterm
  refine ⟨n, w, hw, hpDen, ?_⟩
  rw [hpDen] at hscaled htorus
  unfold markedResonancePoint gaussPrefixMarkedPoint resonanceTimeCoordinate
  rw [hpDen, hscaled, htorus]

/-- The exact Gauss approximation coefficient is strictly positive on a
nonterminating positive prefix. -/
theorem gaussApproximationCoordinate_pos_of_mem_positivePrefix
    {n : ℕ} (w : PositiveDigitWord n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1))
    (hw : x ∈ positivePrefixCylinder n w) :
    0 < gaussApproximationCoordinate n x := by
  have htheta := gaussApproximationCoordinate_eq_gaussPrefixMobius
    w.2.2 hx (by simpa [w.2.1] using! hex) hw
  rw [w.2.1] at htheta
  have hy := gaussOrbit_mem_Ioc_of_not_mem_exceptional
    (b := n + 1) (k := n)
    (⟨hx.1, hx.2.le⟩ : x ∈ Ioc (0 : ℝ) 1) hex (by omega)
  have hD : (0 : ℝ) < (gaussPrefixMobius w.1).D := by
    exact_mod_cast gaussPrefixMobius_D_pos w.2.2
  have hC : (0 : ℝ) ≤ (gaussPrefixMobius w.1).C := by positivity
  have hmul : (0 : ℝ) ≤
      (gaussPrefixMobius w.1).C * gaussOrbit n x :=
    mul_nonneg hC hy.1.le
  have hden : (0 : ℝ) <
      (gaussPrefixMobius w.1).C * gaussOrbit n x +
        (gaussPrefixMobius w.1).D :=
    add_pos_of_nonneg_of_pos hmul hD
  rw [htheta]
  exact div_pos (mul_pos hD hy.1) hden

/-- Converse deterministic identification.  If a positive-prefix
approximation coefficient is below `1/2`, then its terminal rational is
literally the nearest primitive resonance.  The conclusion includes the
Legendre-range inequality used in the forward direction, so the two
descriptions agree without an unstated convention. -/
theorem terminalPrefix_is_small_primitive_resonance
    {n : ℕ} (w : PositiveDigitWord n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1))
    (hw : x ∈ positivePrefixCylinder n w)
    (hthetaSmall : gaussApproximationCoordinate n x < (1 : ℝ) / 2) :
    resonanceNumerator (cfTerminalDenominator w.1) x =
        (cfTerminalNumerator w.1 : ℤ) ∧
      IsPrimitiveResonance (cfTerminalDenominator w.1) x ∧
      resonanceDelta (cfTerminalDenominator w.1) x =
        (-1 : ℝ) ^ n * gaussApproximationCoordinate n x /
          cfTerminalDenominator w.1 ∧
      |resonanceDelta (cfTerminalDenominator w.1) x| <
        1 / (2 * (cfTerminalDenominator w.1 : ℝ)) := by
  have hpos : IsPositiveCFWord w.1 := w.2.2
  have hlen : w.1.length = n := w.2.1
  have hthetaPos :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix w hx hex hw
  have hDnat : 0 < cfTerminalDenominator w.1 :=
    cfTerminalDenominator_pos hpos
  have hD : (0 : ℝ) < cfTerminalDenominator w.1 := by
    exact_mod_cast hDnat
  have hDOne : (1 : ℝ) ≤ cfTerminalDenominator w.1 := by
    exact_mod_cast (Nat.succ_le_iff.mpr hDnat)
  have hterminal := terminalDenominator_mul_sub_terminalNumerator_eq
    hpos hx (by simpa [hlen] using! hex) hw
  rw [gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_B_eq_terminalNumerator, hlen] at hterminal
  have habsEndpoint :
      |(cfTerminalDenominator w.1 : ℝ) * x -
          (cfTerminalNumerator w.1 : ℝ)| =
        gaussApproximationCoordinate n x /
          cfTerminalDenominator w.1 := by
    rw [hterminal, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_pos hthetaPos, abs_of_pos hD]
  have hnearest :
      |(cfTerminalDenominator w.1 : ℝ) * x -
          (((cfTerminalNumerator w.1 : ℕ) : ℤ) : ℝ)| <
        (1 : ℝ) / 2 := by
    norm_cast
    rw [habsEndpoint]
    exact lt_of_le_of_lt (div_le_self hthetaPos.le hDOne) hthetaSmall
  have hnum : resonanceNumerator (cfTerminalDenominator w.1) x =
      (cfTerminalNumerator w.1 : ℤ) :=
    resonanceNumerator_eq_of_abs_sub_lt_half hnearest
  have hprim : IsPrimitiveResonance (cfTerminalDenominator w.1) x := by
    unfold IsPrimitiveResonance
    rw [hnum]
    simpa using! cfTerminalPair_coprime w.1
  have hdelta : resonanceDelta (cfTerminalDenominator w.1) x =
      (-1 : ℝ) ^ n * gaussApproximationCoordinate n x /
        cfTerminalDenominator w.1 := by
    unfold resonanceDelta
    rw [hnum]
    simpa using! hterminal
  have hsmall : |resonanceDelta (cfTerminalDenominator w.1) x| <
      1 / (2 * (cfTerminalDenominator w.1 : ℝ)) := by
    rw [hdelta, abs_div, abs_mul, abs_pow, abs_neg, abs_one,
      one_pow, one_mul, abs_of_pos hthetaPos, abs_of_pos hD]
    calc
      gaussApproximationCoordinate n x /
          (cfTerminalDenominator w.1 : ℝ) <
          ((1 : ℝ) / 2) / cfTerminalDenominator w.1 :=
        (div_lt_div_iff_of_pos_right hD).2 hthetaSmall
      _ = 1 / (2 * (cfTerminalDenominator w.1 : ℝ)) := by ring
  exact ⟨hnum, hprim, hdelta, hsmall⟩

/-- Point-valued form of the converse identification. -/
theorem markedResonancePoint_terminalDenominator_eq_gaussPrefixMarkedPoint
    {N n : ℕ} (w : PositiveDigitWord n) {x : ℝ}
    (hx : x ∈ Ioo (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (n + 1))
    (hw : x ∈ positivePrefixCylinder n w)
    (hthetaSmall : gaussApproximationCoordinate n x < (1 : ℝ) / 2) :
    markedResonancePoint N (cfTerminalDenominator w.1) x =
      gaussPrefixMarkedPoint N n w x := by
  obtain ⟨_hnum, _hprim, hdelta, _hsmall⟩ :=
    terminalPrefix_is_small_primitive_resonance
      w hx hex hw hthetaSmall
  have hp : (0 : ℝ) < cfTerminalDenominator w.1 := by
    exact_mod_cast cfTerminalDenominator_pos w.2.2
  have hpne : (cfTerminalDenominator w.1 : ℝ) ≠ 0 := hp.ne'
  have hscaled :
      scaledResonanceCoordinate N (cfTerminalDenominator w.1) x =
        (-1 : ℝ) ^ n * Real.log (N : ℝ) *
          gaussApproximationCoordinate n x := by
    rw [scaledResonanceCoordinate, hdelta]
    field_simp [hpne]
  have htorus :
      resonanceTorusCoordinate N (cfTerminalDenominator w.1) x =
        Int.fract
          (((-1 : ℝ) ^ n * (N : ℝ) *
              gaussApproximationCoordinate n x) /
            cfTerminalDenominator w.1) := by
    unfold resonanceTorusCoordinate
    rw [hdelta]
    congr 1
    ring
  unfold markedResonancePoint gaussPrefixMarkedPoint resonanceTimeCoordinate
  rw [hscaled, htorus]

/-- Two nonterminating positive prefixes of the same point cannot represent
the same reduced terminal rational at different depths.  The determinant
identity supplies the missing parity: its error is positive at even depth
and negative at odd depth. -/
theorem positivePrefix_depth_eq_of_terminalPair_eq
    {n m : ℕ} (w : PositiveDigitWord n) (v : PositiveDigitWord m)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hexw : x ∉ gaussPrefixExceptional (n + 1))
    (hexv : x ∉ gaussPrefixExceptional (m + 1))
    (hw : x ∈ positivePrefixCylinder n w)
    (hv : x ∈ positivePrefixCylinder m v)
    (hpair : cfTerminalPair w.1 = cfTerminalPair v.1) :
    n = m := by
  have hthetaW :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix w hx hexw hw
  have hthetaV :=
    gaussApproximationCoordinate_pos_of_mem_positivePrefix v hx hexv hv
  have hDWnat : 0 < cfTerminalDenominator w.1 :=
    cfTerminalDenominator_pos w.2.2
  have hDW : (0 : ℝ) < cfTerminalDenominator w.1 := by
    exact_mod_cast hDWnat
  have hnum : cfTerminalNumerator w.1 = cfTerminalNumerator v.1 := by
    simpa [cfTerminalNumerator] using! congrArg Prod.fst hpair
  have hden : cfTerminalDenominator w.1 = cfTerminalDenominator v.1 := by
    simpa [cfTerminalDenominator] using! congrArg Prod.snd hpair
  have herrW := terminalDenominator_mul_sub_terminalNumerator_eq
    w.2.2 hx (by simpa [w.2.1] using! hexw) hw
  have herrV := terminalDenominator_mul_sub_terminalNumerator_eq
    v.2.2 hx (by simpa [v.2.1] using! hexv) hv
  rw [gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_B_eq_terminalNumerator, w.2.1] at herrW
  rw [gaussPrefixMobius_D_eq_terminalDenominator,
    gaussPrefixMobius_B_eq_terminalNumerator, v.2.1,
    ← hnum, ← hden] at herrV
  have hparity : n % 2 = m % 2 := by
    rcases Nat.even_or_odd n with hn | hn
    · rcases Nat.even_or_odd m with hm | hm
      · have hn0 : n % 2 = 0 :=
          Nat.not_odd_iff.mp (Nat.not_odd_iff_even.mpr hn)
        have hm0 : m % 2 = 0 :=
          Nat.not_odd_iff.mp (Nat.not_odd_iff_even.mpr hm)
        rw [hn0, hm0]
      · have hleftPos : 0 <
            (cfTerminalDenominator w.1 : ℝ) * x -
              cfTerminalNumerator w.1 := by
          rw [herrW, hn.neg_one_pow, one_mul]
          exact div_pos hthetaW hDW
        have hleftNeg :
            (cfTerminalDenominator w.1 : ℝ) * x -
                cfTerminalNumerator w.1 < 0 := by
          rw [herrV, hm.neg_one_pow, neg_one_mul]
          exact div_neg_of_neg_of_pos (neg_neg_of_pos hthetaV) hDW
        linarith
    · rcases Nat.even_or_odd m with hm | hm
      · have hleftNeg :
            (cfTerminalDenominator w.1 : ℝ) * x -
                cfTerminalNumerator w.1 < 0 := by
          rw [herrW, hn.neg_one_pow, neg_one_mul]
          exact div_neg_of_neg_of_pos (neg_neg_of_pos hthetaW) hDW
        have hleftPos : 0 <
            (cfTerminalDenominator w.1 : ℝ) * x -
              cfTerminalNumerator w.1 := by
          rw [herrV, hm.neg_one_pow, one_mul]
          exact div_pos hthetaV hDW
        linarith
      · rw [Nat.odd_iff.mp hn, Nat.odd_iff.mp hm]
  have hwordParity : w.1.length % 2 = v.1.length % 2 := by
    simpa [w.2.1, v.2.1] using! hparity
  have hword := eq_of_cfTerminalPair_eq_of_length_mod_two_eq
    w.2.2 v.2.2 hpair hwordParity
  have hlength := congrArg List.length hword
  simpa [w.2.1, v.2.1] using! hlength

end

end Erdos1002
