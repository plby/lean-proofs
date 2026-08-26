import ErdosProblems.Erdos1002.ContinuedFractionCylinderCounting
import ErdosProblems.Erdos1002.ContinuedFractions
import ErdosProblems.Erdos1002.ResonantConvergents

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Gauss-prefix endpoints are the ordinary convergents

The marked-resonance argument recognizes a sufficiently small primitive
rational cell as a continued-fraction convergent by Legendre's theorem.  The
cylinder argument, on the other hand, is phrased in terms of finite positive
Gauss words.  This file proves the missing literal identification between
those two conventions.
-/

open Set

namespace Erdos1002

noncomputable section

/-- Splitting off the integral part does not change the positive-depth tail
of the recursively defined rational convergents.  The statement also covers
depth zero. -/
theorem realConvergent_eq_floor_add_fractConvergent
    (x : ℝ) (n : ℕ) :
    x.convergent n = (⌊x⌋ : ℚ) + (Int.fract x).convergent n := by
  cases n with
  | zero =>
      simp only [Real.convergent_zero]
      have hfloor : ⌊Int.fract x⌋ = 0 :=
        Int.floor_eq_zero_iff.mpr ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
      rw [hfloor]
      simp
  | succ n =>
      rw [Real.convergent_succ, Real.convergent_succ]
      have hfloor : ⌊Int.fract x⌋ = 0 :=
        Int.floor_eq_zero_iff.mpr ⟨Int.fract_nonneg x, Int.fract_lt_one x⟩
      rw [hfloor, Int.fract_fract]
      simp

/-- For a point in the half-open unit interval, the convergent whose depth is
the length of a positive Gauss word is exactly the endpoint obtained by
sending the remaining tail to zero through the corresponding inverse
branches. -/
theorem cast_convergent_eq_gaussInverseWord_zero
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    ((x.convergent w.length : ℚ) : ℝ) = gaussInverseWord w 0 := by
  induction w generalizing x with
  | nil =>
      have hfloor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
      simp [Real.convergent_zero, gaussInverseWord, hfloor]
  | cons q w ih =>
      have hq : 0 < q := hpos q (by simp)
      have htailPos : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hxFirst : x ∈ firstDigitCylinder q := hw.1
      have hxUnit : x ∈ Ioc (0 : ℝ) 1 :=
        firstDigitCylinder_subset_unit q hq hxFirst
      have hdigit : gaussFirstDigit x = (q : ℤ) :=
        (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hxUnit q hq).2 hxFirst
      have hfloorInv : ⌊x⁻¹⌋ = (q : ℤ) := by
        simpa only [gaussFirstDigit] using! hdigit
      have hfract : Int.fract x = x :=
        Int.fract_eq_self.mpr hx
      have hfloor : ⌊x⌋ = 0 := Int.floor_eq_zero_iff.mpr hx
      have hy : gaussMap x ∈ Ico (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      have htail : gaussMap x ∈ gaussHalfOpenPrefixCylinder w := hw.2
      have ih' := ih htailPos hy htail
      have hshift :
          x⁻¹.convergent w.length =
            (q : ℚ) + (gaussMap x).convergent w.length := by
        rw [realConvergent_eq_floor_add_fractConvergent]
        rw [hfloorInv]
        rfl
      simp only [List.length_cons, Real.convergent_succ, hfract, hshift, hfloor,
        gaussInverseWord, gaussInverseBranch]
      push_cast
      rw [ih']
      simp [one_div]

/-- The same identity written with the terminal coprime numerator and
denominator used by the cylinder-counting layer. -/
theorem cast_convergent_eq_cfTerminalRatio
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    ((x.convergent w.length : ℚ) : ℝ) =
      (cfTerminalNumerator w : ℝ) / cfTerminalDenominator w := by
  rw [cast_convergent_eq_gaussInverseWord_zero hpos hx hw]
  exact gaussInverseWord_zero_eq_cfTerminalRatio hpos

/-- Two nonnegative reduced fractions with positive denominators and equal
real values have identical numerator--denominator pairs. -/
theorem natPair_eq_of_coprime_ratio_eq
    {a b c d : ℕ} (hb : 0 < b) (hd : 0 < d)
    (hab : a.Coprime b) (hcd : c.Coprime d)
    (hratio : (a : ℝ) / b = (c : ℝ) / d) :
    (a, b) = (c, d) := by
  have hcrossR : (a : ℝ) * d = (c : ℝ) * b :=
    (div_eq_div_iff (by exact_mod_cast hb.ne')
      (by exact_mod_cast hd.ne')).1 hratio
  have hcross : a * d = c * b := by exact_mod_cast hcrossR
  have hb_dvd_d : b ∣ d := by
    apply (hab.symm.dvd_mul_left).1
    rw [hcross]
    exact ⟨c, by simp [Nat.mul_comm]⟩
  have hd_dvd_b : d ∣ b := by
    apply (hcd.symm.dvd_mul_left).1
    rw [← hcross]
    exact ⟨a, by simp [Nat.mul_comm]⟩
  have hbd : b = d := Nat.dvd_antisymm hb_dvd_d hd_dvd_b
  have hac : a = c := by
    apply Nat.mul_right_cancel hb
    simpa [hbd] using! hcross
  exact Prod.ext hac hbd

/-- If a primitive nearest-cell rational is the convergent selected by a
positive prefix cylinder, its literal denominator and unsigned numerator are
the terminal continuants of that prefix. -/
theorem resonancePair_eq_cfTerminalPair_of_prefix_convergent
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {p : ℕ} (hp : 0 < p) (hprim : IsPrimitiveResonance p x)
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w)
    (hconv :
      (resonanceNumerator p x : ℚ) / (p : ℚ) =
        x.convergent w.length) :
    ((resonanceNumerator p x).natAbs, p) = cfTerminalPair w := by
  have hbounds := resonanceNumerator_bounds_of_mem_unitInterval p hx
  have hnumCast :
      (((resonanceNumerator p x).natAbs : ℕ) : ℝ) =
        (resonanceNumerator p x : ℝ) := by
    rw [← Int.cast_natCast]
    rw [Int.natAbs_of_nonneg hbounds.1]
  have hconvR := congrArg (fun z : ℚ ↦ (z : ℝ)) hconv
  have hendpoint := cast_convergent_eq_cfTerminalRatio hpos
    (⟨hx.1.le, hx.2⟩ : x ∈ Ico (0 : ℝ) 1) hw
  have hratio :
      (((resonanceNumerator p x).natAbs : ℕ) : ℝ) / p =
        (cfTerminalNumerator w : ℝ) / cfTerminalDenominator w := by
    rw [hnumCast]
    calc
      (resonanceNumerator p x : ℝ) / (p : ℝ) =
          ((x.convergent w.length : ℚ) : ℝ) := by
            simpa using! hconvR
      _ = (cfTerminalNumerator w : ℝ) / cfTerminalDenominator w :=
        hendpoint
  have htermPos : 0 < cfTerminalDenominator w :=
    cfTerminalDenominator_pos hpos
  apply natPair_eq_of_coprime_ratio_eq hp htermPos hprim
    (cfTerminalPair_coprime w)
  exact hratio

/-- Outside the terminating continued-fraction exceptional set, every
primitive resonance in Legendre's range is represented by an actual positive
Gauss prefix whose terminal denominator is the original denominator.  This
is the bridge consumed by the marked-cylinder argument. -/
theorem exists_positivePrefix_resonancePair_eq_of_small
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    {p : ℕ} (hp : 0 < p) (hprim : IsPrimitiveResonance p x)
    (hsmall : |resonanceDelta p x| < 1 / (2 * (p : ℝ)))
    (hnonterm : ∀ k : ℕ, (gaussMap^[k]) x ≠ 0) :
    ∃ (n : ℕ) (w : PositiveDigitWord n),
      x ∈ positivePrefixCylinder n w ∧
        ((resonanceNumerator p x).natAbs, p) = cfTerminalPair w.1 := by
  obtain ⟨n, hconv⟩ :=
    resonance_eq_convergent_of_small x p hp hprim hsmall
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  obtain ⟨w, hw⟩ := exists_positiveDigitWord_of_no_early_zero hxIco
    (fun k _hk ↦ hnonterm k)
  refine ⟨n, w, hw, ?_⟩
  apply resonancePair_eq_cfTerminalPair_of_prefix_convergent hx hp hprim
    w.2.2 hw
  simpa [w.2.1] using! hconv

end

end Erdos1002
