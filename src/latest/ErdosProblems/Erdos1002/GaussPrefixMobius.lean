import ErdosProblems.Erdos1002.GaussConvergentEndpoint
import ErdosProblems.Erdos1002.GaussApproximationCoordinate

set_option autoImplicit false
set_option relaxedAutoImplicit false
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Exact linear-fractional coordinates of a Gauss prefix

This file records all four continuants of a positive finite Gauss word.
Unlike an endpoint-only formulation, the four-coefficient matrix retains the
tail variable.  Its determinant gives the exact signed approximation error
needed to identify the manuscript's resonance coordinate with the standard
continued-fraction coefficient.
-/

open Set

namespace Erdos1002

noncomputable section

/-- Coefficients of the linear-fractional map encoded by a finite Gauss
word: `x ↦ (A*x+B)/(C*x+D)`. -/
@[ext] structure GaussPrefixMobius where
  A : ℕ
  B : ℕ
  C : ℕ
  D : ℕ
  deriving DecidableEq

/-- The coefficient recursion is the literal inverse-branch recursion. -/
def gaussPrefixMobius : List ℕ → GaussPrefixMobius
  | [] => ⟨1, 0, 0, 1⟩
  | q :: w =>
      let M := gaussPrefixMobius w
      ⟨M.C, M.D, q * M.C + M.A, q * M.D + M.B⟩

@[simp] theorem gaussPrefixMobius_nil :
    gaussPrefixMobius [] = ⟨1, 0, 0, 1⟩ := rfl

@[simp] theorem gaussPrefixMobius_cons_A (q : ℕ) (w : List ℕ) :
    (gaussPrefixMobius (q :: w)).A = (gaussPrefixMobius w).C := rfl

@[simp] theorem gaussPrefixMobius_cons_B (q : ℕ) (w : List ℕ) :
    (gaussPrefixMobius (q :: w)).B = (gaussPrefixMobius w).D := rfl

@[simp] theorem gaussPrefixMobius_cons_C (q : ℕ) (w : List ℕ) :
    (gaussPrefixMobius (q :: w)).C =
      q * (gaussPrefixMobius w).C + (gaussPrefixMobius w).A := rfl

@[simp] theorem gaussPrefixMobius_cons_D (q : ℕ) (w : List ℕ) :
    (gaussPrefixMobius (q :: w)).D =
      q * (gaussPrefixMobius w).D + (gaussPrefixMobius w).B := rfl

/-- The two constant coefficients are exactly the terminal pair already
used by the cylinder-counting layer. -/
theorem gaussPrefixMobius_BD_eq_terminalPair (w : List ℕ) :
    ((gaussPrefixMobius w).B, (gaussPrefixMobius w).D) =
      cfTerminalPair w := by
  induction w with
  | nil => rfl
  | cons q w ih =>
      change ((gaussPrefixMobius w).D,
          q * (gaussPrefixMobius w).D + (gaussPrefixMobius w).B) =
        ((cfTerminalPair w).2,
          q * (cfTerminalPair w).2 + (cfTerminalPair w).1)
      have hB : (gaussPrefixMobius w).B = (cfTerminalPair w).1 := by
        simpa using! congrArg Prod.fst ih
      have hD : (gaussPrefixMobius w).D = (cfTerminalPair w).2 := by
        simpa using! congrArg Prod.snd ih
      rw [hB, hD]

/-- The constant numerator is the terminal numerator. -/
theorem gaussPrefixMobius_B_eq_terminalNumerator (w : List ℕ) :
    (gaussPrefixMobius w).B = cfTerminalNumerator w := by
  exact congrArg Prod.fst (gaussPrefixMobius_BD_eq_terminalPair w)

/-- The constant denominator is the terminal denominator. -/
theorem gaussPrefixMobius_D_eq_terminalDenominator (w : List ℕ) :
    (gaussPrefixMobius w).D = cfTerminalDenominator w := by
  exact congrArg Prod.snd (gaussPrefixMobius_BD_eq_terminalPair w)

/-- The integral determinant alternates exactly with word length. -/
theorem gaussPrefixMobius_determinant (w : List ℕ) :
    ((gaussPrefixMobius w).A : ℤ) * (gaussPrefixMobius w).D -
        ((gaussPrefixMobius w).B : ℤ) * (gaussPrefixMobius w).C =
      (-1 : ℤ) ^ w.length := by
  induction w with
  | nil => norm_num [gaussPrefixMobius]
  | cons q w ih =>
      simp only [gaussPrefixMobius_cons_A, gaussPrefixMobius_cons_B,
        gaussPrefixMobius_cons_C, gaussPrefixMobius_cons_D,
        List.length_cons, pow_succ]
      push_cast
      rw [← ih]
      ring

/-- A positive word has a strictly positive constant denominator. -/
theorem gaussPrefixMobius_D_pos
    {w : List ℕ} (hpos : IsPositiveCFWord w) :
    0 < (gaussPrefixMobius w).D := by
  rw [gaussPrefixMobius_D_eq_terminalDenominator]
  exact cfTerminalDenominator_pos hpos

/-- Exact linear-fractional formula on the nonnegative tail half-line. -/
theorem gaussInverseWord_eq_gaussPrefixMobius
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : 0 ≤ x) :
    gaussInverseWord w x =
      (((gaussPrefixMobius w).A : ℝ) * x + (gaussPrefixMobius w).B) /
        (((gaussPrefixMobius w).C : ℝ) * x + (gaussPrefixMobius w).D) := by
  induction w generalizing x with
  | nil => simp [gaussInverseWord, gaussPrefixMobius]
  | cons q w ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
        exact_mod_cast gaussPrefixMobius_D_pos htail
      have hden : (0 : ℝ) <
          (gaussPrefixMobius w).C * x + (gaussPrefixMobius w).D := by
        positivity
      rw [gaussInverseWord, gaussInverseBranch, ih htail hx]
      simp only [gaussPrefixMobius_cons_A, gaussPrefixMobius_cons_B,
        gaussPrefixMobius_cons_C, gaussPrefixMobius_cons_D]
      push_cast
      field_simp [ne_of_gt hden]
      ring

/-- Appending the last digit is right multiplication by its inverse-branch
matrix.  This is the form compatible with the backward-ratio recursion. -/
theorem gaussPrefixMobius_append_singleton (w : List ℕ) (q : ℕ) :
    gaussPrefixMobius (w ++ [q]) =
      ⟨(gaussPrefixMobius w).B,
        (gaussPrefixMobius w).A + q * (gaussPrefixMobius w).B,
        (gaussPrefixMobius w).D,
        (gaussPrefixMobius w).C + q * (gaussPrefixMobius w).D⟩ := by
  induction w with
  | nil =>
      apply GaussPrefixMobius.ext <;> simp [gaussPrefixMobius]
  | cons a w ih =>
      change
        (⟨(gaussPrefixMobius (w ++ [q])).C,
          (gaussPrefixMobius (w ++ [q])).D,
          a * (gaussPrefixMobius (w ++ [q])).C +
            (gaussPrefixMobius (w ++ [q])).A,
          a * (gaussPrefixMobius (w ++ [q])).D +
            (gaussPrefixMobius (w ++ [q])).B⟩ : GaussPrefixMobius) = _
      rw [ih]
      apply GaussPrefixMobius.ext
      · rfl
      · rfl
      · rfl
      · simp only [gaussPrefixMobius_cons_C, gaussPrefixMobius_cons_D]
        ring

/-- Splitting a prefix after `u.length` is exact, provided the original
sample lies in the half-open unit interval. -/
theorem mem_gaussHalfOpenPrefixCylinder_append_iff
    (u v : List ℕ) {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1) :
    x ∈ gaussHalfOpenPrefixCylinder (u ++ v) ↔
      x ∈ gaussHalfOpenPrefixCylinder u ∧
        gaussOrbit u.length x ∈ gaussHalfOpenPrefixCylinder v := by
  induction u generalizing x with
  | nil =>
      simp [gaussHalfOpenPrefixCylinder, gaussOrbit, hx]
  | cons q u ih =>
      have hTx : gaussMap x ∈ Ico (0 : ℝ) 1 :=
        ⟨Int.fract_nonneg _, Int.fract_lt_one _⟩
      simp only [List.cons_append, gaussHalfOpenPrefixCylinder,
        mem_inter_iff, mem_preimage]
      rw [ih hTx]
      have horbit : gaussOrbit (q :: u).length x =
          gaussOrbit u.length (gaussMap x) := by
        simp [gaussOrbit, Function.iterate_succ_apply]
      rw [horbit]
      tauto

/-- A point of a prefix cylinder is obtained by applying the encoded inverse
word to its remaining Gauss tail. -/
theorem eq_gaussInverseWord_gaussOrbit_of_mem_prefix
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    x = gaussInverseWord w (gaussOrbit w.length x) := by
  induction w generalizing x with
  | nil => simp [gaussInverseWord, gaussOrbit]
  | cons q w ih =>
      have hq : 0 < q := hpos q (by simp)
      have htail : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hfirst : x ∈ firstDigitCylinder q := hw.1
      have hrest : gaussMap x ∈ gaussHalfOpenPrefixCylinder w := hw.2
      calc
        x = gaussInverseBranch q (gaussMap x) :=
          (gaussInverseBranch_gaussMap hq hfirst).symm
        _ = gaussInverseBranch q
            (gaussInverseWord w (gaussOrbit w.length (gaussMap x))) := by
          congr 1
          exact ih htail hrest
        _ = gaussInverseWord (q :: w)
            (gaussOrbit (q :: w).length x) := by
          simp only [gaussInverseWord, List.length_cons]
          congr 1

/-- The final digit of an appended positive cylinder is the corresponding
Gauss digit at the preceding depth. -/
theorem gaussDigitAt_eq_of_mem_append_singleton
    {w : List ℕ} {q : ℕ} (hq : 0 < q)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder (w ++ [q])) :
    gaussDigitAt w.length x = q := by
  have hsplit :=
    (mem_gaussHalfOpenPrefixCylinder_append_iff w [q] hx).1 hw
  have hfirst : gaussOrbit w.length x ∈ firstDigitCylinder q := hsplit.2.1
  have hunit := firstDigitCylinder_subset_unit q hq hfirst
  have hdigit : gaussFirstDigit (gaussOrbit w.length x) = (q : ℤ) :=
    (gaussFirstDigit_eq_iff_mem_firstDigitCylinder hunit q hq).2 hfirst
  unfold gaussDigitAt gaussFirstDigitNat
  rw [hdigit]
  simp

/-- The recursively defined backward continuant ratio is exactly `C/D` of
the prefix matrix.  This proves, rather than assumes, the interpretation
`gaussBackwardRatio n x = Q_{n-1}/Q_n`. -/
theorem gaussBackwardRatio_eq_gaussPrefixMobius
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ico (0 : ℝ) 1)
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    gaussBackwardRatio w.length x =
      ((gaussPrefixMobius w).C : ℝ) / (gaussPrefixMobius w).D := by
  induction w using List.reverseRecOn generalizing x with
  | nil => simp [gaussBackwardRatio, gaussPrefixMobius]
  | append_singleton w q ih =>
      have hq : 0 < q := hpos q (by simp)
      have hprefixPos : IsPositiveCFWord w := by
        intro a ha
        exact hpos a (by simp [ha])
      have hsplit :=
        (mem_gaussHalfOpenPrefixCylinder_append_iff w [q] hx).1 hw
      have ih' := ih hprefixPos hx hsplit.1
      have hdigit := gaussDigitAt_eq_of_mem_append_singleton hq hx hw
      have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
        exact_mod_cast gaussPrefixMobius_D_pos hprefixPos
      rw [List.length_append, List.length_singleton, gaussBackwardRatio]
      rw [hdigit, ih', gaussPrefixMobius_append_singleton]
      simp only
      push_cast
      field_simp [ne_of_gt hD]
      ring

/-- On a nonterminating positive prefix, the exact approximation coordinate
is the explicit tail expression `D*x_n/(C*x_n+D)`. -/
theorem gaussApproximationCoordinate_eq_gaussPrefixMobius
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (w.length + 1))
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    gaussApproximationCoordinate w.length x =
      ((gaussPrefixMobius w).D : ℝ) * gaussOrbit w.length x /
        (((gaussPrefixMobius w).C : ℝ) * gaussOrbit w.length x +
          (gaussPrefixMobius w).D) := by
  have hxIoc : x ∈ Ioc (0 : ℝ) 1 := ⟨hx.1, hx.2.le⟩
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  rw [gaussApproximationCoordinate_eq_orbit_div hxIoc hex,
    gaussBackwardRatio_eq_gaussPrefixMobius hpos hxIco hw]
  have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  field_simp [ne_of_gt hD]
  ring

/-- Exact convergent-error identity in the notation used by the manuscript:
`Q_n*x-P_n = (-1)^n*theta_n/Q_n`. -/
theorem terminalDenominator_mul_sub_terminalNumerator_eq
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : x ∈ Ioo (0 : ℝ) 1)
    (hex : x ∉ gaussPrefixExceptional (w.length + 1))
    (hw : x ∈ gaussHalfOpenPrefixCylinder w) :
    ((gaussPrefixMobius w).D : ℝ) * x - (gaussPrefixMobius w).B =
      (-1 : ℝ) ^ w.length * gaussApproximationCoordinate w.length x /
        (gaussPrefixMobius w).D := by
  have hxIco : x ∈ Ico (0 : ℝ) 1 := ⟨hx.1.le, hx.2⟩
  let y : ℝ := gaussOrbit w.length x
  have hy : 0 ≤ y := by
    dsimp [y]
    cases w.length with
    | zero => simpa [gaussOrbit] using! hx.1.le
    | succ n => exact (gaussOrbit_succ_mem_Ico n x).1
  have hrepr := eq_gaussInverseWord_gaussOrbit_of_mem_prefix hpos hw
  have hmobius := gaussInverseWord_eq_gaussPrefixMobius hpos hy
  have htheta := gaussApproximationCoordinate_eq_gaussPrefixMobius
    hpos hx hex hw
  have hrepr' : x = gaussInverseWord w y := by
    simpa [y] using! hrepr
  have htheta' : gaussApproximationCoordinate w.length x =
      ((gaussPrefixMobius w).D : ℝ) * y /
        (((gaussPrefixMobius w).C : ℝ) * y +
          (gaussPrefixMobius w).D) := by
    simpa [y] using! htheta
  have hxMobius : x =
      (((gaussPrefixMobius w).A : ℝ) * y +
          (gaussPrefixMobius w).B) /
        (((gaussPrefixMobius w).C : ℝ) * y +
          (gaussPrefixMobius w).D) := hrepr'.trans hmobius
  have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  have hden : (0 : ℝ) <
      (gaussPrefixMobius w).C * y + (gaussPrefixMobius w).D := by
    positivity
  have hdetZ := gaussPrefixMobius_determinant w
  have hdetR :
      ((gaussPrefixMobius w).A : ℝ) * (gaussPrefixMobius w).D -
          ((gaussPrefixMobius w).B : ℝ) * (gaussPrefixMobius w).C =
        (-1 : ℝ) ^ w.length := by
    exact_mod_cast hdetZ
  rw [htheta', hxMobius]
  change ((gaussPrefixMobius w).D : ℝ) *
      ((((gaussPrefixMobius w).A : ℝ) * y +
          (gaussPrefixMobius w).B) /
        (((gaussPrefixMobius w).C : ℝ) * y +
          (gaussPrefixMobius w).D)) -
      (gaussPrefixMobius w).B = _
  field_simp [ne_of_gt hD, ne_of_gt hden]
  nlinarith

/-- Exact signed error from the terminal rational endpoint.  The parity sign
is visible and every denominator factor is explicit. -/
theorem gaussInverseWord_sub_terminalRatio
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : 0 ≤ x) :
    gaussInverseWord w x -
        ((gaussPrefixMobius w).B : ℝ) / (gaussPrefixMobius w).D =
      ((-1 : ℝ) ^ w.length * x) /
        ((gaussPrefixMobius w).D *
          (((gaussPrefixMobius w).C : ℝ) * x +
            (gaussPrefixMobius w).D)) := by
  have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  have hden : (0 : ℝ) <
      (gaussPrefixMobius w).C * x + (gaussPrefixMobius w).D := by
    positivity
  rw [gaussInverseWord_eq_gaussPrefixMobius hpos hx]
  have hdetZ := gaussPrefixMobius_determinant w
  have hdetR :
      ((gaussPrefixMobius w).A : ℝ) * (gaussPrefixMobius w).D -
          ((gaussPrefixMobius w).B : ℝ) * (gaussPrefixMobius w).C =
        (-1 : ℝ) ^ w.length := by
    exact_mod_cast hdetZ
  field_simp [ne_of_gt hD, ne_of_gt hden]
  nlinarith

/-- Absolute form of the preceding exact error identity. -/
theorem abs_gaussInverseWord_sub_terminalRatio
    {w : List ℕ} (hpos : IsPositiveCFWord w)
    {x : ℝ} (hx : 0 ≤ x) :
    |gaussInverseWord w x -
        ((gaussPrefixMobius w).B : ℝ) / (gaussPrefixMobius w).D| =
      x /
        ((gaussPrefixMobius w).D *
          (((gaussPrefixMobius w).C : ℝ) * x +
            (gaussPrefixMobius w).D)) := by
  rw [gaussInverseWord_sub_terminalRatio hpos hx, abs_div, abs_mul,
    abs_neg_one_pow, abs_of_nonneg hx]
  have hD : (0 : ℝ) < (gaussPrefixMobius w).D := by
    exact_mod_cast gaussPrefixMobius_D_pos hpos
  have hden : (0 : ℝ) <
      (gaussPrefixMobius w).C * x + (gaussPrefixMobius w).D := by
    positivity
  rw [abs_mul, abs_of_pos hD, abs_of_pos hden]
  simp

end

end Erdos1002
