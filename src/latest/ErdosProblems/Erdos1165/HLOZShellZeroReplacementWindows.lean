/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZShellZeroReplacementProduct
import ErdosProblems.Erdos1165.HLOZProposition48Candidates
import ErdosProblems.Erdos1165.HLOZSharpWindowProductClosure
import ErdosProblems.Erdos1165.SmallWindow
import ErdosProblems.Erdos1165.TilingAwayNegativeBinomial

/-!
# Literal shell-zero replacement windows

The first strip in HLOZ Proposition 4.8 is not controlled by a uniform
conditional estimate on each stopped trace.  The source window is

`I₁ = (m - w, m)`,

whereas the comparison window is the artificial, above-level window

`I₀ = [m + 1, m + w)`.

This module records those literal integer windows, translates them by a
fixed external local time, and proves all deterministic facts needed by the
negative-binomial local-CLT comparison.  It also packages the exact global
disjointness mechanism used for the replacement events `B_η`: at the clock
carried by a replacement trace, a monotone threshold count jumps from one
fixed value to its successor.  Two distinct clocks cannot both carry that
same jump, while two different traces at the same clock are separated by
their trace label.
-/

open MeasureTheory Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZShellZeroReplacementWindows

open HLOZProposition48Candidates HLOZShellZeroReplacementProduct
open HLOZSharpWindowProductClosure
open NegativeBinomial NegativeBinomialLocalCLT ScreeningInstantiation
open SmallWindow TilingAwayNegativeBinomial
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

/-! ## The literal `I₀` and `I₁` windows -/

/-- HLOZ's artificial above-level comparison window
`I₀ = [m + 1, m + w)`. -/
def shellZeroReplacementTotalWindow (m w : ℕ) : Finset ℕ :=
  Finset.Ico (m + 1) (m + w)

/-- HLOZ's first below-level strip `I₁ = (m - w, m)`. -/
def shellZeroSourceTotalWindow (m w : ℕ) : Finset ℕ :=
  Finset.Ico (m - w + 1) m

/-- Lazy-count values corresponding to `I₀`, after fixing external local
time `i`.  The hypotheses used below ensure that the subtraction is exact. -/
def shellZeroReplacementFailureWindow (m w i : ℕ) : Finset ℕ :=
  Finset.Ico (m + 1 - i) (m + w - i)

/-- Lazy-count values corresponding to `I₁`, after fixing external local
time `i`. -/
def shellZeroSourceFailureWindow (m w i : ℕ) : Finset ℕ :=
  Finset.Ico (m - w + 1 - i) (m - i)

@[simp] theorem mem_shellZeroReplacementTotalWindow {m w j : ℕ} :
    j ∈ shellZeroReplacementTotalWindow m w ↔ m + 1 ≤ j ∧ j < m + w := by
  simp [shellZeroReplacementTotalWindow]

@[simp] theorem mem_shellZeroSourceTotalWindow {m w j : ℕ} :
    j ∈ shellZeroSourceTotalWindow m w ↔ m - w + 1 ≤ j ∧ j < m := by
  simp [shellZeroSourceTotalWindow]

@[simp] theorem mem_shellZeroReplacementFailureWindow {m w i v : ℕ} :
    v ∈ shellZeroReplacementFailureWindow m w i ↔
      m + 1 - i ≤ v ∧ v < m + w - i := by
  simp [shellZeroReplacementFailureWindow]

@[simp] theorem mem_shellZeroSourceFailureWindow {m w i v : ℕ} :
    v ∈ shellZeroSourceFailureWindow m w i ↔
      m - w + 1 - i ≤ v ∧ v < m - i := by
  simp [shellZeroSourceFailureWindow]

theorem shellZeroReplacementTotalWindow_card {m w : ℕ} (hw : 1 ≤ w) :
    (shellZeroReplacementTotalWindow m w).card = w - 1 := by
  simp [shellZeroReplacementTotalWindow, Nat.card_Ico]
  omega

theorem shellZeroSourceTotalWindow_card {m w : ℕ} (hw : w ≤ m) :
    (shellZeroSourceTotalWindow m w).card = w - 1 := by
  simp [shellZeroSourceTotalWindow, Nat.card_Ico]
  omega

theorem shellZeroTotalWindows_disjoint (m w : ℕ) :
    Disjoint (shellZeroSourceTotalWindow m w)
      (shellZeroReplacementTotalWindow m w) := by
  rw [Finset.disjoint_left]
  intro j hsource hreplacement
  simp only [mem_shellZeroSourceTotalWindow] at hsource
  simp only [mem_shellZeroReplacementTotalWindow] at hreplacement
  omega

theorem shellZeroReplacementFailureWindow_card
    {m w i : ℕ} (hi : i ≤ m + 1) (hw : 1 ≤ w) :
    (shellZeroReplacementFailureWindow m w i).card = w - 1 := by
  simp [shellZeroReplacementFailureWindow, Nat.card_Ico]
  omega

theorem shellZeroSourceFailureWindow_card
    {m w i : ℕ} (hi : i ≤ m - w + 1) (hw : w ≤ m) :
    (shellZeroSourceFailureWindow m w i).card = w - 1 := by
  simp [shellZeroSourceFailureWindow, Nat.card_Ico]
  omega

theorem shellZeroFailureWindows_disjoint
    {m w i : ℕ} (hi : i ≤ m - w + 1) :
    Disjoint (shellZeroSourceFailureWindow m w i)
      (shellZeroReplacementFailureWindow m w i) := by
  rw [Finset.disjoint_left]
  intro v hsource hreplacement
  simp only [mem_shellZeroSourceFailureWindow] at hsource
  simp only [mem_shellZeroReplacementFailureWindow] at hreplacement
  omega

theorem shellZeroSourceFailureWindow_nonempty
    {m w i : ℕ} (hi : i ≤ m - w + 1) (hw : 2 ≤ w) (hwm : w ≤ m) :
    (shellZeroSourceFailureWindow m w i).Nonempty := by
  apply Finset.card_pos.mp
  rw [shellZeroSourceFailureWindow_card hi hwm]
  omega

theorem shellZeroReplacementFailureWindow_nonempty
    {m w i : ℕ} (hi : i ≤ m - w + 1) (hw : 2 ≤ w) :
    (shellZeroReplacementFailureWindow m w i).Nonempty := by
  apply Finset.card_pos.mp
  rw [shellZeroReplacementFailureWindow_card (by omega) (by omega)]
  omega

/-! ## Exact translation and local-CLT geometry -/

lemma deviation_sub_eq_totalDeviation {i j : ℕ} (hi : i ≤ j) :
    deviation i (j - i) = (j : ℝ) - (16 / 15 : ℝ) * (i : ℝ) := by
  unfold deviation
  rw [Nat.cast_sub hi]
  ring

/-- Membership in the below-level base-site local-time window is exactly
membership in its translated lazy-count window.  Here `i` is the retained
external count at the base and `j - i` is the inserted lazy count. -/
theorem sub_mem_shellZeroSourceFailureWindow_iff
    {m w i j : ℕ} (hi : i ≤ m - w + 1) (hij : i ≤ j) :
    j - i ∈ shellZeroSourceFailureWindow m w i ↔
      j ∈ shellZeroSourceTotalWindow m w := by
  simp only [mem_shellZeroSourceFailureWindow,
    mem_shellZeroSourceTotalWindow]
  omega

/-- Membership in the artificial above-level base-site local-time window is
exactly membership in its translated lazy-count window. -/
theorem sub_mem_shellZeroReplacementFailureWindow_iff
    {m w i j : ℕ} (hij : i ≤ j) :
    j - i ∈ shellZeroReplacementFailureWindow m w i ↔
      j ∈ shellZeroReplacementTotalWindow m w := by
  simp only [mem_shellZeroReplacementFailureWindow,
    mem_shellZeroReplacementTotalWindow]
  omega

/-- A convenient deterministic radius.  `centerRadius` controls the distance
between the base-site local-time center `(16/15)i` and `m`; the extra `w`
allows either literal shell-zero window. -/
def shellZeroDeviationRadius (w : ℕ) (centerRadius : ℝ) : ℝ :=
  (w : ℝ) + centerRadius

/-- The two base-site local-time windows are separated by at most `2w` after
translation. -/
def shellZeroWindowSeparation (w : ℕ) : ℝ := 2 * (w : ℝ)

lemma shellZeroDeviationRadius_nonneg {w : ℕ} {centerRadius : ℝ}
    (hcenterRadius : 0 ≤ centerRadius) :
    0 ≤ shellZeroDeviationRadius w centerRadius := by
  unfold shellZeroDeviationRadius
  positivity

lemma shellZeroWindowSeparation_nonneg (w : ℕ) :
    0 ≤ shellZeroWindowSeparation w := by
  unfold shellZeroWindowSeparation
  positivity

theorem sourceTotal_deviation_le
    {m w i j : ℕ} {centerRadius : ℝ}
    (hwm : w ≤ m)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hj : j ∈ shellZeroSourceTotalWindow m w) :
    |(j : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroDeviationRadius w centerRadius := by
  simp only [mem_shellZeroSourceTotalWindow] at hj
  have hjLower : ((m - w + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hj.1
  have hjUpper : (j : ℝ) < (m : ℝ) := by
    exact_mod_cast hj.2
  rw [Nat.cast_add, Nat.cast_sub hwm] at hjLower
  push_cast at hjLower hjUpper
  rw [abs_le] at hcenter ⊢
  unfold shellZeroDeviationRadius
  constructor <;> linarith

theorem replacementTotal_deviation_le
    {m w i j : ℕ} {centerRadius : ℝ}
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hj : j ∈ shellZeroReplacementTotalWindow m w) :
    |(j : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroDeviationRadius w centerRadius := by
  simp only [mem_shellZeroReplacementTotalWindow] at hj
  have hjLower : ((m + 1 : ℕ) : ℝ) ≤ (j : ℝ) := by
    exact_mod_cast hj.1
  have hjUpper : (j : ℝ) < ((m + w : ℕ) : ℝ) := by
    exact_mod_cast hj.2
  push_cast at hjLower hjUpper
  rw [abs_le] at hcenter ⊢
  unfold shellZeroDeviationRadius
  constructor <;> linarith

theorem sourceFailure_deviation_le
    {m w i v : ℕ} {centerRadius : ℝ}
    (hi : i ≤ m - w + 1)
    (hwm : w ≤ m)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hv : v ∈ shellZeroSourceFailureWindow m w i) :
    |deviation i v| ≤ shellZeroDeviationRadius w centerRadius := by
  have hj : v + i ∈ shellZeroSourceTotalWindow m w := by
    simp only [mem_shellZeroSourceFailureWindow] at hv
    simp only [mem_shellZeroSourceTotalWindow]
    omega
  have hsub : v + i - i = v := by omega
  rw [← hsub, deviation_sub_eq_totalDeviation (by omega)]
  exact sourceTotal_deviation_le hwm hcenter hj

theorem replacementFailure_deviation_le
    {m w i v : ℕ} {centerRadius : ℝ}
    (_hi : i ≤ m - w + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hv : v ∈ shellZeroReplacementFailureWindow m w i) :
    |deviation i v| ≤ shellZeroDeviationRadius w centerRadius := by
  have hj : v + i ∈ shellZeroReplacementTotalWindow m w := by
    simp only [mem_shellZeroReplacementFailureWindow] at hv
    simp only [mem_shellZeroReplacementTotalWindow]
    omega
  have hsub : v + i - i = v := by omega
  rw [← hsub, deviation_sub_eq_totalDeviation (by omega)]
  exact replacementTotal_deviation_le hcenter hj

theorem shellZeroFailure_deviation_sub_le
    {m w i source replacement : ℕ}
    (hi : i ≤ m - w + 1)
    (hsource : source ∈ shellZeroSourceFailureWindow m w i)
    (hreplacement : replacement ∈ shellZeroReplacementFailureWindow m w i) :
    |deviation i source - deviation i replacement| ≤
      shellZeroWindowSeparation w := by
  have hle : source ≤ replacement := by
    simp only [mem_shellZeroSourceFailureWindow] at hsource
    simp only [mem_shellZeroReplacementFailureWindow] at hreplacement
    omega
  have hgap : replacement ≤ source + 2 * w := by
    simp only [mem_shellZeroSourceFailureWindow] at hsource
    simp only [mem_shellZeroReplacementFailureWindow] at hreplacement
    omega
  have heq : deviation i source - deviation i replacement =
      (source : ℝ) - (replacement : ℝ) := by
    unfold deviation
    ring
  have hleR : (source : ℝ) ≤ (replacement : ℝ) := by exact_mod_cast hle
  have hgapR : (replacement : ℝ) - (source : ℝ) ≤ 2 * (w : ℝ) := by
    have hgapNat : replacement - source ≤ 2 * w := by omega
    exact_mod_cast hgapNat
  rw [heq, abs_of_nonpos (sub_nonpos.mpr hleR)]
  unfold shellZeroWindowSeparation
  linarith

/-- The checked negative-binomial local CLT compares the literal below-level
source window with the artificial above-level replacement window. -/
theorem sourceWindowMass_le_adjacentLocalRatio_mul_replacementWindowMass
    {m w i : ℕ} {centerRadius : ℝ}
    (hi : 0 < i) (htranslate : i ≤ m - w + 1)
    (hw : 2 ≤ w) (hwm : w ≤ m)
    (hcenterRadius : 0 ≤ centerRadius)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤ centerRadius)
    (hmoderate : shellZeroDeviationRadius w centerRadius ≤ (i : ℝ) / 30) :
    windowMass i (shellZeroSourceFailureWindow m w i) ≤
      adjacentLocalRatio i (shellZeroDeviationRadius w centerRadius)
          (shellZeroWindowSeparation w) *
        windowMass i (shellZeroReplacementFailureWindow m w i) := by
  apply adjacentWindowMass_le_adjacentLocalRatio hi
    (shellZeroDeviationRadius_nonneg hcenterRadius)
    (shellZeroWindowSeparation_nonneg w) hmoderate
    (shellZeroReplacementFailureWindow_nonempty htranslate hw)
  · rw [shellZeroSourceFailureWindow_card htranslate hwm,
      shellZeroReplacementFailureWindow_card (by omega) (by omega)]
  · exact fun v hv ↦ sourceFailure_deviation_le htranslate hwm hcenter hv
  · exact fun v hv ↦ replacementFailure_deviation_le htranslate hcenter hv
  · intro source hsource replacement hreplacement
    exact shellZeroFailure_deviation_sub_le htranslate hsource hreplacement

/-! ## An explicit eventual local-ratio constant -/

/-- The center range appearing in HLOZ's exceptional set `theta`: it permits
one shell width in addition to the checked geometric deviation. -/
noncomputable def shellZeroCenterRadius (m : ℕ) : ℝ :=
  (shellWidth48 m : ℝ) + geometricDeviation m

/-- The common local-CLT radius for the literal `I₀/I₁` windows. -/
noncomputable def literalShellZeroDeviationRadius (m : ℕ) : ℝ :=
  shellZeroDeviationRadius (shellWidth48 m) (shellZeroCenterRadius m)

/-- A deliberately generous fixed local-ratio constant.  Its size is
irrelevant to summability; only finiteness and independence of `m` matter. -/
noncomputable def shellZeroLocalRatioConstant : ℝ := Real.exp 50000000
-- The explicit value is intentionally coarse; it is independent of `m`.

lemma shellZeroLocalRatioConstant_pos : 0 < shellZeroLocalRatioConstant := by
  exact Real.exp_pos _

/-- The numerical facts needed for the literal shell-zero local-CLT
comparison.  The pathwise adapter only has to show that the external count
is thick, translatable below `m-w+1`, and lies in `shellZeroCenterRadius`. -/
def ShellZeroWindowArithmeticAt (m : ℕ) : Prop :=
  2 ≤ shellWidth48 m ∧ shellWidth48 m ≤ m ∧
    ∀ i, m / 2 ≤ i →
      0 < i ∧
      literalShellZeroDeviationRadius m ≤ (i : ℝ) / 30 ∧
      adjacentLocalRatio i (literalShellZeroDeviationRadius m)
          (shellZeroWindowSeparation (shellWidth48 m)) ≤
        shellZeroLocalRatioConstant

/-- Once the retained external count is in the admissible center range, the
literal source-window mass is bounded by one fixed multiple of the
artificial replacement-window mass.  All analytic/local-CLT input is
discharged here; downstream fibre code only supplies the three pathwise
arithmetic facts `hthick`, `htranslate`, and `hcenter`. -/
theorem sourceWindowMass_le_shellZeroLocalRatioConstant
    {m i : ℕ} (harithmetic : ShellZeroWindowArithmeticAt m)
    (hthick : m / 2 ≤ i)
    (htranslate : i ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroCenterRadius m) :
    windowMass i
        (shellZeroSourceFailureWindow m (shellWidth48 m) i) ≤
      shellZeroLocalRatioConstant *
        windowMass i
          (shellZeroReplacementFailureWindow m (shellWidth48 m) i) := by
  have hlocal := harithmetic.2.2 i hthick
  refine (sourceWindowMass_le_adjacentLocalRatio_mul_replacementWindowMass
    hlocal.1 htranslate harithmetic.1 harithmetic.2.1
      ?_ hcenter hlocal.2.1).trans ?_
  · unfold shellZeroCenterRadius
    exact add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m)
  · exact mul_le_mul_of_nonneg_right hlocal.2.2
      (windowMass_nonneg _ _)

/-- All-six tiling-coordinate form of the preceding literal-window bound.
The capped normalization cancels exactly, so the same fixed constant works
on every away domino. -/
theorem tilingAway_coordinateMass_shellZeroSource_le
    {retainedCount cap m : ℕ}
    (t : Tilings.Tiling) (x : Point)
    (r : TilingRetainedWord t x retainedCount) (D : Finset Point)
    (upper : TilingAwayDomino t x r D → ℕ)
    (b : TilingAwayDomino t x r D)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hthick : m / 2 ≤ Fintype.card (TilingCoordinatesAt t x r b.1))
    (htranslate : Fintype.card (TilingCoordinatesAt t x r b.1) ≤
      m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) *
        (Fintype.card (TilingCoordinatesAt t x r b.1) : ℝ)| ≤
      shellZeroCenterRadius m)
    (hsourceUpper : ∀ v,
      v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v < upper b)
    (hreplacementUpper : ∀ v,
      v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v < upper b)
    (hsourceCap : ∀ v,
      v ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v ≤ cap)
    (hreplacementCap : ∀ v,
      v ∈ shellZeroReplacementFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) →
        v ≤ cap) :
    (∑ v : Fin (upper b),
      if (v : ℕ) ∈ shellZeroSourceFailureWindow m (shellWidth48 m)
          (Fintype.card (TilingCoordinatesAt t x r b.1)) then
        FiniteDominoProductLaw.coordinateMass
          (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0) ≤
      shellZeroLocalRatioConstant *
        ∑ v : Fin (upper b),
          if (v : ℕ) ∈
              shellZeroReplacementFailureWindow m (shellWidth48 m)
                (Fintype.card (TilingCoordinatesAt t x r b.1)) then
            FiniteDominoProductLaw.coordinateMass
              (tilingAwayPointMass (cap := cap) t x r D) upper b v else 0 := by
  apply tilingAway_coordinateMass_window_ratio t x r D upper b
    (shellZeroSourceFailureWindow m (shellWidth48 m)
      (Fintype.card (TilingCoordinatesAt t x r b.1)))
    (shellZeroReplacementFailureWindow m (shellWidth48 m)
      (Fintype.card (TilingCoordinatesAt t x r b.1)))
    hsourceUpper hreplacementUpper hsourceCap hreplacementCap
  · have hpositive : 0 < Fintype.card (TilingCoordinatesAt t x r b.1) :=
      (harithmetic.2.2 _ hthick).1
    exact hpositive
  · exact sourceWindowMass_le_shellZeroLocalRatioConstant
      harithmetic hthick htranslate hcenter

lemma rpow_one_sub_kappaOne_cube_div_square {m : ℕ} (hm : 0 < m) :
    (((m : ℝ) ^ (1 - kappaOne)) ^ 3) / (m : ℝ) ^ 2 =
      (m : ℝ) ^ (-(1 / 32 : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (((m : ℝ) ^ (1 - kappaOne)) ^ 3) / (m : ℝ) ^ 2 =
        ((m : ℝ) ^ (1 - kappaOne)) ^ (3 : ℝ) /
          (m : ℝ) ^ (2 : ℝ) := by
      congr 1
      · exact (Real.rpow_natCast ((m : ℝ) ^ (1 - kappaOne)) 3).symm
      · exact (Real.rpow_natCast (m : ℝ) 2).symm
    _ = (m : ℝ) ^ ((1 - kappaOne) * 3) /
          (m : ℝ) ^ (2 : ℝ) := by
      rw [(Real.rpow_mul hmR.le (1 - kappaOne) 3).symm]
    _ = (m : ℝ) ^ ((1 - kappaOne) * 3 - 2) := by
      rw [Real.rpow_sub hmR]
    _ = (m : ℝ) ^ (-(1 / 32 : ℝ)) := by
      congr 1
      norm_num [kappaOne]

lemma rpow_one_sub_kappaOne_mul_kappaOne {m : ℕ} (hm : 0 < m) :
    (m : ℝ) ^ (1 - kappaOne) * (m : ℝ) ^ kappaOne = (m : ℝ) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (m : ℝ) ^ (1 - kappaOne) * (m : ℝ) ^ kappaOne =
        (m : ℝ) ^ ((1 - kappaOne) + kappaOne) :=
      (Real.rpow_add hmR (1 - kappaOne) kappaOne).symm
    _ = (m : ℝ) := by rw [sub_add_cancel, Real.rpow_one]

lemma literalShellZeroDeviationRadius_le_thirteen_rpow
    {m : ℕ} (hm : 1 ≤ m)
    (hwidth : (shellWidth48 m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne) :
    literalShellZeroDeviationRadius m ≤
      13 * (m : ℝ) ^ (1 - kappaOne) := by
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hmono : (m : ℝ) ^ kappaOne ≤ (m : ℝ) ^ (1 - kappaOne) := by
    apply Real.rpow_le_rpow_of_exponent_le hmR
    norm_num [kappaOne]
  have hyOne : 1 ≤ (m : ℝ) ^ (1 - kappaOne) := by
    exact Real.one_le_rpow hmR (by norm_num [kappaOne])
  unfold literalShellZeroDeviationRadius shellZeroDeviationRadius
    shellZeroCenterRadius geometricDeviation
  nlinarith

lemma shellZeroWindowSeparation_le_four_rpow
    {m : ℕ}
    (hwidth : (shellWidth48 m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne) :
    shellZeroWindowSeparation (shellWidth48 m) ≤
      4 * (m : ℝ) ^ kappaOne := by
  unfold shellZeroWindowSeparation
  linarith

lemma adjacentLocalRatio_literalShellZero_le_constant
    {m i : ℕ} (hm : 2 ≤ m) (hi : m / 2 ≤ i)
    (hwidth : (shellWidth48 m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne) :
    adjacentLocalRatio i (literalShellZeroDeviationRadius m)
        (shellZeroWindowSeparation (shellWidth48 m)) ≤
      shellZeroLocalRatioConstant := by
  let M : ℝ := m
  let I : ℝ := i
  let X : ℝ := M ^ kappaOne
  let Y : ℝ := M ^ (1 - kappaOne)
  let D : ℝ := literalShellZeroDeviationRadius m
  let W : ℝ := shellZeroWindowSeparation (shellWidth48 m)
  have hmPos : 0 < m := by omega
  have hiPos : 0 < i := by
    have hhalf : 1 ≤ m / 2 := by omega
    omega
  have hMpos : 0 < M := by
    dsimp only [M]
    exact_mod_cast hmPos
  have hIpos : 0 < I := by
    dsimp only [I]
    exact_mod_cast hiPos
  have hMone : 1 ≤ M := by
    dsimp only [M]
    exact_mod_cast (show 1 ≤ m by omega)
  have hMle : M ≤ 3 * I := by
    dsimp only [M, I]
    have hnat : m ≤ 3 * i := by omega
    exact_mod_cast hnat
  have hD0 : 0 ≤ D := by
    dsimp only [D, literalShellZeroDeviationRadius, shellZeroCenterRadius,
      shellZeroDeviationRadius]
    exact add_nonneg (Nat.cast_nonneg _) (add_nonneg (Nat.cast_nonneg _)
      (geometricDeviation_nonneg m))
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact shellZeroWindowSeparation_nonneg _
  have hD : D ≤ 13 * Y := by
    simpa only [D, Y, M] using
      literalShellZeroDeviationRadius_le_thirteen_rpow
        (show 1 ≤ m by omega) hwidth
  have hW : W ≤ 4 * X := by
    simpa only [W, X, M] using
      shellZeroWindowSeparation_le_four_rpow hwidth
  have hXY : Y * X = M := by
    simpa only [Y, X, M] using
      rpow_one_sub_kappaOne_mul_kappaOne hmPos
  have hYcubeDiv : Y ^ 3 / M ^ 2 = M ^ (-(1 / 32 : ℝ)) := by
    simpa only [Y, M] using rpow_one_sub_kappaOne_cube_div_square hmPos
  have hnegPowLe : M ^ (-(1 / 32 : ℝ)) ≤ 1 := by
    rw [Real.rpow_neg hMpos.le]
    apply (inv_le_one₀ (Real.rpow_pos_of_pos hMpos _)).2
    exact Real.one_le_rpow hMone (by norm_num)
  have hYcube : Y ^ 3 ≤ M ^ 2 := by
    have hMsq : 0 < M ^ 2 := sq_pos_of_pos hMpos
    exact (div_le_one hMsq).mp (hYcubeDiv.trans_le hnegPowLe)
  have hMsq : M ^ 2 ≤ 9 * I ^ 2 := by nlinarith
  have hDcube : D ^ 3 ≤ 2197 * Y ^ 3 := by
    calc
      D ^ 3 ≤ (13 * Y) ^ 3 := pow_le_pow_left₀ hD0 hD 3
      _ = 2197 * Y ^ 3 := by ring
  have htermOne : 38 / Real.sqrt I ≤ 38 := by
    have hIone : 1 ≤ I := by
      dsimp only [I]
      exact_mod_cast (show 1 ≤ i by omega)
    have hsqrtOne : 1 ≤ Real.sqrt I := Real.one_le_sqrt.mpr hIone
    have hsqrtPos : 0 < Real.sqrt I := Real.sqrt_pos.2 hIpos
    rw [div_le_iff₀ hsqrtPos]
    nlinarith
  have htermTwo : 1840 * D ^ 3 / I ^ 2 ≤ 36382320 := by
    have hIsq : 0 < I ^ 2 := sq_pos_of_pos hIpos
    rw [div_le_iff₀ hIsq]
    calc
      1840 * D ^ 3 ≤ 1840 * (2197 * Y ^ 3) := by gcongr
      _ ≤ 1840 * (2197 * M ^ 2) := by gcongr
      _ ≤ 36382320 * I ^ 2 := by nlinarith
  have hDW : D * W ≤ 156 * I := by
    calc
      D * W ≤ (13 * Y) * (4 * X) :=
        mul_le_mul hD hW hW0
          (mul_nonneg (by norm_num) (Real.rpow_nonneg hMpos.le _))
      _ = 52 * M := by rw [← hXY]; ring
      _ ≤ 156 * I := by nlinarith
  have hden : 0 < 2 * variance * I := by
    norm_num [variance]
    exact hIpos
  have htermThree : (2 * D * W) / (2 * variance * I) ≤ 2500 := by
    rw [div_le_iff₀ hden]
    norm_num [variance]
    nlinarith
  apply Real.exp_le_exp.mpr
  unfold localErrorBudget
  dsimp only [D, W, I] at htermOne htermTwo htermThree ⊢
  calc
    2 * (19 / Real.sqrt (i : ℝ) +
          920 * literalShellZeroDeviationRadius m ^ 3 / (i : ℝ) ^ 2) +
        2 * literalShellZeroDeviationRadius m *
          shellZeroWindowSeparation (shellWidth48 m) /
            (2 * variance * (i : ℝ)) =
        38 / Real.sqrt (i : ℝ) +
          1840 * literalShellZeroDeviationRadius m ^ 3 / (i : ℝ) ^ 2 +
          2 * literalShellZeroDeviationRadius m *
            shellZeroWindowSeparation (shellWidth48 m) /
              (2 * variance * (i : ℝ)) := by ring
    _ ≤ 38 + 36382320 + 2500 := by linarith
    _ ≤ 50000000 := by norm_num

theorem eventually_shellZeroWindowArithmeticAt :
    ∀ᶠ m : ℕ in Filter.atTop, ShellZeroWindowArithmeticAt m := by
  have hwidthPower :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      960 kappaOne 1 (by norm_num [kappaOne])
  have hdeviationPower :=
    ExternalProposition44.eventually_const_mul_nat_rpow_le
      4320 (1 - kappaOne) 1 (by norm_num [kappaOne])
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow,
      hwidthPower, hdeviationPower, Filter.eventually_ge_atTop (2 : ℕ)] with
      m hwidth hwidthPowerM hdeviationPowerM hm
  have hmPos : 0 < m := by omega
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast (show 1 ≤ m by omega)
  have hwidthTwo : 2 ≤ shellWidth48 m := by
    unfold shellWidth48
    have honeLt : (1 : ℝ) < (m : ℝ) ^ kappaOne :=
      Real.one_lt_rpow (by exact_mod_cast hm) (by norm_num [kappaOne])
    have honeCeil : 1 < Nat.ceil ((m : ℝ) ^ kappaOne) :=
      Nat.lt_ceil.mpr (by simpa using honeLt)
    omega
  have hwidthLinear : 480 * (shellWidth48 m : ℝ) ≤ (m : ℝ) := by
    simp only [Real.rpow_one] at hwidthPowerM
    nlinarith
  have hdeviationLinear : 240 * geometricDeviation m ≤ (m : ℝ) := by
    simp only [Real.rpow_one, geometricDeviation] at hdeviationPowerM ⊢
    nlinarith
  have hwidthLe : shellWidth48 m ≤ m := by
    have hwidthLinear' : (shellWidth48 m : ℝ) ≤ (m : ℝ) := by
      have hwidthNonneg : (0 : ℝ) ≤ shellWidth48 m := by positivity
      calc
        (shellWidth48 m : ℝ) ≤ 480 * (shellWidth48 m : ℝ) := by nlinarith
        _ ≤ (m : ℝ) := hwidthLinear
    exact_mod_cast hwidthLinear'
  constructor
  · exact hwidthTwo
  constructor
  · exact hwidthLe
  · intro i hi
    have hiPos : 0 < i := by
      have hhalf : 1 ≤ m / 2 := by omega
      omega
    have hiR : (m : ℝ) ≤ 3 * (i : ℝ) := by
      have hnat : m ≤ 3 * i := by omega
      exact_mod_cast hnat
    have hmoderate : literalShellZeroDeviationRadius m ≤ (i : ℝ) / 30 := by
      unfold literalShellZeroDeviationRadius shellZeroDeviationRadius
        shellZeroCenterRadius
      have hradius :
          2 * (shellWidth48 m : ℝ) + geometricDeviation m ≤ (m : ℝ) / 120 := by
        calc
          2 * (shellWidth48 m : ℝ) + geometricDeviation m =
              (1 / 240 : ℝ) * (480 * (shellWidth48 m : ℝ)) +
                (1 / 240 : ℝ) * (240 * geometricDeviation m) := by ring
          _ ≤ (1 / 240 : ℝ) * (m : ℝ) +
                (1 / 240 : ℝ) * (m : ℝ) := by
            exact add_le_add
              (mul_le_mul_of_nonneg_left hwidthLinear (by norm_num))
              (mul_le_mul_of_nonneg_left hdeviationLinear (by norm_num))
          _ = (m : ℝ) / 120 := by ring
      calc
        (shellWidth48 m : ℝ) +
            ((shellWidth48 m : ℝ) + geometricDeviation m) =
            2 * (shellWidth48 m : ℝ) + geometricDeviation m := by ring
        _ ≤ (m : ℝ) / 120 :=
          hradius
        _ ≤ (i : ℝ) / 40 := by nlinarith
        _ ≤ (i : ℝ) / 30 := by
          have hiNonneg : (0 : ℝ) ≤ i := by positivity
          nlinarith
    exact ⟨hiPos, hmoderate,
      adjacentLocalRatio_literalShellZero_le_constant hm hi hwidth⟩

/-! ## The `B_η` threshold-jump disjointness mechanism -/

/-- Data expressing the pathwise reason that HLOZ's replacement events
`B_η` are disjoint.  Each event fixes a trace label at its retained clock,
and at that clock one monotone threshold count jumps from `rank` to
`rank + 1`. -/
structure ThresholdJumpReplacementFamily
    {Omega Index : Type*} [MeasurableSpace Omega]
    (replacement : Index → Set Omega) where
  clock : Index → ℕ
  traceAt : Omega → ℕ → Index
  thresholdCount : Omega → ℕ → ℕ
  monotone_thresholdCount : ∀ omega, Monotone (thresholdCount omega)
  rank : ℕ
  trace_eq : ∀ z omega, omega ∈ replacement z →
    traceAt omega (clock z) = z
  count_before : ∀ z omega, omega ∈ replacement z →
    thresholdCount omega (clock z - 1) = rank
  count_at : ∀ z omega, omega ∈ replacement z →
    thresholdCount omega (clock z) = rank + 1

/-- Distinct replacement labels define disjoint events.  Equal clocks are
separated by the fixed trace label; ordered unequal clocks contradict
monotonicity of the threshold count across the two prescribed jumps. -/
theorem pairwise_disjoint_of_thresholdJumpReplacementFamily
    {Omega Index : Type*} [MeasurableSpace Omega]
    {replacement : Index → Set Omega}
    (data : ThresholdJumpReplacementFamily replacement) :
    Pairwise fun z w ↦ Disjoint (replacement z) (replacement w) := by
  intro z w hzw
  rw [Set.disjoint_left]
  intro omega hz hw
  by_cases hclock : data.clock z = data.clock w
  · apply hzw
    calc
      z = data.traceAt omega (data.clock z) := (data.trace_eq z omega hz).symm
      _ = data.traceAt omega (data.clock w) := by rw [hclock]
      _ = w := data.trace_eq w omega hw
  · rcases lt_or_gt_of_ne hclock with hlt | hgt
    · have htime : data.clock z ≤ data.clock w - 1 := by omega
      have hmono := data.monotone_thresholdCount omega htime
      rw [data.count_at z omega hz, data.count_before w omega hw] at hmono
      omega
    · have htime : data.clock w ≤ data.clock z - 1 := by omega
      have hmono := data.monotone_thresholdCount omega htime
      rw [data.count_at w omega hw, data.count_before z omega hz] at hmono
      omega

/-- Build the global replacement certificate once the atomwise finite-product
comparison, source cover, measurability, and concrete threshold-jump data are
available.  In particular, pairwise disjointness is a conclusion rather than
a probability premise. -/
def globalDisjointReplacementCertificateOfThresholdJump
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) (source : Set Omega) (q : ℝ≥0∞)
    (sourceAtom replacement : Index → Set Omega)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hatom : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z))
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (jump : ThresholdJumpReplacementFamily replacement) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source q where
  sourceAtom := sourceAtom
  replacement := replacement
  source_subset := hsource
  atom_le := hatom
  measurable_replacement := hmeasurable
  disjoint_replacement :=
    pairwise_disjoint_of_thresholdJumpReplacementFamily jump

/-- Preferred source-faithful constructor.  The per-atom input consists of
two exact stopped-trace product-mass identities with a common external
factor and a finite coordinate-product bound.  Thus no premise is the
desired atomwise probability inequality. -/
def globalDisjointReplacementCertificateOfAtomProductsAndThresholdJump
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsFiniteMeasure mu]
    (source : Set Omega) (sourceAtom replacement : Index → Set Omega)
    (q : ℝ)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (jump : ThresholdJumpReplacementFamily replacement)
    (atom : ∀ z, ReplacementAtomProductCertificate
      mu (sourceAtom z) (replacement z) q) :
    GlobalDisjointReplacementCertificate
      (Index := Index) mu source (ENNReal.ofReal q) :=
  globalDisjointReplacementCertificateOfAtomProducts
    mu source sourceAtom replacement q hsource hmeasurable
      (pairwise_disjoint_of_thresholdJumpReplacementFamily jump) atom

/-- Source-correct global shell-zero summation.  The factor `q` is retained
only once, because the replacement events are disjoint by their prescribed
threshold jump. -/
theorem measure_source_le_of_thresholdJumpReplacement
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (q : ℝ≥0∞)
    (sourceAtom replacement : Index → Set Omega)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hatom : ∀ z, mu (sourceAtom z) ≤ q * mu (replacement z))
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (jump : ThresholdJumpReplacementFamily replacement) :
    mu source ≤ q := by
  exact measure_le_of_globalDisjointReplacementCertificate mu source q
    (globalDisjointReplacementCertificateOfThresholdJump
      (Index := Index) mu source q
      sourceAtom replacement hsource hatom hmeasurable jump)

/-- Global probability estimate obtained solely from exact per-atom product
identities and the threshold-jump description of the replacement events. -/
theorem measure_source_le_of_atomProductsAndThresholdJump
    {Omega Index : Type*} [MeasurableSpace Omega] [Countable Index]
    (mu : Measure Omega) [IsProbabilityMeasure mu]
    (source : Set Omega) (sourceAtom replacement : Index → Set Omega)
    (q : ℝ)
    (hsource : source ⊆ ⋃ z, sourceAtom z)
    (hmeasurable : ∀ z, MeasurableSet (replacement z))
    (jump : ThresholdJumpReplacementFamily replacement)
    (atom : ∀ z, ReplacementAtomProductCertificate
      mu (sourceAtom z) (replacement z) q) :
    mu source ≤ ENNReal.ofReal q := by
  exact measure_le_of_globalDisjointReplacementCertificate
    mu source (ENNReal.ofReal q)
      (globalDisjointReplacementCertificateOfAtomProductsAndThresholdJump
        (Index := Index) mu source sourceAtom replacement q hsource
          hmeasurable jump atom)

end

end Erdos1165.HLOZShellZeroReplacementWindows
