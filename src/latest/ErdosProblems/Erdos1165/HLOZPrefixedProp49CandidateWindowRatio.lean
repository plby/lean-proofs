/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZPrefixedAllCreationCanonicalDominantWindows
import ErdosProblems.Erdos1165.HLOZMeshCandidatePolynomialNumerics

/-!
# The concrete Proposition 4.9 candidate window ratio

For a low mesh cell `a`, the narrow local-time window is the final
`gapDeficitCutoff m a` integer values below `m`.  This file compares its
negative-binomial mass with the full first shell-zero strip.  The comparison
keeps the cardinality gain, so its scale is

`m ^ (meshExponent a + meshDelta - kappaOne)`.

The result is deterministic finite-product input.  It has no random-walk or
transition-probability premise.
-/

open Filter

namespace Erdos1165.HLOZPrefixedProp49CandidateWindowRatio

open HLOZPathEvents HLOZProposition48Candidates
open HLOZPrefixedAllCreationCanonicalDominantWindows
open HLOZPrefixedTilingConditionalCoordinateReconstruction
open HLOZShellZeroReplacementWindows
open HLOZTilingConditionalCandidateWindows
open FiniteDominoProductLaw
open NegativeBinomial
open NegativeBinomialLocalCLT
open ScreeningInstantiation SmallWindow
open TilingLazyDecomposition TilingPrefixedInsertedLocalTime
open TilingSpatialInsertionFiber

noncomputable section

/-- A fixed numerical constant for the Proposition 4.9 coordinate ratio. -/
def prop49WindowRatioConstant : ℝ := 4 * shellZeroLocalRatioConstant

lemma prop49WindowRatioConstant_pos : 0 < prop49WindowRatioConstant := by
  unfold prop49WindowRatioConstant
  exact mul_pos (by norm_num) shellZeroLocalRatioConstant_pos

/-- The literal narrow total-local-time window left by the complement of the
low-gap deficit event. -/
def prop49NarrowTotalWindow (m : ℕ) (a : GapScale) : Finset ℕ :=
  Finset.Ico (m - gapDeficitCutoff m a) m

/-- Failure-count coordinates in the narrow total-local-time window after
fixing the external contribution `i`. -/
def prop49NarrowFailureWindow (m : ℕ) (a : GapScale) (i : ℕ) : Finset ℕ :=
  Finset.Ico (m - gapDeficitCutoff m a - i) (m - i)

@[simp] theorem mem_prop49NarrowTotalWindow {m : ℕ} {a : GapScale} {j : ℕ} :
    j ∈ prop49NarrowTotalWindow m a ↔
      m - gapDeficitCutoff m a ≤ j ∧ j < m := by
  simp [prop49NarrowTotalWindow]

@[simp] theorem mem_prop49NarrowFailureWindow
    {m : ℕ} {a : GapScale} {i v : ℕ} :
    v ∈ prop49NarrowFailureWindow m a i ↔
      m - gapDeficitCutoff m a - i ≤ v ∧ v < m - i := by
  simp [prop49NarrowFailureWindow]

theorem prop49NarrowTotalWindow_card
    {m : ℕ} {a : GapScale} (hcut : gapDeficitCutoff m a ≤ m) :
    (prop49NarrowTotalWindow m a).card = gapDeficitCutoff m a := by
  simp [prop49NarrowTotalWindow, Nat.card_Ico]
  omega

theorem prop49NarrowFailureWindow_card
    {m : ℕ} {a : GapScale} {i : ℕ}
    (hcut : gapDeficitCutoff m a ≤ m)
    (hi : i ≤ m - gapDeficitCutoff m a) :
    (prop49NarrowFailureWindow m a i).card = gapDeficitCutoff m a := by
  simp [prop49NarrowFailureWindow, Nat.card_Ico]
  omega

theorem prop49NarrowTotalWindow_subset_source
    {m w : ℕ} {a : GapScale}
    (hw : 1 ≤ w) (hwm : w ≤ m)
    (hcut : gapDeficitCutoff m a ≤ w - 1) :
    prop49NarrowTotalWindow m a ⊆ shellZeroSourceTotalWindow m w := by
  intro j hj
  simp only [mem_prop49NarrowTotalWindow] at hj
  simp only [mem_shellZeroSourceTotalWindow]
  omega

theorem prop49NarrowFailureWindow_subset_source
    {m w i : ℕ} {a : GapScale}
    (hw : 1 ≤ w) (hwm : w ≤ m)
    (hi : i ≤ m - w + 1)
    (hcut : gapDeficitCutoff m a ≤ w - 1) :
    prop49NarrowFailureWindow m a i ⊆
      shellZeroSourceFailureWindow m w i := by
  intro v hv
  simp only [mem_prop49NarrowFailureWindow] at hv
  simp only [mem_shellZeroSourceFailureWindow]
  omega

/-- Both failure-count coordinates in the source strip are separated by at
most the shell comparison width. -/
theorem sourceFailure_pair_deviation_sub_le
    {m w i u v : ℕ}
    (hi : i ≤ m - w + 1) (hwm : w ≤ m)
    (hu : u ∈ shellZeroSourceFailureWindow m w i)
    (hv : v ∈ shellZeroSourceFailureWindow m w i) :
    |deviation i u - deviation i v| ≤ shellZeroWindowSeparation w := by
  have hu' := hu
  have hv' := hv
  simp only [mem_shellZeroSourceFailureWindow] at hu' hv'
  have huvLeft : v ≤ u + w := by omega
  have huvRight : u ≤ v + w := by omega
  have huv : |(u : ℝ) - (v : ℝ)| ≤ (w : ℝ) := by
    rw [abs_le]
    constructor
    · have h : (v : ℝ) ≤ (u : ℝ) + w := by exact_mod_cast huvLeft
      linarith
    · have h : (u : ℝ) ≤ (v : ℝ) + w := by exact_mod_cast huvRight
      linarith
  have heq : deviation i u - deviation i v = (u : ℝ) - (v : ℝ) := by
    unfold deviation
    ring
  rw [heq]
  unfold shellZeroWindowSeparation
  have hw : (0 : ℝ) ≤ w := by positivity
  linarith

/-- Exact shifted-coordinate realization of the narrow window. -/
theorem shiftedEndpointWindow_prop49NarrowTotalWindow
    {m upper i : ℕ} {a : GapScale}
    (hcut : gapDeficitCutoff m a ≤ m)
    (_hi : i ≤ m - gapDeficitCutoff m a)
    (hupper : m - i ≤ upper) :
    shiftedEndpointWindow i upper (prop49NarrowTotalWindow m a) =
      prop49NarrowFailureWindow m a i := by
  ext v
  simp only [shiftedEndpointWindow, Finset.mem_filter, Finset.mem_range,
    mem_prop49NarrowTotalWindow, mem_prop49NarrowFailureWindow]
  omega

/-- Exact shifted-coordinate realization of the broad first strip. -/
theorem shiftedEndpointWindow_shellZeroSourceTotalWindow
    {m w upper i : ℕ}
    (hi : i ≤ m - w + 1) (_hwm : w ≤ m)
    (hupper : m - i ≤ upper) :
    shiftedEndpointWindow i upper (shellZeroSourceTotalWindow m w) =
      shellZeroSourceFailureWindow m w i := by
  ext v
  simp only [shiftedEndpointWindow, Finset.mem_filter, Finset.mem_range,
    mem_shellZeroSourceTotalWindow, mem_shellZeroSourceFailureWindow]
  omega

/-! ## Ceiling and power arithmetic -/

lemma gapDeficitCutoff_cast_le_two_rpow
    {m : ℕ} (hm : 1 ≤ m) (a : GapScale) :
    (gapDeficitCutoff m a : ℝ) ≤
      2 * (m : ℝ) ^ (meshExponent a + meshDelta) := by
  let x : ℝ := (m : ℝ) ^ (meshExponent a + meshDelta)
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hexponent : 0 ≤ meshExponent a + meshDelta := by
    have hmesh : 0 ≤ meshExponent a := by
      unfold meshExponent
      exact mul_nonneg (by positivity) (by norm_num [meshDelta])
    have hdelta : 0 ≤ meshDelta := by norm_num [meshDelta]
    linarith
  have hxOne : 1 ≤ x := by
    dsimp only [x]
    exact Real.one_le_rpow hmR hexponent
  have hceil : (Nat.ceil x : ℝ) < x + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (Nat.cast_nonneg m) _)
  simpa only [gapDeficitCutoff, x] using hceil.le.trans (by linarith)

lemma half_rpow_kappaOne_le_shellWidth48_pred
    {m : ℕ} (hpow : 2 ≤ (m : ℝ) ^ kappaOne) :
    (m : ℝ) ^ kappaOne / 2 ≤ (shellWidth48 m - 1 : ℕ) := by
  have hceil : (m : ℝ) ^ kappaOne ≤ (shellWidth48 m : ℕ) := by
    exact Nat.le_ceil _
  have hwidthTwo : 2 ≤ shellWidth48 m := by
    exact_mod_cast hpow.trans hceil
  rw [Nat.cast_sub (by omega : 1 ≤ shellWidth48 m)]
  push_cast
  linarith

lemma rpow_ratio_mul_rpow_kappaOne
    {m : ℕ} (hm : 1 ≤ m) (a : GapScale) :
    (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) *
        (m : ℝ) ^ kappaOne =
      (m : ℝ) ^ (meshExponent a + meshDelta) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  rw [← Real.rpow_add hmR]
  congr 1
  ring

/-- The eventual arithmetic package used by the pathwise candidate fibre. -/
structure Prop49WindowArithmeticAt (m : ℕ) (a : GapScale) : Prop where
  cut_le_width_pred : gapDeficitCutoff m a ≤ shellWidth48 m - 1
  coefficient_le :
    shellZeroLocalRatioConstant * (gapDeficitCutoff m a : ℝ) /
        (shellWidth48 m - 1 : ℕ) ≤
      prop49WindowRatioConstant *
        (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)

theorem eventually_prop49WindowArithmeticAt
    (a : GapScale) (ha : a ∈ lowGapMesh) :
    ∀ᶠ m : ℕ in atTop, Prop49WindowArithmeticAt m a := by
  have hexponentPos : 0 < meshExponent a + meshDelta := by
    have hmesh : 0 < meshExponent a := by
      unfold meshExponent
      exact mul_pos (by positivity) (by norm_num [meshDelta])
    have hdelta : 0 < meshDelta := by norm_num [meshDelta]
    linarith
  have hexponentLt : meshExponent a + meshDelta < kappaOne := by
    have hlow := (mem_lowGapMesh_iff.mp ha).2
    norm_num [kappaTwo, meshDelta, kappaOne] at hlow ⊢
    linarith
  have hdom := ExternalProposition44.eventually_const_mul_nat_rpow_le
    4 (meshExponent a + meshDelta) kappaOne hexponentLt
  have hpow := (tendsto_nat_rpow_atTop (a := kappaOne)
    (by norm_num [kappaOne])).eventually
    (eventually_ge_atTop (2 : ℝ))
  filter_upwards [hdom, hpow, eventually_ge_atTop (1 : ℕ)] with
      m hdomM hpowM hm
  have hcutUpper := gapDeficitCutoff_cast_le_two_rpow hm a
  have hwidthLower := half_rpow_kappaOne_le_shellWidth48_pred hpowM
  have hbaseOne : 1 ≤ (m : ℝ) ^ (meshExponent a + meshDelta) := by
    exact Real.one_le_rpow (by exact_mod_cast hm) hexponentPos.le
  have hwidthCeil : (m : ℝ) ^ kappaOne ≤ (shellWidth48 m : ℕ) := by
    exact Nat.le_ceil _
  have hcutSuccReal : (gapDeficitCutoff m a : ℝ) + 1 ≤
      (shellWidth48 m : ℕ) := by
    calc
      (gapDeficitCutoff m a : ℝ) + 1 ≤
          2 * (m : ℝ) ^ (meshExponent a + meshDelta) + 1 := by
        linarith
      _ ≤ 4 * (m : ℝ) ^ (meshExponent a + meshDelta) := by
        linarith
      _ ≤ (m : ℝ) ^ kappaOne := hdomM
      _ ≤ (shellWidth48 m : ℕ) := hwidthCeil
  have hcut : gapDeficitCutoff m a ≤ shellWidth48 m - 1 := by
    have hcutSucc : gapDeficitCutoff m a + 1 ≤ shellWidth48 m := by
      exact_mod_cast hcutSuccReal
    omega
  refine ⟨hcut, ?_⟩
  have hdenPos : (0 : ℝ) < (shellWidth48 m - 1 : ℕ) := by
    have : 1 < shellWidth48 m := by
      have : (2 : ℝ) ≤ shellWidth48 m := hpowM.trans hwidthCeil
      exact_mod_cast this
    exact_mod_cast Nat.sub_pos_of_lt this
  rw [div_le_iff₀ hdenPos]
  have hratioNonneg :
      0 ≤ (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne) :=
    Real.rpow_nonneg (Nat.cast_nonneg m) _
  have hconstantPos : 0 < shellZeroLocalRatioConstant :=
    shellZeroLocalRatioConstant_pos
  calc
    shellZeroLocalRatioConstant * (gapDeficitCutoff m a : ℝ) ≤
        shellZeroLocalRatioConstant *
          (2 * (m : ℝ) ^ (meshExponent a + meshDelta)) := by
      gcongr
    _ = 2 * shellZeroLocalRatioConstant *
        (m : ℝ) ^ (meshExponent a + meshDelta) := by ring
    _ = (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        ((m : ℝ) ^ kappaOne / 2) := by
      rw [prop49WindowRatioConstant,
        ← rpow_ratio_mul_rpow_kappaOne hm a]
      ring
    _ ≤ (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        (shellWidth48 m - 1 : ℕ) := by
      gcongr
      exact mul_nonneg prop49WindowRatioConstant_pos.le hratioNonneg

/-! ## The exact local-CLT cardinality ratio -/

/-- The selected narrow coordinate gains its full lattice-cardinality ratio
against the broad first strip.  The very large constant is the already
checked, uniform shell-zero local-CLT constant; it does not depend on the
mesh cell or on `m`. -/
theorem narrowFailureWindowMass_le_shellZeroLocalRatio_mul_cardRatio
    {m i : ℕ} (a : GapScale)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hthick : m / 2 ≤ i)
    (htranslate : i ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroCenterRadius m)
    (hcut : gapDeficitCutoff m a ≤ shellWidth48 m - 1) :
    windowMass i (prop49NarrowFailureWindow m a i) ≤
      (shellZeroLocalRatioConstant * (gapDeficitCutoff m a : ℝ) /
          (shellWidth48 m - 1 : ℕ)) *
        windowMass i
          (shellZeroSourceFailureWindow m (shellWidth48 m) i) := by
  let broad := shellZeroSourceFailureWindow m (shellWidth48 m) i
  let narrow := prop49NarrowFailureWindow m a i
  let D := literalShellZeroDeviationRadius m
  let W := shellZeroWindowSeparation (shellWidth48 m)
  have hlocal := harithmetic.2.2 i hthick
  have hcutm : gapDeficitCutoff m a ≤ m := by
    have hwm := harithmetic.2.1
    omega
  have hiNarrow : i ≤ m - gapDeficitCutoff m a := by
    apply Nat.le_sub_of_add_le
    have hmw : m - shellWidth48 m + shellWidth48 m = m :=
      Nat.sub_add_cancel harithmetic.2.1
    calc
      i + gapDeficitCutoff m a ≤ i + (shellWidth48 m - 1) := by
        exact Nat.add_le_add_left hcut i
      _ ≤ (m - shellWidth48 m + 1) + (shellWidth48 m - 1) :=
        Nat.add_le_add_right htranslate _
      _ = (m - shellWidth48 m) +
          (1 + (shellWidth48 m - 1)) := by
        simp only [Nat.add_assoc]
      _ = (m - shellWidth48 m) + shellWidth48 m := by
        rw [Nat.add_sub_of_le
          ((show 1 ≤ 2 by norm_num).trans harithmetic.1)]
      _ = m := hmw
  have hnarrowSubset : narrow ⊆ broad := by
    dsimp only [narrow, broad]
    exact prop49NarrowFailureWindow_subset_source
      ((show 1 ≤ 2 by norm_num).trans harithmetic.1)
      harithmetic.2.1 htranslate hcut
  have hbroadNonempty : broad.Nonempty := by
    dsimp only [broad]
    exact shellZeroSourceFailureWindow_nonempty htranslate harithmetic.1
      harithmetic.2.1
  obtain ⟨b, hb, hbmin⟩ :=
    Finset.exists_min_image broad (hlozMass i) hbroadNonempty
  have hbPos : 0 < hlozMass i b := hlozMass_pos hlocal.1 b
  have hD0 : 0 ≤ D := by
    dsimp only [D, literalShellZeroDeviationRadius, shellZeroDeviationRadius,
      shellZeroCenterRadius]
    exact add_nonneg (Nat.cast_nonneg _)
      (add_nonneg (Nat.cast_nonneg _) (geometricDeviation_nonneg m))
  have hW0 : 0 ≤ W := by
    dsimp only [W]
    exact shellZeroWindowSeparation_nonneg _
  have hsmallCard : (narrow.card : ℝ) ≤ gapDeficitCutoff m a := by
    rw [show narrow.card = gapDeficitCutoff m a by
      dsimp only [narrow]
      exact prop49NarrowFailureWindow_card hcutm hiNarrow]
  have hlargeCard : ((shellWidth48 m - 1 : ℕ) : ℝ) ≤ broad.card := by
    rw [show broad.card = shellWidth48 m - 1 by
      dsimp only [broad]
      exact shellZeroSourceFailureWindow_card htranslate harithmetic.2.1]
  have hsmallPoint : ∀ v ∈ narrow,
      hlozMass i v ≤ adjacentLocalRatio i D W * hlozMass i b := by
    intro v hv
    have hvBroad := hnarrowSubset hv
    apply hlozMass_le_adjacentLocalRatio_mul hlocal.1 hD0 hW0
    · dsimp only [D]
      exact sourceFailure_deviation_le htranslate harithmetic.2.1 hcenter
        hvBroad
    · dsimp only [D]
      exact sourceFailure_deviation_le htranslate harithmetic.2.1 hcenter hb
    · dsimp only [W]
      exact sourceFailure_pair_deviation_sub_le htranslate harithmetic.2.1
        hvBroad hb
    · simpa only [D] using hlocal.2.1
  have hraw := windowMass_small_le_ratio_mul_large
    (i := i) (small := narrow) (large := broad)
    (b := hlozMass i b) (C := adjacentLocalRatio i D W)
    (g := (gapDeficitCutoff m a : ℝ))
    (f := ((shellWidth48 m - 1 : ℕ) : ℝ))
    hbPos (adjacentLocalRatio_nonneg i D W) (Nat.cast_nonneg _)
    (by
      exact_mod_cast
        (Nat.sub_pos_of_lt (show 1 < shellWidth48 m from harithmetic.1)))
    hsmallCard hlargeCard hsmallPoint (fun v hv ↦ hbmin v hv)
  have hmassNonneg : 0 ≤ windowMass i broad := windowMass_nonneg _ _
  calc
    windowMass i (prop49NarrowFailureWindow m a i) =
        windowMass i narrow := by rfl
    _ ≤ (adjacentLocalRatio i D W * (gapDeficitCutoff m a : ℝ) /
          (shellWidth48 m - 1 : ℕ)) * windowMass i broad := hraw
    _ ≤ (shellZeroLocalRatioConstant * (gapDeficitCutoff m a : ℝ) /
          (shellWidth48 m - 1 : ℕ)) * windowMass i broad := by
      gcongr
      simpa only [D, W] using hlocal.2.2
    _ = (shellZeroLocalRatioConstant * (gapDeficitCutoff m a : ℝ) /
          (shellWidth48 m - 1 : ℕ)) *
        windowMass i
          (shellZeroSourceFailureWindow m (shellWidth48 m) i) := by rfl

/-- Pointwise polynomial form of Proposition 4.9's chosen-coordinate ratio. -/
theorem narrowFailureWindowMass_le_prop49Envelope
    {m i : ℕ} (a : GapScale)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hthick : m / 2 ≤ i)
    (htranslate : i ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroCenterRadius m) :
    windowMass i (prop49NarrowFailureWindow m a i) ≤
      (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        windowMass i
          (shellZeroSourceFailureWindow m (shellWidth48 m) i) := by
  have hraw := narrowFailureWindowMass_le_shellZeroLocalRatio_mul_cardRatio
    a harithmetic hthick htranslate hcenter hwindow.cut_le_width_pred
  exact hraw.trans (mul_le_mul_of_nonneg_right hwindow.coefficient_le
    (windowMass_nonneg _ _))

/-- The same ratio in the precise shifted windows appearing in
`PrefixedCanonicalDominantCandidateWindowSpec`. -/
theorem shiftedEndpointWindow_prop49_mass_le
    {m i upper : ℕ} (a : GapScale)
    (hwindow : Prop49WindowArithmeticAt m a)
    (harithmetic : ShellZeroWindowArithmeticAt m)
    (hthick : m / 2 ≤ i)
    (htranslate : i ≤ m - shellWidth48 m + 1)
    (hcenter : |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
      shellZeroCenterRadius m)
    (hupper : m - i ≤ upper) :
    windowMass i
        (shiftedEndpointWindow i upper (prop49NarrowTotalWindow m a)) ≤
      (prop49WindowRatioConstant *
          (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
        windowMass i
          (shiftedEndpointWindow i upper
            (shellZeroSourceTotalWindow m (shellWidth48 m))) := by
  have hcutm : gapDeficitCutoff m a ≤ m := by
    exact hwindow.cut_le_width_pred.trans
      ((Nat.sub_le _ _).trans harithmetic.2.1)
  have hiNarrow : i ≤ m - gapDeficitCutoff m a := by
    apply Nat.le_sub_of_add_le
    have hmw : m - shellWidth48 m + shellWidth48 m = m :=
      Nat.sub_add_cancel harithmetic.2.1
    calc
      i + gapDeficitCutoff m a ≤ i + (shellWidth48 m - 1) :=
        Nat.add_le_add_left hwindow.cut_le_width_pred i
      _ ≤ (m - shellWidth48 m + 1) + (shellWidth48 m - 1) :=
        Nat.add_le_add_right htranslate _
      _ = (m - shellWidth48 m) +
          (1 + (shellWidth48 m - 1)) := by
        simp only [Nat.add_assoc]
      _ = (m - shellWidth48 m) + shellWidth48 m := by
        rw [Nat.add_sub_of_le
          ((show 1 ≤ 2 by norm_num).trans harithmetic.1)]
      _ = m := hmw
  rw [shiftedEndpointWindow_prop49NarrowTotalWindow hcutm hiNarrow hupper,
    shiftedEndpointWindow_shellZeroSourceTotalWindow htranslate
      harithmetic.2.1 hupper]
  exact narrowFailureWindowMass_le_prop49Envelope a hwindow harithmetic
    hthick htranslate hcenter

/-- Uniform eventual shifted-window ratio on every fixed low mesh cell. -/
theorem eventually_shiftedEndpointWindow_prop49_mass_le
    (a : GapScale) (ha : a ∈ lowGapMesh) :
    ∀ᶠ m : ℕ in atTop, ∀ i upper : ℕ,
      m / 2 ≤ i →
      i ≤ m - shellWidth48 m + 1 →
      |(m : ℝ) - (16 / 15 : ℝ) * (i : ℝ)| ≤
        shellZeroCenterRadius m →
      m - i ≤ upper →
      windowMass i
          (shiftedEndpointWindow i upper (prop49NarrowTotalWindow m a)) ≤
        (prop49WindowRatioConstant *
            (m : ℝ) ^ (meshExponent a + meshDelta - kappaOne)) *
          windowMass i
            (shiftedEndpointWindow i upper
              (shellZeroSourceTotalWindow m (shellWidth48 m))) := by
  filter_upwards [eventually_prop49WindowArithmeticAt a ha,
      eventually_shellZeroWindowArithmeticAt] with m hwindow harithmetic
  intro i upper hthick htranslate hcenter hupper
  exact shiftedEndpointWindow_prop49_mass_le a hwindow harithmetic hthick
    htranslate hcenter hupper

end

end Erdos1165.HLOZPrefixedProp49CandidateWindowRatio
