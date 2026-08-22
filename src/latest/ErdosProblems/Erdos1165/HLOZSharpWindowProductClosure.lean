/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors.
-/

import ErdosProblems.Erdos1165.HLOZSharpProductNumerics

/-!
# Sharp active-window constructor for the all-six product screen

Only spatial dominoes with external multiplicity at least `m / 2` belong to
the HLOZ thick-site screen.  The inactive coordinates therefore use empty
windows.  On active coordinates the two consecutive windows have the true
HLOZ strip width `shellWidth48 m`, and the checked negative-binomial local
CLT supplies the mass comparison.  The final Chernoff envelope is the sharp
one from `HLOZSharpProductNumerics`, not the crude cardinality bound.
-/

open Filter Set
open scoped ENNReal BigOperators

namespace Erdos1165.HLOZSharpWindowProductClosure

open FiniteDominoProductLaw HLOZAllSixBandProductClosure
open HLOZAllSixExactCoordinateProductClosure HLOZProposition48Candidates
open HLOZSharpProductNumerics NearFavoriteThresholded
open ScreeningInstantiation TilingAwayNegativeBinomial
open TilingCappedMarginalization TilingSpatialInsertionFiber

noncomputable section

/-- Lower adjacent failure window, restricted to coordinates in the thick
external-multiplicity range. -/
def activeLowerFailureWindow (m i : ℕ) : Finset ℕ :=
  if m / 2 ≤ i then lowerFailureWindow i (shellWidth48 m) else ∅

/-- Upper adjacent failure window, with the same activity restriction. -/
def activeUpperFailureWindow (m i : ℕ) : Finset ℕ :=
  if m / 2 ≤ i then upperFailureWindow i (shellWidth48 m) else ∅

lemma activeLowerFailureWindow_eq_of_active {m i : ℕ} (h : m / 2 ≤ i) :
    activeLowerFailureWindow m i = lowerFailureWindow i (shellWidth48 m) := by
  simp [activeLowerFailureWindow, h]

lemma activeUpperFailureWindow_eq_of_active {m i : ℕ} (h : m / 2 ≤ i) :
    activeUpperFailureWindow m i = upperFailureWindow i (shellWidth48 m) := by
  simp [activeUpperFailureWindow, h]

lemma activeLowerFailureWindow_eq_empty_of_inactive {m i : ℕ}
    (h : ¬m / 2 ≤ i) : activeLowerFailureWindow m i = ∅ := by
  simp [activeLowerFailureWindow, h]

lemma activeUpperFailureWindow_eq_empty_of_inactive {m i : ℕ}
    (h : ¬m / 2 ≤ i) : activeUpperFailureWindow m i = ∅ := by
  simp [activeUpperFailureWindow, h]

/-- All level-dependent analytic arithmetic needed by the active windows.
The next theorem isolates the asymptotic proof of this proposition from the
literal stopped-fibre data. -/
def SharpWindowArithmeticAt (m : ℕ) : Prop :=
  0 < shellWidth48 m ∧
    ∀ i, m / 2 ≤ i →
      0 < i ∧
      adjacentWindowRadius (shellWidth48 m) ≤ (i : ℝ) / 30 ∧
      adjacentLocalRatio i (adjacentWindowRadius (shellWidth48 m))
          (adjacentWindowSeparation (shellWidth48 m)) ≤ 4 / 3

/-- A convenient explicit majorant for the logarithm of the active-window
local ratio.  Its three powers are respectively `-1/2`, `3κ₁-2`, and
`2κ₁-1`. -/
noncomputable def sharpWindowErrorMajorant (m : ℕ) : ℝ :=
  76 * (m : ℝ) ^ (-(1 / 2 : ℝ)) +
    2070000 * (m : ℝ) ^ (-(31 / 32 : ℝ)) +
      900 * (m : ℝ) ^ (-(5 / 16 : ℝ))

lemma tendsto_sharpWindowErrorMajorant_zero :
    Tendsto sharpWindowErrorMajorant atTop (nhds 0) := by
  unfold sharpWindowErrorMajorant
  have hhalf : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (-(1 / 2 : ℝ))) atTop
      (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (1 / 2 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hthirtyOne : Tendsto
      (fun m : ℕ ↦ (m : ℝ) ^ (-(31 / 32 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (31 / 32 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  have hfive : Tendsto
      (fun m : ℕ ↦ (m : ℝ) ^ (-(5 / 16 : ℝ))) atTop (nhds 0) :=
    (tendsto_rpow_neg_atTop (by norm_num : 0 < (5 / 16 : ℝ))).comp
      tendsto_natCast_atTop_atTop
  convert ((hhalf.const_mul (76 : ℝ)).add
      (hthirtyOne.const_mul (2070000 : ℝ))).add
        (hfive.const_mul (900 : ℝ)) using 1
  norm_num

lemma eventually_sharpWindowErrorMajorant_le_quarter :
    ∀ᶠ m : ℕ in atTop, sharpWindowErrorMajorant m ≤ 1 / 4 := by
  exact tendsto_sharpWindowErrorMajorant_zero.eventually
    (eventually_le_nhds (by norm_num : (0 : ℝ) < 1 / 4))

lemma eventually_shellWidth48_cast_le_two_rpow :
    ∀ᶠ m : ℕ in atTop,
      (shellWidth48 m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne := by
  filter_upwards [eventually_ge_atTop (1 : ℕ)] with m hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 1 ≤ (m : ℝ) ^ kappaOne :=
    Real.one_le_rpow hmR (by norm_num [kappaOne])
  have hceil := Nat.ceil_lt_add_one
    (Real.rpow_nonneg (Nat.cast_nonneg m) kappaOne)
  unfold shellWidth48
  linarith

lemma eventually_shellWidth48_moderate_nat :
    ∀ᶠ m : ℕ in atTop, 2 * (60 * shellWidth48 m + 30) ≤ m := by
  have hpower := ExternalProposition44.eventually_const_mul_nat_rpow_le
    480 kappaOne 1 (by norm_num [kappaOne])
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow, hpower,
      eventually_ge_atTop (1 : ℕ)] with m hwidth hpowerM hm
  have hmR : (1 : ℝ) ≤ m := by exact_mod_cast hm
  have hx : 1 ≤ (m : ℝ) ^ kappaOne :=
    Real.one_le_rpow hmR (by norm_num [kappaOne])
  have hreal : ((2 * (60 * shellWidth48 m + 30) : ℕ) : ℝ) ≤ (m : ℝ) := by
    simp only [Real.rpow_one] at hpowerM
    push_cast
    nlinarith
  exact_mod_cast hreal

lemma rpow_kappaOne_cube_div_square {m : ℕ} (hm : 0 < m) :
    (((m : ℝ) ^ kappaOne) ^ 3) / (m : ℝ) ^ 2 =
      (m : ℝ) ^ (-(31 / 32 : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (((m : ℝ) ^ kappaOne) ^ 3) / (m : ℝ) ^ 2 =
        ((m : ℝ) ^ kappaOne) ^ (3 : ℝ) / (m : ℝ) ^ (2 : ℝ) := by
      congr 1
      · exact (Real.rpow_natCast ((m : ℝ) ^ kappaOne) 3).symm
      · exact (Real.rpow_natCast (m : ℝ) 2).symm
    _ = (m : ℝ) ^ (kappaOne * 3) / (m : ℝ) ^ (2 : ℝ) := by
      rw [(Real.rpow_mul hmR.le kappaOne 3).symm]
    _ = (m : ℝ) ^ (kappaOne * 3 - 2) := by
      rw [Real.rpow_sub hmR]
    _ = (m : ℝ) ^ (-(31 / 32 : ℝ)) := by
      congr 1
      norm_num [kappaOne]

lemma rpow_kappaOne_square_div_self {m : ℕ} (hm : 0 < m) :
    (((m : ℝ) ^ kappaOne) ^ 2) / (m : ℝ) =
      (m : ℝ) ^ (-(5 / 16 : ℝ)) := by
  have hmR : (0 : ℝ) < m := by exact_mod_cast hm
  calc
    (((m : ℝ) ^ kappaOne) ^ 2) / (m : ℝ) =
        ((m : ℝ) ^ kappaOne) ^ (2 : ℝ) / (m : ℝ) ^ (1 : ℝ) := by
      congr 1
      · exact (Real.rpow_natCast ((m : ℝ) ^ kappaOne) 2).symm
      · rw [Real.rpow_one]
    _ = (m : ℝ) ^ (kappaOne * 2) / (m : ℝ) ^ (1 : ℝ) := by
      rw [(Real.rpow_mul hmR.le kappaOne 2).symm]
    _ = (m : ℝ) ^ (kappaOne * 2 - 1) := by
      rw [Real.rpow_sub hmR]
    _ = (m : ℝ) ^ (-(5 / 16 : ℝ)) := by
      congr 1
      norm_num [kappaOne]

lemma adjacentLocalRatio_shellWidth48_le_four_thirds
    {m i : ℕ} (hm : 6 ≤ m) (hi : m / 2 ≤ i)
    (hwidth : (shellWidth48 m : ℝ) ≤ 2 * (m : ℝ) ^ kappaOne)
    (herror : sharpWindowErrorMajorant m ≤ 1 / 4) :
    adjacentLocalRatio i (adjacentWindowRadius (shellWidth48 m))
        (adjacentWindowSeparation (shellWidth48 m)) ≤ 4 / 3 := by
  let M : ℝ := m
  let I : ℝ := i
  let X : ℝ := M ^ kappaOne
  let D : ℝ := adjacentWindowRadius (shellWidth48 m)
  let W : ℝ := adjacentWindowSeparation (shellWidth48 m)
  have hmPos : 0 < m := by omega
  have hiPos : 0 < i := by omega
  have hMpos : 0 < M := by
    dsimp only [M]
    exact_mod_cast hmPos
  have hIpos : 0 < I := by
    dsimp only [I]
    exact_mod_cast hiPos
  have hXone : 1 ≤ X := by
    apply Real.one_le_rpow
    · dsimp only [X, M]
      exact_mod_cast (show 1 ≤ m by omega)
    · norm_num [kappaOne]
  have hmiNat : m ≤ 3 * i := by omega
  have hmi : M ≤ 3 * I := by
    dsimp only [M, I]
    exact_mod_cast hmiNat
  have hD0 : 0 ≤ D := adjacentWindowRadius_nonneg _
  have hW0 : 0 ≤ W := adjacentWindowSeparation_nonneg _
  have hD : D ≤ 5 * X := by
    dsimp only [D, X, M]
    unfold adjacentWindowRadius
    nlinarith
  have hW : W ≤ 4 * X := by
    dsimp only [W, X, M]
    unfold adjacentWindowSeparation
    nlinarith
  have hsqrtM : Real.sqrt M ≤ 2 * Real.sqrt I := by
    have hmono : Real.sqrt M ≤ Real.sqrt (3 * I) :=
      Real.sqrt_le_sqrt hmi
    have hsqrt3 : Real.sqrt (3 : ℝ) ≤ 2 := by
      nlinarith [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3),
        Real.sqrt_nonneg 3]
    calc
      Real.sqrt M ≤ Real.sqrt (3 * I) := hmono
      _ = Real.sqrt 3 * Real.sqrt I := by
        rw [Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 3)]
      _ ≤ 2 * Real.sqrt I := by
        gcongr
  have hsqrtMpos : 0 < Real.sqrt M := Real.sqrt_pos.2 hMpos
  have hsqrtIpos : 0 < Real.sqrt I := Real.sqrt_pos.2 hIpos
  have htermOne : 38 / Real.sqrt I ≤ 76 / Real.sqrt M := by
    rw [div_le_div_iff₀ hsqrtIpos hsqrtMpos]
    nlinarith
  have hDcube : D ^ 3 ≤ 125 * X ^ 3 := by
    calc
      D ^ 3 ≤ (5 * X) ^ 3 := pow_le_pow_left₀ hD0 hD 3
      _ = 125 * X ^ 3 := by ring
  have hMsq : M ^ 2 ≤ 9 * I ^ 2 := by nlinarith
  have htermTwo : 1840 * D ^ 3 / I ^ 2 ≤
      2070000 * X ^ 3 / M ^ 2 := by
    rw [div_le_div_iff₀ (sq_pos_of_pos hIpos) (sq_pos_of_pos hMpos)]
    calc
      1840 * D ^ 3 * M ^ 2 ≤
          1840 * (125 * X ^ 3) * (9 * I ^ 2) := by
        calc
          1840 * D ^ 3 * M ^ 2 ≤
              1840 * (125 * X ^ 3) * M ^ 2 := by
            gcongr
          _ ≤ 1840 * (125 * X ^ 3) * (9 * I ^ 2) := by
            gcongr
      _ = 2070000 * X ^ 3 * I ^ 2 := by ring
  have hDW : D * W ≤ 20 * X ^ 2 := by
    calc
      D * W ≤ (5 * X) * (4 * X) :=
        mul_le_mul hD hW hW0
          (mul_nonneg (by norm_num) ((by norm_num : (0 : ℝ) ≤ 1).trans hXone))
      _ = 20 * X ^ 2 := by ring
  have hden : 0 < 2 * NegativeBinomialLocalCLT.variance * I := by
    norm_num [NegativeBinomialLocalCLT.variance]
    exact hIpos
  have htermThree : (2 * D * W) /
      (2 * NegativeBinomialLocalCLT.variance * I) ≤
        900 * X ^ 2 / M := by
    rw [div_le_div_iff₀ hden hMpos]
    calc
      2 * D * W * M = 2 * (D * W) * M := by ring
      _ ≤ 2 * (20 * X ^ 2) * M := by
        gcongr
      _ ≤ 2 * (20 * X ^ 2) * (3 * I) := by
        gcongr
      _ ≤ 900 * X ^ 2 *
          (2 * NegativeBinomialLocalCLT.variance * I) := by
        norm_num [NegativeBinomialLocalCLT.variance]
        nlinarith [mul_nonneg (sq_nonneg X) hIpos.le]
  have hhalfIdentity : M ^ (-(1 / 2 : ℝ)) = 1 / Real.sqrt M := by
    rw [Real.rpow_neg hMpos.le, ← Real.sqrt_eq_rpow]
    simp only [one_div]
  have hcubeIdentity : X ^ 3 / M ^ 2 = M ^ (-(31 / 32 : ℝ)) := by
    simpa only [X, M] using rpow_kappaOne_cube_div_square hmPos
  have hsquareIdentity : X ^ 2 / M = M ^ (-(5 / 16 : ℝ)) := by
    simpa only [X, M] using rpow_kappaOne_square_div_self hmPos
  have hexponent :
      2 * localErrorBudget i D +
          (2 * D * W) /
            (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) ≤
        sharpWindowErrorMajorant m := by
    unfold localErrorBudget sharpWindowErrorMajorant
    dsimp only [I] at htermOne htermTwo htermThree
    dsimp only [M] at hhalfIdentity hcubeIdentity hsquareIdentity
    rw [hhalfIdentity, ← hcubeIdentity, ← hsquareIdentity]
    calc
      2 * (19 / Real.sqrt (i : ℝ) + 920 * D ^ 3 / (i : ℝ) ^ 2) +
          (2 * D * W) /
            (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) =
          38 / Real.sqrt (i : ℝ) + 1840 * D ^ 3 / (i : ℝ) ^ 2 +
            (2 * D * W) /
              (2 * NegativeBinomialLocalCLT.variance * (i : ℝ)) := by ring
      _ ≤ 76 / Real.sqrt M + 2070000 * X ^ 3 / M ^ 2 +
            900 * X ^ 2 / M :=
        add_le_add (add_le_add htermOne htermTwo) htermThree
      _ = 76 * (1 / Real.sqrt M) +
          2070000 * (X ^ 3 / M ^ 2) + 900 * (X ^ 2 / M) := by ring
  have hexpQuarter : Real.exp
      (2 * localErrorBudget i D +
        (2 * D * W) /
          (2 * NegativeBinomialLocalCLT.variance * (i : ℝ))) ≤
      Real.exp (1 / 4) := Real.exp_le_exp.mpr (hexponent.trans herror)
  have hquarter : Real.exp (1 / 4 : ℝ) ≤ 4 / 3 := by
    calc
      Real.exp (1 / 4 : ℝ) ≤
          (2 + (1 / 4 : ℝ)) / (2 - 1 / 4) :=
        Real.exp_le_two_add_div_two_sub (x := (1 / 4 : ℝ))
          (by norm_num) (by norm_num)
      _ ≤ 4 / 3 := by norm_num
  exact hexpQuarter.trans hquarter

/-- All active-window local-CLT hypotheses hold from one explicit eventual
level onward.  In particular no coordinatewise analytic premise is left in
the stopped-product constructor below. -/
theorem eventually_sharpWindowArithmeticAt :
    ∀ᶠ m : ℕ in atTop, SharpWindowArithmeticAt m := by
  filter_upwards [eventually_shellWidth48_cast_le_two_rpow,
      eventually_shellWidth48_moderate_nat,
      eventually_sharpWindowErrorMajorant_le_quarter,
      eventually_ge_atTop (6 : ℕ)] with m hwidth hmoderate herror hm
  have hmPos : 0 < m := by omega
  constructor
  · unfold shellWidth48
    exact Nat.ceil_pos.mpr (Real.rpow_pos_of_pos (by exact_mod_cast hmPos) _)
  · intro i hi
    have hiPos : 0 < i := by omega
    have hscale : 60 * shellWidth48 m + 30 ≤ i := by omega
    exact ⟨hiPos, adjacentWindowRadius_le_thirtieth hscale,
      adjacentLocalRatio_shellWidth48_le_four_thirds hm hi hwidth herror⟩

/-- Literal stopped-fibre semantics for the active sharp windows.  There are
no probability, local-CLT, or balance-law fields. -/
structure TilingSharpWindowTailData {index : Type*}
    (piece : index → Set WalkPath) (next : Set WalkPath)
    (m : ℕ) (threshold : ℕ → ℕ) (j bound : ℕ) where
  factored : TilingFactoredStoppedCoordinateData piece next (1 : ℝ≥0∞)
  accepts_iff : ∀ z cap ell,
    factored.accepts z cap ell = true ↔
      randomTotalThresholdedUpperTail
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ activeUpperFailureWindow m
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1)))
        (fun b (v : Fin (factored.upper z cap b)) ↦
          (v : ℕ) ∈ activeLowerFailureWindow m
            (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
              (factored.start z cap) (factored.retained z cap) b.1)))
        threshold shellGrowth48 j bound ell
  upper_lt_truncation : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) →
      v < factored.upper z cap b
  lower_lt_truncation : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) →
      v < factored.upper z cap b
  upper_le_cap : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeUpperFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) → v ≤ cap
  lower_le_cap : ∀ z cap
    (b : TilingAwayDomino (factored.tiling z cap) (factored.start z cap)
      (factored.retained z cap) (factored.distinguished z cap)) v,
    v ∈ activeLowerFailureWindow m
        (Fintype.card (TilingCoordinatesAt (factored.tiling z cap)
          (factored.start z cap) (factored.retained z cap) b.1)) → v ≤ cap

/-- Insert the negative-binomial local CLT and the sharp thresholded
Chernoff calculation. -/
noncomputable def exactCoordinateTailDataOfSharpWindowData
    {index : Type*} {piece : index → Set WalkPath} {next : Set WalkPath}
    {m : ℕ} {threshold : ℕ → ℕ} {j bound : ℕ}
    (harith : SharpWindowArithmeticAt m)
    (data : TilingSharpWindowTailData piece next m threshold j bound) :
    TilingExactCoordinateRandomTotalTailData piece next threshold
      shellGrowth48 j bound
      (sharpInterfaceCost threshold j) where
  factored := data.factored
  upperWindow := fun z cap b v ↦
    (v : ℕ) ∈ activeUpperFailureWindow m
      (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap) b.1))
  lowerWindow := fun z cap b v ↦
    (v : ℕ) ∈ activeLowerFailureWindow m
      (Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
        (data.factored.start z cap) (data.factored.retained z cap) b.1))
  upperDecidable := fun _ _ _ _ ↦ Finset.decidableMem _ _
  lowerDecidable := fun _ _ _ _ ↦ Finset.decidableMem _ _
  accepts_iff := data.accepts_iff
  upper_lower_disjoint := by
    intro z cap b v hv
    let i := Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap) b.1)
    by_cases hi : m / 2 ≤ i
    · rw [activeUpperFailureWindow_eq_of_active hi,
          activeLowerFailureWindow_eq_of_active hi] at hv
      rw [upperFailureWindow, Finset.mem_Ico] at hv
      rw [lowerFailureWindow, Finset.mem_Ico] at hv
      omega
    · rw [activeUpperFailureWindow_eq_empty_of_inactive hi] at hv
      simp at hv
  ratioConstant := fun _ _ ↦ 4 / 3
  ratioConstant_nonneg := by norm_num
  window_ratio := by
    intro z cap b
    let i := Fintype.card (TilingCoordinatesAt (data.factored.tiling z cap)
      (data.factored.start z cap) (data.factored.retained z cap) b.1)
    by_cases hi : m / 2 ≤ i
    · have hiFacts := harith.2 i hi
      rw [activeUpperFailureWindow_eq_of_active hi]
      rw [activeLowerFailureWindow_eq_of_active hi]
      refine (tilingAway_coordinateMass_window_ratio_of_localCLT
        (data.factored.tiling z cap) (data.factored.start z cap)
        (data.factored.retained z cap) (data.factored.distinguished z cap)
        (data.factored.upper z cap) b
        (upperFailureWindow i (shellWidth48 m))
        (lowerFailureWindow i (shellWidth48 m))
        (fun v hv ↦ data.upper_lt_truncation z cap b v (by
          rw [activeUpperFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.lower_lt_truncation z cap b v (by
          rw [activeLowerFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.upper_le_cap z cap b v (by
          rw [activeUpperFailureWindow_eq_of_active hi]
          exact hv))
        (fun v hv ↦ data.lower_le_cap z cap b v (by
          rw [activeLowerFailureWindow_eq_of_active hi]
          exact hv))
        hiFacts.1 (adjacentWindowRadius_nonneg _)
        (adjacentWindowSeparation_nonneg _) hiFacts.2.1
        (lowerFailureWindow_nonempty harith.1)
        (by simp) (fun _ hv ↦ upperFailureWindow_deviation_le hv)
        (fun _ hv ↦ lowerFailureWindow_deviation_le hv)
        (fun _ hu _ hl ↦ adjacentFailureWindow_deviation_sub_le hu hl)).trans ?_
      apply mul_le_mul_of_nonneg_right hiFacts.2.2
      apply Finset.sum_nonneg
      intro v _
      split
      · apply coordinateMass_nonneg_of_pointMass_nonneg
        intro b' ell
        exact tilingAwayExactTotalMass_nonneg
          (data.factored.tiling z cap) (data.factored.start z cap)
          (data.factored.retained z cap) (data.factored.distinguished z cap)
          b' ell
      · exact le_rfl
    · rw [activeUpperFailureWindow_eq_empty_of_inactive hi]
      rw [activeLowerFailureWindow_eq_empty_of_inactive hi]
      simp
  cost_nonneg := sharpInterfaceCost_nonneg threshold j
  envelope := by
    intro _z _cap total _htotal
    exact thresholdedProductEnvelope_le_sharpInterfaceCost
      (4 / 3) (by norm_num) four_thirds_le_positiveInterfaceRatioConstant
        threshold j total

end

end Erdos1165.HLOZSharpWindowProductClosure
