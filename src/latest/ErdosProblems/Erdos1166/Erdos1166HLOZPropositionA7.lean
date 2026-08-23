import ErdosProblems.Erdos1166.Erdos1166HLOZAppendixALocalLimit
import ErdosProblems.Erdos1166.Erdos1166HLOZLemmaA8

/-!
# The finite trajectory comparison in HLOZ Proposition A.7

This file combines the success-`1 / 2` negative-binomial local estimate with
the discrete Gaussian kernel of HLOZ Lemma A.8.  It contains no invocation of
the unrelated success-`15 / 16` urn law.

The comparison is factored into three proved pieces:

* exact centering and expansion around the parabola `2 * ℓ ^ 2`;
* a pointwise and pathwise comparison with the Lemma-A.8 Gaussian weight;
* a finite-sum transfer theorem whose sole remaining input is a lower bound
  for the corresponding many-path Gaussian corridor sum.
-/

open scoped BigOperators

namespace Erdos1166.HLOZPropositionA7

open Filter

/-- Deviation of a natural-valued trajectory from the parabola `2 * ℓ ^ 2`. -/
def centeredDeviation (ℓ m : ℕ) : ℤ :=
  (m : ℤ) - 2 * (ℓ : ℤ) ^ 2

/-- Exact increment after centering at consecutive points of the parabola. -/
theorem centeredDeviation_increment (ℓ m m' : ℕ) :
    (m' : ℤ) - m = 4 * (ℓ : ℤ) + 2 +
      (centeredDeviation (ℓ + 1) m' - centeredDeviation ℓ m) := by
  simp only [centeredDeviation]
  push_cast
  ring

/-- A coordinate lies in the window `m_ℓ = 2ℓ² + Δ_ℓ`, `|Δ_ℓ| ≤ R`. -/
def ParabolicWindow (ℓ m R : ℕ) : Prop :=
  |centeredDeviation ℓ m| ≤ (R : ℤ)

/-- An explicit radius budget which guarantees both positivity of the current
coordinate and the quarter-width hypothesis needed by the sharp local limit.
This is the deterministic window calculation behind Proposition A.7. -/
theorem localConditions_of_parabolicWindows {ℓ b b' R R' : ℕ}
    (hbwin : ParabolicWindow ℓ b R)
    (hb'win : ParabolicWindow (ℓ + 1) b' R')
    (hbudget : R + 4 * (4 * ℓ + 2 + R + R') ≤ 2 * ℓ ^ 2) :
    2 ≤ b ∧ 4 * Nat.dist b b' ≤ b := by
  unfold ParabolicWindow centeredDeviation at hbwin hb'win
  rw [abs_le] at hbwin hb'win
  have hdist : Nat.dist b b' ≤ 4 * ℓ + 2 + R + R' := by
    rcases le_total b b' with hle | hle
    · rw [Nat.dist_eq_sub_of_le hle]
      have hcenterZ :
          2 * ((ℓ + 1 : ℕ) : ℤ) ^ 2 =
            2 * (ℓ : ℤ) ^ 2 + 4 * ℓ + 2 := by
        push_cast
        ring
      exact_mod_cast (show (b' : ℤ) - b ≤ 4 * ℓ + 2 + R + R' by
        nlinarith [hbwin.1, hb'win.2, hcenterZ])
    · rw [Nat.dist_eq_sub_of_le_right hle]
      have hcenterZ :
          2 * ((ℓ + 1 : ℕ) : ℤ) ^ 2 =
            2 * (ℓ : ℤ) ^ 2 + 4 * ℓ + 2 := by
        push_cast
        ring
      exact_mod_cast (show (b : ℤ) - b' ≤ 4 * ℓ + 2 + R + R' by
        nlinarith [hbwin.2, hb'win.1, hcenterZ])
  have hR : R ≤ 2 * ℓ ^ 2 := by omega
  have hblow : 2 * ℓ ^ 2 - R ≤ b := by
    exact_mod_cast (show (2 * ℓ ^ 2 : ℤ) - R ≤ b by nlinarith [hbwin.1])
  constructor <;> omega

/-- The deterministic transition envelope between two consecutive
parabolic windows. -/
theorem natDist_le_of_parabolicWindows {ℓ b b' R R' : ℕ}
    (hbwin : ParabolicWindow ℓ b R)
    (hb'win : ParabolicWindow (ℓ + 1) b' R') :
    Nat.dist b b' ≤ 4 * ℓ + 2 + R + R' := by
  unfold ParabolicWindow centeredDeviation at hbwin hb'win
  rw [abs_le] at hbwin hb'win
  have hcenterZ :
      2 * ((ℓ + 1 : ℕ) : ℤ) ^ 2 =
        2 * (ℓ : ℤ) ^ 2 + 4 * ℓ + 2 := by
    push_cast
    ring
  rcases le_total b b' with hle | hle
  · rw [Nat.dist_eq_sub_of_le hle]
    exact_mod_cast (show (b' : ℤ) - b ≤ 4 * ℓ + 2 + R + R' by
      nlinarith [hbwin.1, hb'win.2, hcenterZ])
  · rw [Nat.dist_eq_sub_of_le_right hle]
    exact_mod_cast (show (b : ℤ) - b' ≤ 4 * ℓ + 2 + R + R' by
      nlinarith [hbwin.2, hb'win.1, hcenterZ])

/-- Lower edge of a natural-valued parabolic window. -/
theorem parabolicWindow_lower {ℓ b R : ℕ} (hwin : ParabolicWindow ℓ b R)
    (hR : R ≤ 2 * ℓ ^ 2) : 2 * ℓ ^ 2 - R ≤ b := by
  unfold ParabolicWindow centeredDeviation at hwin
  rw [abs_le] at hwin
  exact_mod_cast (show (2 * ℓ ^ 2 : ℤ) - R ≤ b by nlinarith [hwin.1])

/-- Squaring removes the orientation in `Nat.dist`. -/
theorem natDist_sq_cast (m m' : ℕ) :
    ((Nat.dist m m' : ℕ) : ℝ) ^ 2 = ((m' : ℝ) - m) ^ 2 := by
  rcases le_total m m' with h | h
  · rw [Nat.dist_eq_sub_of_le h, Nat.cast_sub h]
  · rw [Nat.dist_eq_sub_of_le_right h, Nat.cast_sub h]
    ring

/-- Full quadratic cost appearing before the parabolic expansion. -/
noncomputable def quadraticIncrementAction (ℓ m m' : ℕ) : ℝ :=
  ((Nat.dist m m' : ℕ) : ℝ) ^ 2 / (8 * (ℓ : ℝ) ^ 2)

/-- Quadratic action of the centered Gaussian kernel from Lemma A.8. -/
noncomputable def gaussianIncrementAction (ℓ m m' : ℕ) : ℝ :=
  (((centeredDeviation (ℓ + 1) m' : ℝ) - centeredDeviation ℓ m) ^ 2) /
    (8 * (ℓ : ℝ) ^ 2)

/-- The exact deterministic and linear correction left after removing the
centered Gaussian action. -/
noncomputable def driftIncrementAction (ℓ m m' : ℕ) : ℝ :=
  2 + 2 / (ℓ : ℝ) + 1 / (2 * (ℓ : ℝ) ^ 2) +
    ((centeredDeviation (ℓ + 1) m' : ℝ) - centeredDeviation ℓ m) / (ℓ : ℝ) +
    ((centeredDeviation (ℓ + 1) m' : ℝ) - centeredDeviation ℓ m) /
      (2 * (ℓ : ℝ) ^ 2)

/-- Exact algebraic expansion of the quadratic action around
`m_ℓ = 2 * ℓ ^ 2 + Δ_ℓ`. -/
theorem quadraticIncrementAction_eq_drift_add_gaussian {ℓ m m' : ℕ}
    (hℓ : 0 < ℓ) :
    quadraticIncrementAction ℓ m m' =
      driftIncrementAction ℓ m m' + gaussianIncrementAction ℓ m m' := by
  have hint := centeredDeviation_increment ℓ m m'
  have hintR :
      (m' : ℝ) - m = 4 * (ℓ : ℝ) + 2 +
        ((centeredDeviation (ℓ + 1) m' : ℝ) - centeredDeviation ℓ m) := by
    exact_mod_cast hint
  unfold quadraticIncrementAction driftIncrementAction gaussianIncrementAction
  rw [natDist_sq_cast, hintR]
  field_simp [show (ℓ : ℝ) ≠ 0 by positivity]
  ring

/-- A natural-valued path with `N` transitions. -/
abbrev NatPath (N : ℕ) := Fin (N + 1) → ℕ

/-- Center a natural-valued path at `2 * (start + i) ^ 2`. -/
def centeredPath (start : ℕ) {N : ℕ} (q : NatPath N) :
    Erdos1166.HLOZLemmaA8.Path N :=
  fun i ↦ centeredDeviation (start + i) (q i)

/-- Coordinatewise parabolic corridor for a natural-valued path. -/
def InParabolicCorridor (start : ℕ) {N : ℕ}
    (R : Fin (N + 1) → ℕ) (q : NatPath N) : Prop :=
  ∀ i : Fin (N + 1), ParabolicWindow (start + i) (q i) (R i)

/-- Transitionwise deterministic budget on a corridor radius. -/
def ParabolicRadiusBudget (start N : ℕ) (R : Fin (N + 1) → ℕ) : Prop :=
  ∀ i : Fin N,
    R i.castSucc +
        4 * (4 * (start + (i : ℕ)) + 2 + R i.castSucc + R i.succ) ≤
      2 * (start + (i : ℕ)) ^ 2

/-! ### The literal HLOZ power corridor satisfies the local-limit budget -/

/-- The natural radius function on a finite piece of HLOZ's literal corridor
`|m_ℓ - 2ℓ²| ≤ ℓ^(1+δ)`. -/
noncomputable def hlozRadius (δ : ℝ) (start N : ℕ) : Fin (N + 1) → ℕ :=
  fun i ↦ Erdos1166.HLOZLemmaA8.corridorRadius δ (start + (i : ℕ))

/-- Flooring the real power can only decrease the HLOZ corridor radius. -/
theorem corridorRadius_cast_le (δ : ℝ) (ℓ : ℕ) :
    (Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ : ℝ) ≤
      (ℓ : ℝ) ^ (1 + δ) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg _) _)

/-- A fixed multiple of `ℓ^(1+δ)` is eventually dominated by `ℓ²` whenever
`δ < 1`.  This elementary comparison is kept here so that the corridor
specialization has no asymptotic hypothesis hidden in its statement. -/
theorem eventually_const_mul_corridorRadius_le_sq {δ : ℝ} (hδ : δ < 1)
    (C : ℕ) :
    ∀ᶠ ℓ : ℕ in atTop,
      C * Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ ≤ ℓ ^ 2 := by
  have hpq : 1 + δ < (2 : ℝ) := by linarith
  have hpow : Tendsto (fun ℓ : ℕ ↦ (ℓ : ℝ) ^ ((2 : ℝ) - (1 + δ)))
      atTop atTop :=
    (tendsto_rpow_atTop (sub_pos.mpr hpq)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hpow.eventually (eventually_ge_atTop (C : ℝ))
  filter_upwards [hlarge, eventually_ge_atTop 1] with ℓ hlarge hℓ
  have hℓpos : 0 < (ℓ : ℝ) := by
    exact_mod_cast (show 0 < ℓ by omega)
  have hradius := corridorRadius_cast_le δ ℓ
  have hreal :
      (C : ℝ) *
          (Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ : ℝ) ≤
        (ℓ : ℝ) ^ (2 : ℕ) := by
    calc
      (C : ℝ) *
          (Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ : ℝ) ≤
          (C : ℝ) * (ℓ : ℝ) ^ (1 + δ) := by gcongr
      _ ≤ (ℓ : ℝ) ^ ((2 : ℝ) - (1 + δ)) *
          (ℓ : ℝ) ^ (1 + δ) := by gcongr
      _ = (ℓ : ℝ) ^ (2 : ℝ) := by
        rw [← Real.rpow_add hℓpos]
        congr 2
        ring
      _ = (ℓ : ℝ) ^ (2 : ℕ) := by norm_num [Real.rpow_two]
  exact_mod_cast hreal

/-- The exact one-step source corridor has the sharp-local-limit radius
budget at every sufficiently large scale.  The constants are deliberately
integer-valued: applying the `100R ≤ ℓ²` estimate also at `ℓ+1` gives
`25R_{ℓ+1} ≤ ℓ²`, and the remaining deterministic increment is `16ℓ+8`. -/
theorem eventually_hlozRadius_localBudget {δ : ℝ} (hδ : δ < 1) :
    ∀ᶠ ℓ : ℕ in atTop,
      Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ +
          4 * (4 * ℓ + 2 +
            Erdos1166.HLOZLemmaA8.corridorRadius δ ℓ +
            Erdos1166.HLOZLemmaA8.corridorRadius δ (ℓ + 1)) ≤
        2 * ℓ ^ 2 := by
  have hR := eventually_const_mul_corridorRadius_le_sq hδ 100
  rw [eventually_atTop] at hR
  rcases hR with ⟨L, hL⟩
  filter_upwards [eventually_ge_atTop (max L 18)] with ℓ hℓ
  have hRℓ := hL ℓ (by omega)
  have hRsucc := hL (ℓ + 1) (by omega)
  have hRsucc' :
      25 * Erdos1166.HLOZLemmaA8.corridorRadius δ (ℓ + 1) ≤ ℓ ^ 2 := by
    nlinarith [hRsucc]
  have hlinearR : (16 : ℝ) * ℓ + 8 ≤ (ℓ : ℝ) ^ 2 := by
    have hℓR : (18 : ℝ) ≤ ℓ := by exact_mod_cast (le_trans (Nat.le_max_right _ _) hℓ)
    nlinarith [sq_nonneg ((ℓ : ℝ) - 18)]
  have hlinear : 16 * ℓ + 8 ≤ ℓ ^ 2 := by exact_mod_cast hlinearR
  omega

/-- Uniform tail form of the preceding estimate: after one cutoff depending
only on `δ`, every finite literal HLOZ corridor has all of the hypotheses of
the sharp negative-binomial local bound. -/
theorem eventually_hlozRadiusBudget {δ : ℝ} (hδ : δ < 1) :
    ∀ᶠ start : ℕ in atTop,
      ∀ N : ℕ, ParabolicRadiusBudget start N (hlozRadius δ start N) := by
  have hev := eventually_hlozRadius_localBudget hδ
  rw [eventually_atTop] at hev
  rcases hev with ⟨L, hL⟩
  filter_upwards [eventually_ge_atTop L] with start hstart N i
  simpa only [hlozRadius, Fin.coe_castSucc, Fin.val_succ, Nat.add_assoc] using
    hL (start + (i : ℕ)) (by omega)

theorem pathLocalConditions_of_parabolicCorridor {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hq : InParabolicCorridor start R q)
    (hbudget : ParabolicRadiusBudget start N R) :
    (∀ i : Fin N, 2 ≤ q i.castSucc) ∧
      (∀ i : Fin N,
        4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc) := by
  constructor
  · intro i
    exact (localConditions_of_parabolicWindows
      (hbwin := hq i.castSucc) (hb'win := by
        convert hq i.succ using 1 <;> simp [Nat.add_assoc])
      (hbudget i)).1
  · intro i
    exact (localConditions_of_parabolicWindows
      (hbwin := hq i.castSucc) (hb'win := by
        convert hq i.succ using 1 <;> simp [Nat.add_assoc])
      (hbudget i)).2

/-- Sum of the uncentered quadratic actions along a path. -/
noncomputable def quadraticPathAction (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    quadraticIncrementAction (start + i) (q i.castSucc) (q i.succ)

/-- Sum of the deterministic/linear corrections along a path. -/
noncomputable def driftPathAction (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    driftIncrementAction (start + i) (q i.castSucc) (q i.succ)

/-- Finite Abel summation for forward differences against the reciprocal
scale.  This is the exact identity used for the linear centered term in
HLOZ Proposition A.7. -/
theorem forwardDiff_div_abel (f : ℕ → ℝ) {start : ℕ} (hstart : 0 < start)
    (N : ℕ) :
    (∑ i ∈ Finset.range N,
        (f (i + 1) - f i) / (start + i : ℕ)) =
      f N / (start + N : ℕ) - f 0 / start +
        ∑ i ∈ Finset.range N,
          f (i + 1) /
            ((start + i : ℕ) * (start + i + 1 : ℕ)) := by
  induction N with
  | zero => simp
  | succ N ih =>
      rw [Finset.sum_range_succ, Finset.sum_range_succ, ih]
      have h₁ : (start + N : ℝ) ≠ 0 := by positivity
      have h₂ : (start + N + 1 : ℝ) ≠ 0 := by positivity
      push_cast
      field_simp [h₁, h₂]
      ring

/-- `Fin`-indexed form of `forwardDiff_div_abel`, matching `NatPath`. -/
theorem finForwardDiff_div_abel {N : ℕ} (a : Fin (N + 1) → ℝ)
    {start : ℕ} (hstart : 0 < start) :
    (∑ i : Fin N,
        (a i.succ - a i.castSucc) / (start + (i : ℕ) : ℕ)) =
      a (Fin.last N) / (start + N : ℕ) - a 0 / start +
        ∑ i : Fin N,
          a i.succ /
            ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ)) := by
  let f : ℕ → ℝ := fun i ↦ if hi : i < N + 1 then a ⟨i, hi⟩ else 0
  have h := forwardDiff_div_abel f hstart N
  rw [← Fin.sum_univ_eq_sum_range, ← Fin.sum_univ_eq_sum_range] at h
  convert h using 1
  · simp [f]
    apply Finset.sum_congr rfl
    intro i hi
    congr
  · simp [f]
    congr 2

/-- The deterministic part of the drift action. -/
noncomputable def baseDriftPathAction (start N : ℕ) : ℝ :=
  ∑ i : Fin N,
    (2 + 2 / ((start + (i : ℕ) : ℕ) : ℝ) +
      1 / (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2))

/-- The first-order centered difference in the drift action. -/
noncomputable def primaryCenteredDrift (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    ((centeredPath start q i.succ : ℝ) - centeredPath start q i.castSucc) /
      ((start + (i : ℕ) : ℕ) : ℝ)

/-- The smaller second-order centered difference in the drift action. -/
noncomputable def secondaryCenteredDrift (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    ((centeredPath start q i.succ : ℝ) - centeredPath start q i.castSucc) /
      (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)

theorem driftPathAction_eq_three_parts (start N : ℕ) (q : NatPath N) :
    driftPathAction start N q =
      baseDriftPathAction start N + primaryCenteredDrift start N q +
        secondaryCenteredDrift start N q := by
  unfold driftPathAction driftIncrementAction baseDriftPathAction
    primaryCenteredDrift secondaryCenteredDrift centeredPath
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  simp only [Fin.val_succ, Fin.val_castSucc, Nat.add_assoc]

/-- Exact Abel expansion of the only potentially large linear drift term. -/
theorem primaryCenteredDrift_eq_abel {start N : ℕ} (hstart : 0 < start)
    (q : NatPath N) :
    primaryCenteredDrift start N q =
      (centeredPath start q (Fin.last N) : ℝ) / (start + N : ℕ) -
        (centeredPath start q 0 : ℝ) / start +
      ∑ i : Fin N,
        (centeredPath start q i.succ : ℝ) /
          ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ)) := by
  unfold primaryCenteredDrift
  exact finForwardDiff_div_abel (fun i ↦ (centeredPath start q i : ℝ)) hstart

/-- Real absolute-value form of membership in a parabolic corridor. -/
theorem abs_centeredPath_le {start N : ℕ} {R : Fin (N + 1) → ℕ}
    {q : NatPath N} (hq : InParabolicCorridor start R q)
    (i : Fin (N + 1)) :
    |(centeredPath start q i : ℝ)| ≤ R i := by
  exact_mod_cast hq i

/-- Explicit uniform upper bound for the entire drift action.  Its primary
difference term has already been Abel-summed, so the corridor width is paid
only at the two endpoints and against reciprocal-square coefficients. -/
noncomputable def corridorDriftBound
    (start N : ℕ) (R : Fin (N + 1) → ℕ) : ℝ :=
  baseDriftPathAction start N +
    (R (Fin.last N) : ℝ) / (start + N : ℕ) + (R 0 : ℝ) / start +
    (∑ i : Fin N, (R i.succ : ℝ) /
      ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ))) +
    ∑ i : Fin N, ((R i.castSucc : ℝ) + R i.succ) /
      (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)

theorem primaryCenteredDrift_le_corridor {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hstart : 0 < start) (hq : InParabolicCorridor start R q) :
    primaryCenteredDrift start N q ≤
      (R (Fin.last N) : ℝ) / (start + N : ℕ) + (R 0 : ℝ) / start +
        ∑ i : Fin N, (R i.succ : ℝ) /
          ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ)) := by
  rw [primaryCenteredDrift_eq_abel hstart]
  have habs : ∀ i : Fin (N + 1),
      |(centeredPath start q i : ℝ)| ≤ R i := fun i ↦ abs_centeredPath_le hq i
  have hend : (centeredPath start q (Fin.last N) : ℝ) ≤ R (Fin.last N) :=
    (le_abs_self _).trans (habs _)
  have hzero : -(centeredPath start q 0 : ℝ) ≤ R 0 :=
    (neg_le_abs _).trans (habs _)
  have hsum : (∑ i : Fin N,
      (centeredPath start q i.succ : ℝ) /
        ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ))) ≤
      ∑ i : Fin N, (R i.succ : ℝ) /
        ((start + (i : ℕ) : ℕ) * (start + (i : ℕ) + 1 : ℕ)) := by
    apply Finset.sum_le_sum
    intro i hi
    exact div_le_div_of_nonneg_right ((le_abs_self _).trans (habs i.succ)) (by positivity)
  have he : (centeredPath start q (Fin.last N) : ℝ) / (start + N : ℕ) ≤
      (R (Fin.last N) : ℝ) / (start + N : ℕ) :=
    div_le_div_of_nonneg_right hend (by positivity)
  have hz : -(centeredPath start q 0 : ℝ) / start ≤ (R 0 : ℝ) / start :=
    div_le_div_of_nonneg_right hzero (by positivity)
  have hz' : -((centeredPath start q 0 : ℝ) / start) ≤ (R 0 : ℝ) / start := by
    simpa only [neg_div] using hz
  linarith

theorem secondaryCenteredDrift_le_corridor {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hstart : 0 < start) (hq : InParabolicCorridor start R q) :
    secondaryCenteredDrift start N q ≤
      ∑ i : Fin N, ((R i.castSucc : ℝ) + R i.succ) /
        (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2) := by
  unfold secondaryCenteredDrift
  apply Finset.sum_le_sum
  intro i hi
  have ha := abs_centeredPath_le hq i.castSucc
  have hb := abs_centeredPath_le hq i.succ
  apply div_le_div_of_nonneg_right _ (by positivity)
  calc
    (centeredPath start q i.succ : ℝ) - centeredPath start q i.castSucc ≤
        |(centeredPath start q i.succ : ℝ)| +
          |(centeredPath start q i.castSucc : ℝ)| := by
      linarith [le_abs_self (centeredPath start q i.succ : ℝ),
        neg_le_abs (centeredPath start q i.castSucc : ℝ)]
    _ ≤ (R i.succ : ℝ) + R i.castSucc := add_le_add hb ha
    _ = _ := by ring

/-- The accumulated drift estimate, with the source's Abel cancellation
made explicit and no path-dependent term remaining. -/
theorem driftPathAction_le_corridorDriftBound {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hstart : 0 < start) (hq : InParabolicCorridor start R q) :
    driftPathAction start N q ≤ corridorDriftBound start N R := by
  rw [driftPathAction_eq_three_parts]
  unfold corridorDriftBound
  have hp := primaryCenteredDrift_le_corridor hstart hq
  have hs := secondaryCenteredDrift_le_corridor hstart hq
  linarith

/-- Sum of the centered Gaussian actions along a path. -/
noncomputable def gaussianPathAction (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    gaussianIncrementAction (start + i) (q i.castSucc) (q i.succ)

/-- The transitionwise expansion sums exactly over every finite path. -/
theorem quadraticPathAction_eq_drift_add_gaussian {start N : ℕ}
    (hstart : 0 < start) (q : NatPath N) :
    quadraticPathAction start N q =
      driftPathAction start N q + gaussianPathAction start N q := by
  unfold quadraticPathAction driftPathAction gaussianPathAction
  rw [← Finset.sum_add_distrib]
  apply Finset.sum_congr rfl
  intro i hi
  exact quadraticIncrementAction_eq_drift_add_gaussian (by omega)

/-- The sharp local exponent in the negative-binomial estimate. -/
noncomputable def localCost (b b' : ℕ) : ℝ :=
  Erdos1166.HLOZAppendixA.sharpLocalCost b b'

/-- Ratio between the normalization in the safe local estimate and the
normalization of the Lemma-A.8 Gaussian kernel. -/
noncomputable def normalizationRatio (ℓ b : ℕ) : ℝ :=
  (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ))) /
    (2 * Real.sqrt (Real.pi * (b : ℝ)))

/-- Extra exponent needed to turn the safe local estimate into the centered
Gaussian kernel. -/
noncomputable def comparisonCost (ℓ b b' : ℕ) (k k' : ℤ) : ℝ :=
  localCost b b' - (((k : ℝ) - k') ^ 2 / (8 * (ℓ : ℝ) ^ 2))

/-- The explicit non-Gaussian remainder in the sharp local estimate. -/
noncomputable def sharpRemainder (b b' : ℕ) : ℝ :=
  3 * Nat.dist b b' / (b : ℝ) +
    4 * (Nat.dist b b' : ℝ) ^ 3 / (b : ℝ) ^ 2 + 1 / (b : ℝ)

/-- Uniform local-limit remainder on two consecutive parabolic windows.
Here `D = 4ℓ+2+R+R'` is the transition envelope and
`B = 2ℓ²-R` is the lower edge of the current window. -/
noncomputable def corridorSharpRemainderBound (ℓ R R' : ℕ) : ℝ :=
  let D : ℕ := 4 * ℓ + 2 + R + R'
  let B : ℕ := 2 * ℓ ^ 2 - R
  3 * D / (B : ℝ) + 4 * (D : ℝ) ^ 3 / (B : ℝ) ^ 2 + 1 / (B : ℝ)

theorem sharpRemainder_le_corridorBound {ℓ b b' R R' : ℕ}
    (hbwin : ParabolicWindow ℓ b R)
    (hb'win : ParabolicWindow (ℓ + 1) b' R')
    (hbudget : R + 4 * (4 * ℓ + 2 + R + R') ≤ 2 * ℓ ^ 2) :
    sharpRemainder b b' ≤ corridorSharpRemainderBound ℓ R R' := by
  let D : ℕ := 4 * ℓ + 2 + R + R'
  let B : ℕ := 2 * ℓ ^ 2 - R
  have hd : Nat.dist b b' ≤ D := natDist_le_of_parabolicWindows hbwin hb'win
  have hR : R ≤ 2 * ℓ ^ 2 := by omega
  have hb : B ≤ b := parabolicWindow_lower hbwin hR
  have hB : 0 < B := by dsimp [B]; omega
  unfold sharpRemainder corridorSharpRemainderBound
  dsimp only [D, B]
  have h1 : 3 * (Nat.dist b b' : ℝ) / b ≤ 3 * (D : ℝ) / B := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · exact_mod_cast (Nat.mul_le_mul_left 3 hd)
    · exact_mod_cast hb
  have h3 : 4 * (Nat.dist b b' : ℝ) ^ 3 / (b : ℝ) ^ 2 ≤
      4 * (D : ℝ) ^ 3 / (B : ℝ) ^ 2 := by
    refine div_le_div₀ (by positivity) ?_ (by positivity) ?_
    · gcongr
    · gcongr
  have hi : 1 / (b : ℝ) ≤ 1 / B := by
    exact one_div_le_one_div_of_le (by positivity) (by exact_mod_cast hb)
  linarith

/-- The correction caused by replacing the true local denominator `4b` by
the parabolic denominator `8ℓ²`. -/
noncomputable def denominatorMismatchAction (ℓ b b' : ℕ) : ℝ :=
  (Nat.dist b b' : ℝ) ^ 2 / (4 * (b : ℝ)) -
    quadraticIncrementAction ℓ b b'

/-- Uniform bound for replacing the true denominator `4b` by `8ℓ²`.
Unlike a crude bound by the whole quadratic action, this retains the small
factor `R / ℓ²` coming from `|b-2ℓ²| ≤ R`. -/
noncomputable def corridorDenominatorMismatchBound (ℓ R R' : ℕ) : ℝ :=
  let D : ℕ := 4 * ℓ + 2 + R + R'
  let B : ℕ := 2 * ℓ ^ 2 - R
  (D : ℝ) ^ 2 * R / (8 * (ℓ : ℝ) ^ 2 * B)

theorem denominatorMismatchAction_le_corridorBound {ℓ b b' R R' : ℕ}
    (hbwin : ParabolicWindow ℓ b R)
    (hb'win : ParabolicWindow (ℓ + 1) b' R')
    (hbudget : R + 4 * (4 * ℓ + 2 + R + R') ≤ 2 * ℓ ^ 2) :
    denominatorMismatchAction ℓ b b' ≤
      corridorDenominatorMismatchBound ℓ R R' := by
  let D : ℕ := 4 * ℓ + 2 + R + R'
  let B : ℕ := 2 * ℓ ^ 2 - R
  have hd : Nat.dist b b' ≤ D := natDist_le_of_parabolicWindows hbwin hb'win
  have hR : R ≤ 2 * ℓ ^ 2 := by omega
  have hb : B ≤ b := parabolicWindow_lower hbwin hR
  have hB : 0 < B := by dsimp [B]; omega
  have hbpos : 0 < b := lt_of_lt_of_le hB hb
  have hℓ : 0 < ℓ := by
    by_contra h
    simp at h
    subst ℓ
    norm_num at hbudget
  have hdevZ := hbwin
  unfold ParabolicWindow centeredDeviation at hdevZ
  have hdev : |(b : ℝ) - 2 * (ℓ : ℝ) ^ 2| ≤ (R : ℝ) := by
    have hcast : |(((b : ℤ) - 2 * (ℓ : ℤ) ^ 2 : ℤ) : ℝ)| ≤ (R : ℝ) := by
      exact_mod_cast hdevZ
    simpa only [Int.cast_sub, Int.cast_natCast, Int.cast_mul, Int.cast_ofNat,
      Int.cast_pow] using hcast
  have hcenter : 2 * (ℓ : ℝ) ^ 2 - (b : ℝ) ≤ (R : ℝ) := by
    linarith [neg_le_abs ((b : ℝ) - 2 * (ℓ : ℝ) ^ 2)]
  have heq : denominatorMismatchAction ℓ b b' =
      (Nat.dist b b' : ℝ) ^ 2 * (2 * (ℓ : ℝ) ^ 2 - (b : ℝ)) /
        (8 * (ℓ : ℝ) ^ 2 * (b : ℝ)) := by
    unfold denominatorMismatchAction quadraticIncrementAction
    field_simp [show (ℓ : ℝ) ≠ 0 by positivity, show (b : ℝ) ≠ 0 by positivity]
    ring
  rw [heq]
  unfold corridorDenominatorMismatchBound
  dsimp only [D, B]
  apply div_le_div₀ (by positivity)
  · calc
      (Nat.dist b b' : ℝ) ^ 2 * (2 * (ℓ : ℝ) ^ 2 - (b : ℝ)) ≤
          (Nat.dist b b' : ℝ) ^ 2 * (R : ℝ) := by
        gcongr
      _ ≤ (D : ℝ) ^ 2 * (R : ℝ) := by
        gcongr
  · positivity
  · gcongr

theorem localCost_eq_quadratic_add_remainder (b b' : ℕ) :
    localCost b b' =
      (Nat.dist b b' : ℝ) ^ 2 / (4 * (b : ℝ)) + sharpRemainder b b' := by
  unfold localCost Erdos1166.HLOZAppendixA.sharpLocalCost
    Erdos1166.HLOZAppendixA.sharpOffCenterCost sharpRemainder
  ring

/-- Exact transitionwise decomposition of the sharp comparison cost.  The
leading `2` is contained in `driftIncrementAction`; the two remaining terms
are the denominator mismatch and the explicit local-limit remainder. -/
theorem comparisonCost_centered_eq {ℓ b b' : ℕ} (hℓ : 0 < ℓ) :
    comparisonCost ℓ b b'
        (centeredDeviation ℓ b) (centeredDeviation (ℓ + 1) b') =
      driftIncrementAction ℓ b b' + denominatorMismatchAction ℓ b b' +
        sharpRemainder b b' := by
  have hquad := quadraticIncrementAction_eq_drift_add_gaussian
    (ℓ := ℓ) (m := b) (m' := b') hℓ
  have hgaussian :
      (((centeredDeviation ℓ b : ℝ) - centeredDeviation (ℓ + 1) b') ^ 2 /
          (8 * (ℓ : ℝ) ^ 2)) = gaussianIncrementAction ℓ b b' := by
    unfold gaussianIncrementAction
    congr 1
    ring
  unfold comparisonCost denominatorMismatchAction
  rw [localCost_eq_quadratic_add_remainder, hgaussian, hquad]
  ring

theorem normalizationRatio_nonneg (ℓ b : ℕ) : 0 ≤ normalizationRatio ℓ b := by
  unfold normalizationRatio
  positivity

theorem normalizationRatio_sq {ℓ b : ℕ} (hℓ : 0 < ℓ) (hb : 0 < b) :
    normalizationRatio ℓ b ^ 2 = 2 * (ℓ : ℝ) ^ 2 / b := by
  have hpi : Real.pi ≠ 0 := Real.pi_ne_zero
  have hsqrt2pi : Real.sqrt (2 * Real.pi) ^ 2 = 2 * Real.pi :=
    Real.sq_sqrt (by positivity)
  have hsqrtpib : Real.sqrt (Real.pi * (b : ℝ)) ^ 2 = Real.pi * b :=
    Real.sq_sqrt (by positivity)
  unfold normalizationRatio
  rw [div_pow, mul_pow, hsqrt2pi,
    show (2 * Real.sqrt (Real.pi * (b : ℝ))) ^ 2 =
      4 * Real.sqrt (Real.pi * (b : ℝ)) ^ 2 by ring,
    hsqrtpib]
  field_simp
  ring

/-- The normalization loss in a parabolic window is explicitly at most
`R / (2ℓ²)` in the exponent. -/
theorem exp_neg_radius_div_le_normalizationRatio {ℓ b R : ℕ} (hℓ : 0 < ℓ)
    (hb : 0 < b) (hwin : ParabolicWindow ℓ b R) :
    Real.exp (-((R : ℝ) / (2 * (ℓ : ℝ) ^ 2))) ≤ normalizationRatio ℓ b := by
  let x : ℝ := (R : ℝ) / (2 * (ℓ : ℝ) ^ 2)
  have hx0 : 0 ≤ x := by dsimp [x]; positivity
  have hexp : Real.exp (-x) ≤ (1 + x)⁻¹ := by
    rw [Real.exp_neg]
    exact (inv_le_inv₀ (Real.exp_pos x) (by positivity)).2
      (by simpa [add_comm] using Real.add_one_le_exp x)
  have hupper : b ≤ 2 * ℓ ^ 2 + R := by
    unfold ParabolicWindow centeredDeviation at hwin
    rw [abs_le] at hwin
    exact_mod_cast (show (b : ℤ) ≤ 2 * ℓ ^ 2 + R by linarith [hwin.2])
  have honesq : ((1 + x)⁻¹) ^ 2 ≤ normalizationRatio ℓ b ^ 2 := by
    rw [normalizationRatio_sq hℓ hb]
    dsimp [x]
    field_simp
    nlinarith [show (0 : ℝ) ≤ R by positivity,
      show (0 : ℝ) < ℓ by positivity, show (0 : ℝ) < b by positivity,
      show (b : ℝ) ≤ 2 * ℓ ^ 2 + R by exact_mod_cast hupper]
  have hone : (1 + x)⁻¹ ≤ normalizationRatio ℓ b :=
    le_of_sq_le_sq honesq (normalizationRatio_nonneg _ _)
  exact hexp.trans hone

/-- Exact factorization underlying the local comparison. -/
theorem normalizationRatio_mul_exp_mul_b {ℓ b b' : ℕ} (hℓ : 0 < ℓ)
    (hb : 0 < b) (k k' : ℤ) :
    normalizationRatio ℓ b * Real.exp (-comparisonCost ℓ b b' k k') *
        Erdos1166.HLOZLemmaA8.b ℓ k k' =
      Real.exp (-localCost b b') *
        (1 / (2 * Real.sqrt (Real.pi * (b : ℝ)))) := by
  have hsqrtpib : Real.sqrt (Real.pi * (b : ℝ)) ≠ 0 :=
    (Real.sqrt_pos.2 (by positivity)).ne'
  have hnorm : Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)) ≠ 0 := by
    apply mul_ne_zero
    · exact (Real.sqrt_pos.2 (mul_pos (by norm_num) Real.pi_pos)).ne'
    · positivity
  have hexp :
      Real.exp (-comparisonCost ℓ b b' k k') *
          Real.exp (-(((k : ℝ) - k') ^ 2 / (8 * (ℓ : ℝ) ^ 2))) =
        Real.exp (-localCost b b') := by
    rw [← Real.exp_add]
    congr 1
    unfold comparisonCost
    ring
  unfold normalizationRatio Erdos1166.HLOZLemmaA8.b
  calc
    _ =
        ((Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ))) /
            (2 * Real.sqrt (Real.pi * (b : ℝ))) *
          (Real.sqrt (2 * Real.pi) * (2 * (ℓ : ℝ)))⁻¹) *
          (Real.exp (-comparisonCost ℓ b b' k k') *
            Real.exp (-(((k : ℝ) - k') ^ 2 / (8 * (ℓ : ℝ) ^ 2)))) := by ring
    _ = Real.exp (-localCost b b') *
        (1 / (2 * Real.sqrt (Real.pi * (b : ℝ)))) := by
      rw [hexp]
      field_simp [hnorm, hsqrtpib]

/-- Pointwise comparison of the correct success-`1 / 2` urn transition with
the Lemma-A.8 Gaussian kernel. -/
theorem gaussianTransition_le_halfNegBinMass {ℓ b b' : ℕ} (hℓ : 0 < ℓ)
    (hb : 2 ≤ b) (hd : 4 * Nat.dist b b' ≤ b) (k k' : ℤ) :
    normalizationRatio ℓ b * Real.exp (-comparisonCost ℓ b b' k k') *
        Erdos1166.HLOZLemmaA8.b ℓ k k' ≤
      Erdos1166.HLOZAppendixA.halfNegBinMass b b' := by
  rw [normalizationRatio_mul_exp_mul_b hℓ (by omega)]
  simpa only [localCost, div_eq_mul_inv, one_mul] using
    (Erdos1166.HLOZAppendixA.halfNegBinMass_sharp_local_lower hb hd)

/-- Product of the correct negative-binomial transitions along a path. -/
noncomputable def halfNegBinPathWeight {N : ℕ} (q : NatPath N) : ℝ :=
  ∏ i : Fin N, Erdos1166.HLOZAppendixA.halfNegBinMass (q i.castSucc) (q i.succ)

/-- Product of all normalization ratios along a centered path. -/
noncomputable def pathNormalizationRatio (start N : ℕ) (q : NatPath N) : ℝ :=
  ∏ i : Fin N, normalizationRatio (start + i) (q i.castSucc)

/-- Explicit accumulated normalization loss for a prescribed corridor
radius.  For power radii this is the familiar sublinear sum
`∑ R_ℓ / (2ℓ²)`. -/
noncomputable def pathNormalizationCost
    (start N : ℕ) (R : Fin (N + 1) → ℕ) : ℝ :=
  ∑ i : Fin N,
    (R i.castSucc : ℝ) / (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)

/-- Sum of the comparison costs along a centered path. -/
noncomputable def pathComparisonCost (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    comparisonCost (start + i) (q i.castSucc) (q i.succ)
      (centeredPath start q i.castSucc) (centeredPath start q i.succ)

/-- Sum of the true-denominator corrections along a trajectory. -/
noncomputable def pathDenominatorMismatch (start N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N,
    denominatorMismatchAction (start + i) (q i.castSucc) (q i.succ)

/-- Sum of the explicit local-limit remainders along a trajectory. -/
noncomputable def pathSharpRemainder (N : ℕ) (q : NatPath N) : ℝ :=
  ∑ i : Fin N, sharpRemainder (q i.castSucc) (q i.succ)

/-- Pathwise sum of the explicit uniform denominator-mismatch bounds. -/
noncomputable def corridorDenominatorMismatchPathBound
    (start N : ℕ) (R : Fin (N + 1) → ℕ) : ℝ :=
  ∑ i : Fin N,
    corridorDenominatorMismatchBound (start + (i : ℕ)) (R i.castSucc) (R i.succ)

/-- Pathwise sum of the explicit uniform sharp-local-limit remainders. -/
noncomputable def corridorSharpRemainderPathBound
    (start N : ℕ) (R : Fin (N + 1) → ℕ) : ℝ :=
  ∑ i : Fin N,
    corridorSharpRemainderBound (start + (i : ℕ)) (R i.castSucc) (R i.succ)

/-- Complete, path-independent comparison cost on a parabolic corridor. -/
noncomputable def corridorComparisonCostBound
    (start N : ℕ) (R : Fin (N + 1) → ℕ) : ℝ :=
  corridorDriftBound start N R + corridorDenominatorMismatchPathBound start N R +
    corridorSharpRemainderPathBound start N R

theorem pathDenominatorMismatch_le_corridorBound {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hq : InParabolicCorridor start R q)
    (hbudget : ParabolicRadiusBudget start N R) :
    pathDenominatorMismatch start N q ≤
      corridorDenominatorMismatchPathBound start N R := by
  unfold pathDenominatorMismatch corridorDenominatorMismatchPathBound
  apply Finset.sum_le_sum
  intro i hi
  apply denominatorMismatchAction_le_corridorBound (hq i.castSucc)
  · convert hq i.succ using 1 <;> simp [Fin.val_succ, Nat.add_assoc]
  · exact hbudget i

theorem pathSharpRemainder_le_corridorBound {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hq : InParabolicCorridor start R q)
    (hbudget : ParabolicRadiusBudget start N R) :
    pathSharpRemainder N q ≤ corridorSharpRemainderPathBound start N R := by
  unfold pathSharpRemainder corridorSharpRemainderPathBound
  apply Finset.sum_le_sum
  intro i hi
  apply sharpRemainder_le_corridorBound (hq i.castSucc)
  · convert hq i.succ using 1 <;> simp [Fin.val_succ, Nat.add_assoc]
  · exact hbudget i

/-- Exact finite-path expansion.  In particular, no hidden `O(·)` term is
used in the trajectory comparison. -/
theorem pathComparisonCost_eq_drift_add_mismatch_add_remainder
    {start N : ℕ} (hstart : 0 < start) (q : NatPath N) :
    pathComparisonCost start N q =
      driftPathAction start N q + pathDenominatorMismatch start N q +
        pathSharpRemainder N q := by
  unfold pathComparisonCost driftPathAction pathDenominatorMismatch pathSharpRemainder
  calc
    (∑ i : Fin N,
        comparisonCost (start + i) (q i.castSucc) (q i.succ)
          (centeredPath start q i.castSucc) (centeredPath start q i.succ)) =
        ∑ i : Fin N,
          (driftIncrementAction (start + i) (q i.castSucc) (q i.succ) +
            denominatorMismatchAction (start + i) (q i.castSucc) (q i.succ) +
              sharpRemainder (q i.castSucc) (q i.succ)) := by
      apply Finset.sum_congr rfl
      intro i hi
      simp only [centeredPath]
      convert
        (comparisonCost_centered_eq
          (ℓ := start + (i : ℕ)) (b := q i.castSucc) (b' := q i.succ) (by omega))
        using 1 <;> simp [Nat.add_assoc]
    _ = _ := by
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib]

/-- Every elementary local-limit loss is now bounded uniformly on the
corridor.  The right side depends only on the prescribed radii, not on the
trajectory. -/
theorem pathComparisonCost_le_corridorBound {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N}
    (hstart : 0 < start) (hq : InParabolicCorridor start R q)
    (hbudget : ParabolicRadiusBudget start N R) :
    pathComparisonCost start N q ≤ corridorComparisonCostBound start N R := by
  rw [pathComparisonCost_eq_drift_add_mismatch_add_remainder hstart]
  unfold corridorComparisonCostBound
  have hd := driftPathAction_le_corridorDriftBound hstart hq
  have hm := pathDenominatorMismatch_le_corridorBound hq hbudget
  have hr := pathSharpRemainder_le_corridorBound hq hbudget
  linarith

theorem pathNormalizationRatio_nonneg (start N : ℕ) (q : NatPath N) :
    0 ≤ pathNormalizationRatio start N q := by
  unfold pathNormalizationRatio
  exact Finset.prod_nonneg fun i hi ↦ normalizationRatio_nonneg _ _

theorem exp_neg_pathNormalizationCost_le {start N : ℕ}
    {R : Fin (N + 1) → ℕ} {q : NatPath N} (hstart : 0 < start)
    (hq : InParabolicCorridor start R q)
    (hbudget : ParabolicRadiusBudget start N R) :
    Real.exp (-pathNormalizationCost start N R) ≤
      pathNormalizationRatio start N q := by
  unfold pathNormalizationCost pathNormalizationRatio
  rw [show -(∑ i : Fin N,
      (R i.castSucc : ℝ) / (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)) =
      ∑ i : Fin N,
        -((R i.castSucc : ℝ) / (2 * ((start + (i : ℕ) : ℕ) : ℝ) ^ 2)) by
      rw [Finset.sum_neg_distrib], Real.exp_sum]
  apply Finset.prod_le_prod
  · intro i hi
    exact (Real.exp_pos _).le
  · intro i hi
    apply exp_neg_radius_div_le_normalizationRatio (by omega)
    · exact Nat.zero_lt_of_lt
        ((pathLocalConditions_of_parabolicCorridor hq hbudget).1 i)
    · exact hq i.castSucc

/-- Finite trajectory form of the pointwise local comparison. -/
theorem gaussianPathWeight_le_halfNegBinPathWeight {start N : ℕ}
    (hstart : 0 < start) (q : NatPath N)
    (hb : ∀ i : Fin N, 2 ≤ q i.castSucc)
    (hd : ∀ i : Fin N, 4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc) :
    pathNormalizationRatio start N q * Real.exp (-pathComparisonCost start N q) *
        Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q) ≤
      halfNegBinPathWeight q := by
  have hpoint : ∀ i : Fin N,
      normalizationRatio (start + i) (q i.castSucc) *
          Real.exp
            (-comparisonCost (start + i) (q i.castSucc) (q i.succ)
              (centeredPath start q i.castSucc) (centeredPath start q i.succ)) *
          Erdos1166.HLOZLemmaA8.b (start + i) (centeredPath start q i.castSucc)
            (centeredPath start q i.succ) ≤
        Erdos1166.HLOZAppendixA.halfNegBinMass (q i.castSucc) (q i.succ) := by
    intro i
    exact gaussianTransition_le_halfNegBinMass (by omega) (hb i) (hd i) _ _
  calc
    pathNormalizationRatio start N q * Real.exp (-pathComparisonCost start N q) *
        Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q) =
      ∏ i : Fin N,
        (normalizationRatio (start + i) (q i.castSucc) *
          Real.exp
            (-comparisonCost (start + i) (q i.castSucc) (q i.succ)
              (centeredPath start q i.castSucc) (centeredPath start q i.succ)) *
          Erdos1166.HLOZLemmaA8.b (start + i) (centeredPath start q i.castSucc)
            (centeredPath start q i.succ)) := by
      rw [pathNormalizationRatio, pathComparisonCost,
        Erdos1166.HLOZLemmaA8.pathWeight,
        show -(∑ i : Fin N,
            comparisonCost (start + i) (q i.castSucc) (q i.succ)
              (centeredPath start q i.castSucc) (centeredPath start q i.succ)) =
          ∑ i : Fin N,
            -comparisonCost (start + i) (q i.castSucc) (q i.succ)
              (centeredPath start q i.castSucc) (centeredPath start q i.succ) by
            rw [Finset.sum_neg_distrib],
        Real.exp_sum, Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    _ ≤ ∏ i : Fin N,
        Erdos1166.HLOZAppendixA.halfNegBinMass (q i.castSucc) (q i.succ) := by
      exact Finset.prod_le_prod
        (fun i hi ↦ mul_nonneg
          (mul_nonneg (normalizationRatio_nonneg _ _) (Real.exp_pos _).le)
          (Erdos1166.HLOZLemmaA8.b_nonneg _ _ _))
        (fun i hi ↦ hpoint i)
    _ = halfNegBinPathWeight q := rfl

/-- Sum of negative-binomial trajectory weights over a finite family. -/
noncomputable def halfNegBinPathSum {N : ℕ} (Q : Finset (NatPath N)) : ℝ :=
  ∑ q ∈ Q, halfNegBinPathWeight q

/-- The corresponding sum of the Lemma-A.8 Gaussian weights after centering. -/
noncomputable def centeredGaussianPathSum (start N : ℕ) (Q : Finset (NatPath N)) : ℝ :=
  ∑ q ∈ Q, Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q)

/-- The exact weighted Gaussian corridor sum produced by the sharp local
comparison, before making any uniform estimates on its elementary factors. -/
noncomputable def weightedCenteredGaussianPathSum
    (start N : ℕ) (Q : Finset (NatPath N)) : ℝ :=
  ∑ q ∈ Q,
    pathNormalizationRatio start N q * Real.exp (-pathComparisonCost start N q) *
      Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q)

theorem centeredGaussianPathSum_nonneg (start N : ℕ) (Q : Finset (NatPath N)) :
    0 ≤ centeredGaussianPathSum start N Q := by
  unfold centeredGaussianPathSum
  exact Finset.sum_nonneg fun q hq ↦
    Erdos1166.HLOZLemmaA8.pathWeight_nonneg _ _ _

theorem weightedCenteredGaussianPathSum_nonneg
    (start N : ℕ) (Q : Finset (NatPath N)) :
    0 ≤ weightedCenteredGaussianPathSum start N Q := by
  unfold weightedCenteredGaussianPathSum
  exact Finset.sum_nonneg fun q hq ↦
    mul_nonneg
      (mul_nonneg (pathNormalizationRatio_nonneg _ _ _) (Real.exp_pos _).le)
      (Erdos1166.HLOZLemmaA8.pathWeight_nonneg _ _ _)

/-- The checked trajectory/product lower bound corresponding to the local
part of HLOZ Proposition A.7.  All probability factors are explicit; no
asymptotic premise occurs here. -/
theorem weightedCenteredGaussianPathSum_le_halfNegBinPathSum
    {start N : ℕ} (Q : Finset (NatPath N)) (hstart : 0 < start)
    (hb : ∀ q ∈ Q, ∀ i : Fin N, 2 ≤ q i.castSucc)
    (hd : ∀ q ∈ Q, ∀ i : Fin N,
      4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc) :
    weightedCenteredGaussianPathSum start N Q ≤ halfNegBinPathSum Q := by
  unfold weightedCenteredGaussianPathSum halfNegBinPathSum
  exact Finset.sum_le_sum fun q hq ↦
    gaussianPathWeight_le_halfNegBinPathWeight hstart q (hb q hq) (hd q hq)

/-- Consequently, the only remaining premise for any desired corridor lower
bound is the corresponding lower bound on the explicit weighted Gaussian
sum. -/
theorem halfNegBinPathSum_lower_of_weightedGaussian
    {start N : ℕ} (Q : Finset (NatPath N)) {G : ℝ} (hstart : 0 < start)
    (hb : ∀ q ∈ Q, ∀ i : Fin N, 2 ≤ q i.castSucc)
    (hd : ∀ q ∈ Q, ∀ i : Fin N,
      4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc)
    (hGaussian : G ≤ weightedCenteredGaussianPathSum start N Q) :
    G ≤ halfNegBinPathSum Q :=
  hGaussian.trans (weightedCenteredGaussianPathSum_le_halfNegBinPathSum Q hstart hb hd)

/-- Window-specialized trajectory bound.  The local positivity and
quarter-width hypotheses are discharged from the explicit parabolic radius
budget, so the only quantitative premise left is the lower bound on the
weighted Gaussian corridor sum. -/
theorem halfNegBinPathSum_lower_of_parabolicCorridor
    {start N : ℕ} (Q : Finset (NatPath N)) (R : Fin (N + 1) → ℕ) {G : ℝ}
    (hstart : 0 < start) (hbudget : ParabolicRadiusBudget start N R)
    (hQ : ∀ q ∈ Q, InParabolicCorridor start R q)
    (hGaussian : G ≤ weightedCenteredGaussianPathSum start N Q) :
    G ≤ halfNegBinPathSum Q := by
  apply halfNegBinPathSum_lower_of_weightedGaussian Q hstart
  · intro q hq
    exact (pathLocalConditions_of_parabolicCorridor (hQ q hq) hbudget).1
  · intro q hq
    exact (pathLocalConditions_of_parabolicCorridor (hQ q hq) hbudget).2
  · exact hGaussian

/-- A convenient corollary that factors uniform elementary bounds `R` and
`C` out of the exact weighted Gaussian sum.  The only genuinely many-path
input is the displayed premise `hGaussian`; `hRatio` and `hCost` are
pointwise analytic estimates on the explicit factors. -/
theorem halfNegBinPathSum_lower_of_gaussian {start N : ℕ}
    (Q : Finset (NatPath N)) {G R C : ℝ} (hstart : 0 < start)
    (hG : 0 ≤ G) (hR : 0 ≤ R)
    (hb : ∀ q ∈ Q, ∀ i : Fin N, 2 ≤ q i.castSucc)
    (hd : ∀ q ∈ Q, ∀ i : Fin N,
      4 * Nat.dist (q i.castSucc) (q i.succ) ≤ q i.castSucc)
    (hRatio : ∀ q ∈ Q, R ≤ pathNormalizationRatio start N q)
    (hCost : ∀ q ∈ Q, pathComparisonCost start N q ≤ C)
    (hGaussian : G ≤ centeredGaussianPathSum start N Q) :
    R * Real.exp (-C) * G ≤ halfNegBinPathSum Q := by
  calc
    R * Real.exp (-C) * G ≤
        R * Real.exp (-C) * centeredGaussianPathSum start N Q :=
      mul_le_mul_of_nonneg_left hGaussian (mul_nonneg hR (Real.exp_pos _).le)
    _ ≤ halfNegBinPathSum Q := by
      unfold centeredGaussianPathSum halfNegBinPathSum
      rw [Finset.mul_sum]
      apply Finset.sum_le_sum
      intro q hq
      have hexp : Real.exp (-C) ≤ Real.exp (-pathComparisonCost start N q) :=
        Real.exp_le_exp.mpr (by linarith [hCost q hq])
      calc
        R * Real.exp (-C) *
            Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q) ≤
            pathNormalizationRatio start N q *
              Real.exp (-pathComparisonCost start N q) *
              Erdos1166.HLOZLemmaA8.pathWeight start N (centeredPath start q) := by
          exact mul_le_mul
            (mul_le_mul (hRatio q hq) hexp (Real.exp_pos _).le
              (pathNormalizationRatio_nonneg _ _ _))
            le_rfl
            (Erdos1166.HLOZLemmaA8.pathWeight_nonneg _ _ _)
            (mul_nonneg (pathNormalizationRatio_nonneg _ _ _)
              (Real.exp_pos _).le)
        _ ≤ halfNegBinPathWeight q :=
          gaussianPathWeight_le_halfNegBinPathWeight hstart q (hb q hq) (hd q hq)

/-- Fully instantiated corridor transfer.  All local-limit, normalization,
denominator, and drift estimates are discharged by the explicit expressions
on the left.  The sole remaining analytic input is `hGaussian`, the
many-path Gaussian corridor lower bound supplied by Lemma A.8. -/
theorem corridor_halfNegBinPathSum_lower {start N : ℕ}
    (Q : Finset (NatPath N)) (R : Fin (N + 1) → ℕ) {G : ℝ}
    (hstart : 0 < start) (hG : 0 ≤ G)
    (hbudget : ParabolicRadiusBudget start N R)
    (hQ : ∀ q ∈ Q, InParabolicCorridor start R q)
    (hGaussian : G ≤ centeredGaussianPathSum start N Q) :
    Real.exp (-pathNormalizationCost start N R) *
        Real.exp (-corridorComparisonCostBound start N R) * G ≤
      halfNegBinPathSum Q := by
  apply halfNegBinPathSum_lower_of_gaussian Q hstart hG
      (Real.exp_pos _).le
  · intro q hq
    exact (pathLocalConditions_of_parabolicCorridor (hQ q hq) hbudget).1
  · intro q hq
    exact (pathLocalConditions_of_parabolicCorridor (hQ q hq) hbudget).2
  · intro q hq
    exact exp_neg_pathNormalizationCost_le hstart (hQ q hq) hbudget
  · intro q hq
    exact pathComparisonCost_le_corridorBound hstart (hQ q hq) hbudget
  · exact hGaussian

/-- Literal HLOZ power-corridor specialization.  For every `δ < 1`, a
single cutoff makes the preceding theorem applicable to every finite tail
`|m_ℓ-2ℓ²| ≤ floor(ℓ^(1+δ))`.  Thus, past the finite prefix, the only premise
is precisely the corresponding many-path Gaussian lower bound. -/
theorem eventually_hlozCorridor_halfNegBinPathSum_lower {δ : ℝ}
    (hδ : δ < 1) :
    ∀ᶠ start : ℕ in atTop,
      ∀ (N : ℕ) (Q : Finset (NatPath N)) (G : ℝ),
        0 ≤ G →
        (∀ q ∈ Q, InParabolicCorridor start (hlozRadius δ start N) q) →
        G ≤ centeredGaussianPathSum start N Q →
        Real.exp (-pathNormalizationCost start N (hlozRadius δ start N)) *
            Real.exp (-corridorComparisonCostBound start N
              (hlozRadius δ start N)) * G ≤
          halfNegBinPathSum Q := by
  filter_upwards [eventually_hlozRadiusBudget hδ, eventually_ge_atTop 1]
    with start hbudget hstart
  intro N Q G hG hQ hGaussian
  exact corridor_halfNegBinPathSum_lower Q (hlozRadius δ start N)
    (by omega) hG (hbudget N) hQ hGaussian

end Erdos1166.HLOZPropositionA7
