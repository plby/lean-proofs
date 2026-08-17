/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos294.WeightedMinor
import UnitFractions.FinalResults

/-!
# Dense regular smooth denominator sets for Erdős Problem 294

We work in the fixed interval `(N/99,N]`.  Its reciprocal mass has a fixed
positive margin above three.  The existing regularity and smoothness
filters, followed by the local-mass pruning lemma, lose only `o(1)` mass.
The existing inverse theorem then produces a subset satisfying
`good_condition` while retaining mass strictly above one.
-/

open Filter Real
open scoped BigOperators ArithmeticFunction.omega Topology

namespace Erdos294.LowerSetup

open Finset
open UnitFractions

noncomputable section

attribute [local instance] Classical.propDecidable

def wideInterval (N : ℕ) : Finset ℕ :=
  Finset.Icc (N / 99 + 1) N

def smoothCutoff (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - (8 : ℝ) / log (log (N : ℝ)))

def forceScale (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - (1 : ℝ) / log (log (N : ℝ)))

def inverseK (N : ℕ) : ℝ :=
  (N : ℝ) ^ (1 - (3 : ℝ) / log (log (N : ℝ)))

def inverseT (N : ℕ) : ℝ :=
  forceScale N / log (N : ℝ)

def inverseL (N : ℕ) : ℝ :=
  forceScale N / (2 * (log (N : ℝ)) ^ (1 / 100 : ℝ))

def localThreshold (N : ℕ) : ℝ :=
  (log (N : ℝ)) ^ (-(1 / 100 : ℝ))

/-- We use the whole fixed-width interval as the scale in the inverse
theorem.  This is larger than the source's auxiliary scale and gives more
room in all subsequent circle estimates. -/
def setupM (N : ℕ) : ℝ := (N : ℝ) / 99

def setupK (N : ℕ) : ℝ :=
  setupM N * (N : ℝ) ^ (-(2 : ℝ) / log (log (N : ℝ)))

def setupT (N : ℕ) : ℝ := setupM N / log (N : ℝ)

def setupL (N : ℕ) : ℝ :=
  setupM N / (2 * (log (N : ℝ)) ^ (1 / 100 : ℝ))

def reciprocalMass (A : Finset ℕ) : ℝ :=
  ∑ n ∈ A, (1 : ℝ) / n

lemma reciprocalMass_eq_cast_rec_sum (A : Finset ℕ) :
    reciprocalMass A = (rec_sum A : ℝ) := by
  simp [reciprocalMass, rec_sum]

@[simp] lemma mem_wideInterval {N n : ℕ} :
    n ∈ wideInterval N ↔ N / 99 + 1 ≤ n ∧ n ≤ N := by
  simp [wideInterval]

lemma wideInterval_subset_range_succ (N : ℕ) :
    wideInterval N ⊆ Finset.range (N + 1) := by
  intro n hn
  rw [Finset.mem_range]
  exact Nat.lt_succ_of_le (mem_wideInterval.mp hn).2

lemma zero_not_mem_wideInterval (N : ℕ) : 0 ∉ wideInterval N := by
  simp [wideInterval]

lemma wideInterval_lower_real {N n : ℕ} (hN : 0 < N)
    (hn : n ∈ wideInterval N) : (N : ℝ) / 99 < n := by
  have hlt : N < (N / 99 + 1) * 99 := by
    simpa [mul_comm] using Nat.lt_mul_div_succ N (by norm_num : 0 < 99)
  have hle : (N / 99 + 1) * 99 ≤ n * 99 := by
    gcongr
    exact (mem_wideInterval.mp hn).1
  have hreal : (N : ℝ) < n * 99 := by exact_mod_cast hlt.trans_le hle
  norm_num at hreal ⊢
  linarith

lemma exp_four_lt_99 : Real.exp (4 : ℝ) < 99 := by
  calc
    Real.exp (4 : ℝ) = Real.exp (4 * 1) := by norm_num
    _ = (Real.exp 1) ^ 4 := by
      rw [show (4 : ℝ) * 1 = ((4 : ℕ) : ℝ) * 1 by norm_num,
        Real.exp_nat_mul]
    _ < (3 : ℝ) ^ 4 := by
      gcongr
      exact Real.exp_one_lt_three
    _ < 99 := by norm_num

lemma four_lt_log_99 : (4 : ℝ) < Real.log 99 := by
  rw [lt_log_iff_exp_lt (by norm_num)]
  exact exp_four_lt_99

def massMargin : ℝ := (Real.log 99 - 4) / 4

/-- The interval with its upper endpoint removed, so that it lies in
`range N`, as required by the two density filters. -/
def workingInterval (N : ℕ) : Finset ℕ :=
  (wideInterval N).erase N

def regularBad (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun n : ℕ =>
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log (N : ℝ)) ≤ ω n ∧
      (ω n : ℝ) ≤ 2 * log (log (N : ℝ)))

def smoothBad (N : ℕ) (A : Finset ℕ) : Finset ℕ :=
  A.filter fun n : ℕ =>
    ∃ q : ℕ, IsPrimePow q ∧ smoothCutoff N < (q : ℝ) ∧ q ∣ n

/-- The fixed-width interval after the standard regularity and smoothness
filters. -/
def regularSmoothInterval (N : ℕ) : Finset ℕ :=
  workingInterval N \ (regularBad N (workingInterval N) ∪
    smoothBad N (workingInterval N))

lemma massMargin_pos : 0 < massMargin := by
  dsimp [massMargin]
  exact div_pos (sub_pos.mpr four_lt_log_99) (by norm_num)

lemma workingInterval_subset_range (N : ℕ) :
    workingInterval N ⊆ Finset.range N := by
  intro n hn
  rw [workingInterval, Finset.mem_erase] at hn
  rw [Finset.mem_range]
  have hnN := (mem_wideInterval.mp hn.2).2
  omega

lemma workingInterval_subset_wideInterval (N : ℕ) :
    workingInterval N ⊆ wideInterval N := Finset.erase_subset _ _

lemma regularSmoothInterval_subset_working (N : ℕ) :
    regularSmoothInterval N ⊆ workingInterval N := Finset.sdiff_subset

lemma regularSmoothInterval_subset_range_succ (N : ℕ) :
    regularSmoothInterval N ⊆ Finset.range (N + 1) := by
  exact (regularSmoothInterval_subset_working N).trans
    ((workingInterval_subset_wideInterval N).trans (wideInterval_subset_range_succ N))

lemma zero_not_mem_regularSmoothInterval (N : ℕ) :
    0 ∉ regularSmoothInterval N := by
  intro h
  exact zero_not_mem_wideInterval N
    (workingInterval_subset_wideInterval N (regularSmoothInterval_subset_working N h))

lemma regularSmoothInterval_regular (N : ℕ) :
    arith_regular N (regularSmoothInterval N) := by
  intro n hn
  have hnwork := regularSmoothInterval_subset_working N hn
  have hnnot : n ∉ regularBad N (workingInterval N) := by
    have := (Finset.mem_sdiff.mp hn).2
    intro hbad
    exact this (Finset.mem_union_left _ hbad)
  have hn0 : n ≠ 0 := ne_of_mem_of_not_mem
    (workingInterval_subset_wideInterval N hnwork) (zero_not_mem_wideInterval N)
  simpa [regularBad, hnwork, hn0] using hnnot

lemma regularSmoothInterval_smooth (N : ℕ) :
    ∀ n ∈ regularSmoothInterval N, is_smooth (smoothCutoff N) n := by
  intro n hn q hq hqn
  have hnwork := regularSmoothInterval_subset_working N hn
  have hnnot : n ∉ smoothBad N (workingInterval N) := by
    have := (Finset.mem_sdiff.mp hn).2
    intro hbad
    exact this (Finset.mem_union_right _ hbad)
  apply le_of_not_gt
  intro hcut
  apply hnnot
  rw [smoothBad, Finset.mem_filter]
  exact ⟨hnwork, q, hq, hcut, hqn⟩

lemma regularSmoothInterval_lower (N : ℕ) :
    ∀ n ∈ regularSmoothInterval N, (N : ℝ) / 99 ≤ n := by
  intro n hn
  have hnwork := regularSmoothInterval_subset_working N hn
  have hnwide := workingInterval_subset_wideInterval N hnwork
  have hnne : n ≠ N := (Finset.mem_erase.mp hnwork).1
  have hN : 0 < N := by
    have hnN := (mem_wideInterval.mp hnwide).2
    omega
  exact (wideInterval_lower_real hN hnwide).le

lemma wideInterval_sum_eq_harmonic_sub (N : ℕ) :
    ∑ n ∈ wideInterval N, (1 : ℝ) / n =
      (harmonic N : ℝ) - (harmonic (N / 99) : ℝ) := by
  have hmN : N / 99 ≤ N := Nat.div_le_self _ _
  have hdisj : Disjoint (Finset.Icc 1 (N / 99)) (wideInterval N) := by
    rw [Finset.disjoint_left]
    intro n hnlow hnhigh
    have hle := (Finset.mem_Icc.mp hnlow).2
    have hge := (mem_wideInterval.mp hnhigh).1
    omega
  have hunion : Finset.Icc 1 (N / 99) ∪ wideInterval N = Finset.Icc 1 N := by
    ext n
    simp only [Finset.mem_union, Finset.mem_Icc, mem_wideInterval]
    omega
  have hsum :
      ∑ n ∈ Finset.Icc 1 (N / 99), (1 : ℝ) / n +
          ∑ n ∈ wideInterval N, (1 : ℝ) / n =
        ∑ n ∈ Finset.Icc 1 N, (1 : ℝ) / n := by
    rw [← Finset.sum_union hdisj, hunion]
  simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv,
    Rat.cast_natCast, one_div]
  push_cast
  apply eq_sub_iff_add_eq.mpr
  simpa only [one_div, add_comm] using hsum

/-- The unfiltered fixed-width interval has reciprocal mass at least
`3 + 4 * massMargin`. -/
lemma wideInterval_mass_lower {N : ℕ} (hN : 99 ≤ N) :
    3 + 4 * massMargin ≤ ∑ n ∈ wideInterval N, (1 : ℝ) / n := by
  rw [wideInterval_sum_eq_harmonic_sub]
  have hlow := log_add_one_le_harmonic N
  have hupp := harmonic_le_one_add_log (N / 99)
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 99) hN)
  have hmposNat : 0 < N / 99 := Nat.div_pos hN (by norm_num : 0 < 99)
  have hmposCast : (0 : ℝ) < (N / 99 : ℕ) := by exact_mod_cast hmposNat
  have hmpos : (0 : ℝ) < (N : ℝ) / 99 := div_pos hNpos (by norm_num)
  have hlogm : Real.log (N / 99 : ℕ) ≤ Real.log ((N : ℝ) / 99) := by
    apply Real.log_le_log
    · exact hmposCast
    · exact Nat.cast_div_le
  have hlogN : Real.log (N : ℝ) ≤ Real.log (N + 1 : ℕ) := by
    apply Real.log_le_log hNpos
    exact_mod_cast Nat.le_succ N
  have hratio : Real.log (N : ℝ) - Real.log ((N : ℝ) / 99) = Real.log 99 := by
    rw [Real.log_div (ne_of_gt hNpos) (by norm_num : (99 : ℝ) ≠ 0),
      ]
    ring
  dsimp [massMargin]
  have hmargin : 4 * ((Real.log 99 - 4) / 4) = Real.log 99 - 4 := by ring
  rw [hmargin]
  push_cast at hlow hupp hlogN
  have hmain :
      Real.log (N : ℝ) - 1 - Real.log ((N / 99 : ℕ) : ℝ) ≤
        (harmonic N : ℝ) - (harmonic (N / 99) : ℝ) := by
    linarith
  linarith

lemma wideInterval_mass_upper {N : ℕ} (hN : 0 < N) :
    ∑ n ∈ wideInterval N, (1 : ℝ) / n ≤ 99 := by
  calc
    ∑ n ∈ wideInterval N, (1 : ℝ) / n ≤
        ∑ _n ∈ wideInterval N, 99 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnpos : (0 : ℝ) < n := by
        exact lt_of_lt_of_le (div_pos (by exact_mod_cast hN) (by norm_num))
          (wideInterval_lower_real hN hn).le
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_div_iff₀ hnpos hNreal]
      have := wideInterval_lower_real hN hn
      nlinarith
    _ = (wideInterval N).card * (99 / (N : ℝ)) := by simp [nsmul_eq_mul]
    _ ≤ (N : ℝ) * (99 / (N : ℝ)) := by
      gcongr
      have hcard : (wideInterval N).card ≤ N := by
        simp [wideInterval]
      exact_mod_cast hcard
    _ = 99 := by field_simp

lemma workingInterval_mass_lower {N : ℕ} (hN : 99 ≤ N) :
    3 + 4 * massMargin - 1 / (N : ℝ) ≤ reciprocalMass (workingInterval N) := by
  have hmem : N ∈ wideInterval N := by
    rw [mem_wideInterval]
    constructor <;> omega
  have herase := Finset.sum_erase_add
    (s := wideInterval N) (f := fun n : ℕ ↦ (1 : ℝ) / n) hmem
  have hlower := wideInterval_mass_lower hN
  rw [reciprocalMass, workingInterval]
  linarith

lemma reciprocalMass_le_card_mul {N : ℕ} (hN : 0 < N)
    {A : Finset ℕ} (hA : A ⊆ wideInterval N) :
    reciprocalMass A ≤ (A.card : ℝ) * (99 / (N : ℝ)) := by
  unfold reciprocalMass
  calc
    ∑ n ∈ A, (1 : ℝ) / n ≤ ∑ _n ∈ A, 99 / (N : ℝ) := by
      apply Finset.sum_le_sum
      intro n hn
      have hnwide := hA hn
      have hnpos : (0 : ℝ) < n := by
        exact lt_of_lt_of_le (div_pos (by exact_mod_cast hN) (by norm_num))
          (wideInterval_lower_real hN hnwide).le
      have hNreal : (0 : ℝ) < N := by exact_mod_cast hN
      rw [div_le_div_iff₀ hnpos hNreal]
      nlinarith [wideInterval_lower_real hN hnwide]
    _ = (A.card : ℝ) * (99 / (N : ℝ)) := by simp [nsmul_eq_mul]

lemma reciprocalMass_union_le (A B : Finset ℕ) :
    reciprocalMass (A ∪ B) ≤ reciprocalMass A + reciprocalMass B := by
  rw [reciprocalMass_eq_cast_rec_sum, reciprocalMass_eq_cast_rec_sum,
    reciprocalMass_eq_cast_rec_sum]
  exact_mod_cast rec_sum_union (A := A) (B := B)

lemma reciprocalMass_mono {A B : Finset ℕ} (hAB : A ⊆ B) :
    reciprocalMass A ≤ reciprocalMass B := by
  rw [reciprocalMass_eq_cast_rec_sum, reciprocalMass_eq_cast_rec_sum]
  exact_mod_cast rec_sum_mono hAB

lemma reciprocalMass_sdiff_add (A B : Finset ℕ) :
    reciprocalMass A ≤ reciprocalMass (A \ B) + reciprocalMass B := by
  calc
    reciprocalMass A = reciprocalMass ((A \ B) ∪ (A ∩ B)) := by
      rw [Finset.sdiff_union_inter]
    _ ≤ reciprocalMass (A \ B) + reciprocalMass (A ∩ B) :=
      reciprocalMass_union_le _ _
    _ ≤ reciprocalMass (A \ B) + reciprocalMass B := by
      gcongr
      rw [reciprocalMass_eq_cast_rec_sum, reciprocalMass_eq_cast_rec_sum]
      exact_mod_cast rec_sum_mono (Finset.inter_subset_right)

/-- A fixed filter constant large enough that both exceptional sets together
cost much less than `massMargin`. -/
def filterConstant : ℝ := 3168 / massMargin

lemma filterConstant_pos : 0 < filterConstant :=
  div_pos (by norm_num) massMargin_pos

lemma exceptional_reciprocalMass_le {N : ℕ} (hN : 0 < N)
    {E : Finset ℕ} (hE : E ⊆ workingInterval N) {D : ℝ} (hD : 0 < D)
    (hcard : (E.card : ℝ) ≤ (N : ℝ) / D) :
    reciprocalMass E ≤ 99 / D := by
  have hbase := reciprocalMass_le_card_mul hN
    (hE.trans (workingInterval_subset_wideInterval N))
  calc
    reciprocalMass E ≤ (E.card : ℝ) * (99 / (N : ℝ)) := hbase
    _ ≤ ((N : ℝ) / D) * (99 / (N : ℝ)) := by
      gcongr
    _ = 99 / D := by
      have hNR : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      field_simp

lemma regularBad_subset_working (N : ℕ) :
    regularBad N (workingInterval N) ⊆ workingInterval N := Finset.filter_subset _ _

lemma smoothBad_subset_working (N : ℕ) :
    smoothBad N (workingInterval N) ⊆ workingInterval N := Finset.filter_subset _ _

lemma regularSmoothInterval_mass_bound
    {N : ℕ} (hN : 99 ≤ N)
    (hregcard : ((regularBad N (workingInterval N)).card : ℝ) ≤
      (N : ℝ) / filterConstant)
    (hsmoothcard : ((smoothBad N (workingInterval N)).card : ℝ) ≤
      (N : ℝ) / filterConstant) :
    3 + 4 * massMargin - 1 / (N : ℝ) - massMargin / 16 ≤
      reciprocalMass (regularSmoothInterval N) := by
  have hNpos : 0 < N := lt_of_lt_of_le (by norm_num) hN
  let R := regularBad N (workingInterval N)
  let S := smoothBad N (workingInterval N)
  have hR : reciprocalMass R ≤ massMargin / 32 := by
    calc
      reciprocalMass R ≤ 99 / filterConstant :=
        exceptional_reciprocalMass_le hNpos (regularBad_subset_working N)
          filterConstant_pos hregcard
      _ = massMargin / 32 := by
        rw [filterConstant]
        field_simp [massMargin_pos.ne']
        ring
  have hS : reciprocalMass S ≤ massMargin / 32 := by
    calc
      reciprocalMass S ≤ 99 / filterConstant :=
        exceptional_reciprocalMass_le hNpos (smoothBad_subset_working N)
          filterConstant_pos hsmoothcard
      _ = massMargin / 32 := by
        rw [filterConstant]
        field_simp [massMargin_pos.ne']
        ring
  have hunion : reciprocalMass (R ∪ S) ≤ massMargin / 16 := by
    calc
      reciprocalMass (R ∪ S) ≤ reciprocalMass R + reciprocalMass S :=
        reciprocalMass_union_le _ _
      _ ≤ massMargin / 32 + massMargin / 32 := add_le_add hR hS
      _ = massMargin / 16 := by ring
  have hsplit := reciprocalMass_sdiff_add (workingInterval N) (R ∪ S)
  change reciprocalMass (workingInterval N) ≤
    reciprocalMass (regularSmoothInterval N) + reciprocalMass (R ∪ S) at hsplit
  linarith [workingInterval_mass_lower hN]

theorem eventually_regularSmoothInterval_mass :
    ∀ᶠ N : ℕ in atTop,
      3 + (7 / 2 : ℝ) * massMargin ≤ reciprocalMass (regularSmoothInterval N) := by
  filter_upwards
    [ filter_regular filterConstant filterConstant_pos
    , filter_smooth filterConstant filterConstant_pos
    , eventually_ge_atTop (99 : ℕ)
    , tendsto_natCast_atTop_atTop.eventually
        (eventually_ge_atTop (8 / massMargin : ℝ)) ] with
      N hreg hsmooth hN hNlarge
  have hregcard := hreg (workingInterval N) (workingInterval_subset_range N)
  have hsmoothcard := hsmooth (workingInterval N) (workingInterval_subset_range N)
  have hmass := regularSmoothInterval_mass_bound hN hregcard hsmoothcard
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 99) hN)
  have hinv : 1 / (N : ℝ) ≤ massMargin / 8 := by
    rw [div_le_iff₀ hNpos]
    calc
      (1 : ℝ) = (massMargin / 8) * (8 / massMargin) := by
        field_simp [massMargin_pos.ne']
      _ ≤ (massMargin / 8) * (N : ℝ) := by
        exact mul_le_mul_of_nonneg_left hNlarge
          (div_nonneg massMargin_pos.le (by norm_num))
  nlinarith [massMargin_pos]

lemma eventually_localThreshold_loss :
    ∀ᶠ N : ℕ in atTop,
      localThreshold N * 2 * log (log (N : ℝ)) ≤ massMargin / 8 := by
  have hlarge := large_enough_N 1 (by norm_num : (0 : ℝ) < 1)
  have hp := tendsto_coe_log_pow_at_top (1 / 200 : ℝ) (by norm_num)
  filter_upwards
    [ hlarge
    , hp.eventually (eventually_ge_atTop (8 / massMargin : ℝ)) ] with
      N hN hpow
  rcases hN with
    ⟨-, -, -, -, -, hlog, -, -, -, -, -, -, -, -, -, hthreshold, -, -, -, -, -⟩
  have hPpos : 0 < (log (N : ℝ)) ^ (1 / 200 : ℝ) :=
    Real.rpow_pos_of_pos hlog _
  have hsmall : (log (N : ℝ)) ^ (-(1 / 200 : ℝ)) ≤ massMargin / 8 := by
    rw [Real.rpow_neg (le_of_lt hlog)]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hPpos).2
    calc
      (1 : ℝ) = (massMargin / 8) * (8 / massMargin) := by
        field_simp [massMargin_pos.ne']
      _ ≤ (massMargin / 8) * (log (N : ℝ)) ^ (1 / 200 : ℝ) := by
        exact mul_le_mul_of_nonneg_left hpow
          (div_nonneg massMargin_pos.le (by norm_num))
  have hthreshold' :
      localThreshold N * 2 * log (log (N : ℝ)) ≤
        (log (N : ℝ)) ^ (-(1 / 200 : ℝ)) := by
    simpa [localThreshold, mul_assoc, mul_comm, mul_left_comm] using hthreshold
  exact hthreshold'.trans hsmall

lemma eventually_setup_parameters :
    ∀ᶠ N : ℕ in atTop,
      0 < setupM N ∧ setupM N ≤ (N : ℝ) ∧ (N : ℝ) ≤ (setupM N) ^ 2 ∧
      0 < localThreshold N ∧
      (log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ 1 := by
  filter_upwards
    [ eventually_ge_atTop (99 ^ 2 : ℕ)
    , tendsto_log_coe_at_top.eventually (eventually_ge_atTop (1 : ℝ)) ] with
      N hN hlog
  have hNpos : (0 : ℝ) < N := by
    exact_mod_cast (lt_of_lt_of_le (by norm_num : 0 < 99 ^ 2) hN)
  have hlogpos : 0 < log (N : ℝ) := lt_of_lt_of_le (by norm_num) hlog
  have hMpos : 0 < setupM N := div_pos hNpos (by norm_num)
  refine ⟨hMpos, ?_, ?_, Real.rpow_pos_of_pos hlogpos _, ?_⟩
  · dsimp [setupM]
    exact div_le_self hNpos.le (by norm_num)
  · dsimp [setupM]
    have hNR : (99 : ℝ) ^ 2 ≤ N := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 99 ^ 2)]
  · rw [Real.rpow_neg hlogpos.le]
    exact inv_le_one_of_one_le₀ (Real.one_le_rpow hlog (by norm_num))

/-- A dense smooth regular set with the exact inverse-theorem condition and
a fixed amount of reciprocal mass beyond one.  This is the deterministic
denominator supply used by the prescribed-target circle method. -/
theorem eventually_exists_preparedSet :
    ∀ᶠ N : ℕ in atTop, ∃ A : Finset ℕ,
      A ⊆ regularSmoothInterval N ∧
      1 + massMargin ≤ reciprocalMass A ∧
      reciprocalMass A ≤ 99 ∧
      (∀ q ∈ ppowers_in_set A, localThreshold N ≤ rec_sum_local A q) ∧
      good_condition A (setupK N) (setupT N) (setupL N) := by
  filter_upwards
    [ eventually_regularSmoothInterval_mass
    , eventually_localThreshold_loss
    , eventually_setup_parameters
    , pruning_lemma_one
    , force_good_properties
    , force_good_properties2
    , eventually_ge_atTop (99 : ℕ) ] with
      N hmass hloss hparam hprune hforce hforce2 hN
  rcases hparam with ⟨hMpos, hMN, hNM2, heps, hsmallpow⟩
  let C := regularSmoothInterval N
  have hCrange : C ⊆ Finset.range (N + 1) := regularSmoothInterval_subset_range_succ N
  have hC0 : 0 ∉ C := zero_not_mem_regularSmoothInterval N
  have hCreg : arith_regular N C := regularSmoothInterval_regular N
  have hCsmooth : ∀ n ∈ C, is_smooth (smoothCutoff N) n :=
    regularSmoothInterval_smooth N
  have hCM : ∀ n ∈ C, setupM N ≤ (n : ℝ) := regularSmoothInterval_lower N
  have hwideUpper : reciprocalMass (wideInterval N) ≤ 99 := by
    simpa [reciprocalMass] using
      (wideInterval_mass_upper (N := N) (lt_of_lt_of_le (by norm_num) hN))
  have hCupper : reciprocalMass C ≤ 99 :=
    (reciprocalMass_mono (regularSmoothInterval_subset_working N)).trans
      ((reciprocalMass_mono (workingInterval_subset_wideInterval N)).trans hwideUpper)
  obtain ⟨P, hPC, hPmass, hPlocal⟩ :=
    hprune C hCrange (localThreshold N) heps
  have hPrange : P ⊆ Finset.range (N + 1) := hPC.trans hCrange
  have hP0 : 0 ∉ P := fun h ↦ hC0 (hPC h)
  have hPreg : arith_regular N P := hCreg.subset hPC
  have hPM : ∀ n ∈ P, setupM N ≤ (n : ℝ) := fun n hn ↦ hCM n (hPC hn)
  have hPmassReal :
      3 + (27 / 8 : ℝ) * massMargin ≤ reciprocalMass P := by
    rw [reciprocalMass_eq_cast_rec_sum]
    rw [reciprocalMass_eq_cast_rec_sum] at hmass
    have hPmass' :
        (rec_sum C : ℝ) - localThreshold N * 2 * log (log (N : ℝ)) ≤
          (rec_sum P : ℝ) := by exact_mod_cast hPmass
    nlinarith [massMargin_pos]
  have hPrec : (log (N : ℝ)) ^ (-(1 / 101 : ℝ)) ≤ (rec_sum P : ℝ) := by
    rw [← reciprocalMass_eq_cast_rec_sum]
    exact hsmallpow.trans (by nlinarith [hPmassReal, massMargin_pos])
  have hPlocal' : ∀ q ∈ ppowers_in_set P,
      (log (N : ℝ)) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local P q := by
    intro q hq
    exact le_of_lt (hPlocal q hq)
  have hforceP := hforce (setupM N) P hPrange hMpos hMN hNM2 hP0 hPM hPreg hPrec hPlocal'
  rcases hforceP with hlowpp | hgood
  · obtain ⟨B, hBP, hPBmass, hBpp⟩ := hlowpp
    have hBrange : B ⊆ Finset.range (N + 1) := hBP.trans hPrange
    obtain ⟨A, hAB, hAmass, hAlocal⟩ :=
      hprune B hBrange (localThreshold N) heps
    have hAC : A ⊆ C := hAB.trans (hBP.trans hPC)
    have hAmassReal : 1 + massMargin ≤ reciprocalMass A := by
      rw [reciprocalMass_eq_cast_rec_sum]
      rw [reciprocalMass_eq_cast_rec_sum] at hPmassReal
      have hPBmass' : (rec_sum P : ℝ) ≤ 3 * (rec_sum B : ℝ) := by
        exact_mod_cast hPBmass
      have hAmass' :
          (rec_sum B : ℝ) - localThreshold N * 2 * log (log (N : ℝ)) ≤
            (rec_sum A : ℝ) := by exact_mod_cast hAmass
      nlinarith [massMargin_pos]
    have hArange : A ⊆ Finset.range (N + 1) := hAB.trans hBrange
    have hA0 : 0 ∉ A := fun h ↦ hC0 (hAC h)
    have hAreg : arith_regular N A := hCreg.subset hAC
    have hAM : ∀ n ∈ A, setupM N ≤ (n : ℝ) := fun n hn ↦ hCM n (hAC hn)
    have hAlocal' : ∀ q ∈ ppowers_in_set A,
        (log (N : ℝ)) ^ (-(1 / 100 : ℝ)) ≤ rec_sum_local A q := by
      intro q hq
      exact le_of_lt (hAlocal q hq)
    have hApp : (ppower_rec_sum A : ℝ) ≤ (2 / 3 : ℝ) * log (log (N : ℝ)) := by
      have hmono : ppower_rec_sum A ≤ ppower_rec_sum B := ppower_rec_sum_mono hAB
      have hmono' : (ppower_rec_sum A : ℝ) ≤ (ppower_rec_sum B : ℝ) := by
        exact_mod_cast hmono
      exact hmono'.trans hBpp
    have hgoodA := hforce2 (setupM N) A hArange hMpos hMN hNM2 hA0 hAM hAreg
      hAlocal' hApp
    refine ⟨A, hAC, hAmassReal, ?_, ?_, ?_⟩
    · exact (reciprocalMass_mono hAC).trans hCupper
    · intro q hq
      simpa only [localThreshold] using hAlocal' q hq
    · change good_condition A (setupK N) (setupT N) (setupL N) at hgoodA
      exact hgoodA
  · refine ⟨P, hPC, ?_, ?_, ?_, ?_⟩
    · nlinarith [hPmassReal, massMargin_pos]
    · exact (reciprocalMass_mono hPC).trans hCupper
    · intro q hq
      simpa only [localThreshold] using hPlocal' q hq
    · change good_condition P (setupK N) (setupT N) (setupL N) at hgood
      exact hgood

end

end Erdos294.LowerSetup
