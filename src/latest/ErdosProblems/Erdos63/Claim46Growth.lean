/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Lemma315
import ErdosProblems.Erdos63.Parameters

/-!
# Sharp fresh expansion for Liu--Montgomery Claim 4.6

Claim 4.6 needs one auxiliary expansion whose radius is charged twice inside
a simple adjuster.  The more generous bulk schedule used by Corollary 3.15
is therefore not suitable here.  This lower-level module supplies the sharp
variant without importing any adjuster module, so `AdjusterBase` can consume
it without an import cycle.

The seed has order `n/4`.  Writing
`C = ceil(9216 * log(n)^2)`, three `C`-blocks suffice to grow past half once
`6C <= n/4`.  Repeated centre-halving then gives final radius
`3C * (log_2(n/4)+1)`, with asymptotic coefficient
`3*9216/log(2)`, strictly below one quarter of the simple-adjuster radius.
-/

open Finset Set SimpleGraph
open scoped SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

universe u

variable {V : Type u} {G : SimpleGraph V}

/-- The fixed expansion-profile lower bound used by the sharp Claim 4.6
recurrence. -/
theorem lm43_expansion_profile_lower
    {N d s : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (s : ℝ)) (hsN : s ≤ N) :
    (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hdpos : (0 : ℝ) < (d : ℝ) := by
    exact_mod_cast (Nat.zero_lt_one.trans_le hd)
  have hNpos : (0 : ℝ) < (N : ℝ) := by exact_mod_cast (by omega : 0 < N)
  have hNlog : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hk : ((1 / 64 : ℝ) * (d : ℝ)) / 5 ≤ (s : ℝ) := by
    norm_num at hcutoff ⊢
    linarith
  rw [expansionEpsilon_of_le hk]
  have harg :
      15 * (s : ℝ) / ((1 / 64 : ℝ) * (d : ℝ)) =
        960 * (s : ℝ) / (d : ℝ) := by
    field_simp [ne_of_gt hdpos]
    <;> ring
  rw [harg]
  have hratioOne : (1 : ℝ) < 960 * (s : ℝ) / (d : ℝ) := by
    rw [lt_div_iff₀ hdpos]
    nlinarith
  have hlogRatio : 0 < Real.log (960 * (s : ℝ) / (d : ℝ)) :=
    Real.log_pos hratioOne
  have hsNreal : (s : ℝ) ≤ (N : ℝ) := by exact_mod_cast hsN
  have hdOne : (1 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  have hratioN : 960 * (s : ℝ) / (d : ℝ) ≤ 960 * (N : ℝ) := by
    calc
      960 * (s : ℝ) / (d : ℝ) ≤ 960 * (N : ℝ) / (d : ℝ) :=
        div_le_div_of_nonneg_right
          (mul_le_mul_of_nonneg_left hsNreal (by norm_num)) hdpos.le
      _ ≤ 960 * (N : ℝ) := div_le_self (by positivity) hdOne
  have hNsquare : (960 : ℝ) ≤ (N : ℝ) ^ 2 := by
    have hNreal : (32 : ℝ) ≤ (N : ℝ) := by exact_mod_cast hN
    nlinarith [sq_nonneg ((N : ℝ) - 32)]
  have hratioCube : 960 * (s : ℝ) / (d : ℝ) ≤ (N : ℝ) ^ 3 := by
    calc
      960 * (s : ℝ) / (d : ℝ) ≤ 960 * (N : ℝ) := hratioN
      _ ≤ (N : ℝ) * (N : ℝ) ^ 2 := by
        simpa [mul_comm] using
          (mul_le_mul_of_nonneg_right hNsquare hNpos.le)
      _ = (N : ℝ) ^ 3 := by ring
  have hlogUpper :
      Real.log (960 * (s : ℝ) / (d : ℝ)) ≤ 3 * Real.log (N : ℝ) := by
    calc
      Real.log (960 * (s : ℝ) / (d : ℝ)) ≤ Real.log ((N : ℝ) ^ 3) :=
        Real.log_le_log (by positivity) hratioCube
      _ = 3 * Real.log (N : ℝ) := by rw [Real.log_pow]; norm_num
  have hlogNonneg : 0 ≤ Real.log (960 * (s : ℝ) / (d : ℝ)) :=
    (Real.log_pos hratioOne).le
  have hsq :
      Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2 ≤
        (3 * Real.log (N : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hlogNonneg hlogUpper 2
  have hden :
      1024 * Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2 ≤
        9216 * Real.log (N : ℝ) ^ 2 := by
    nlinarith
  calc
    (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2) ≤
        (s : ℝ) /
          (1024 * Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2) :=
      div_le_div_of_nonneg_left (Nat.cast_nonneg s)
        (mul_pos (by norm_num) (sq_pos_of_pos hlogRatio)) hden
    _ = ((1 / 1024 : ℝ) /
          Real.log (960 * (s : ℝ) / (d : ℝ)) ^ 2) * (s : ℝ) := by
      ring

noncomputable def lm43GrowthDenominator (N : ℕ) : ℕ :=
  ⌈9216 * Real.log (N : ℝ) ^ 2⌉₊

noncomputable def lm43GrowthDivisor (N : ℕ) : ℕ :=
  2 * lm43GrowthDenominator N

noncomputable def lm43GrowthGain (N s : ℕ) : ℕ :=
  s / lm43GrowthDivisor N

noncomputable def lm43GrowthCurve (N D : ℕ) : ℕ → ℕ
  | 0 => D
  | i + 1 => lm43GrowthCurve N D i + lm43GrowthGain N (lm43GrowthCurve N D i)

theorem lm43GrowthDenominator_pos {N : ℕ} (hN : 2 ≤ N) :
    0 < lm43GrowthDenominator N := by
  apply Nat.ceil_pos.mpr
  exact mul_pos (by norm_num) (sq_pos_of_pos <|
    Real.log_pos (by exact_mod_cast (by omega : 1 < N)))

theorem lm43GrowthGain_mono (N : ℕ) : Monotone (lm43GrowthGain N) := by
  intro a b hab
  exact Nat.div_le_div_right hab

@[simp] theorem lm43GrowthCurve_zero (N D : ℕ) :
    lm43GrowthCurve N D 0 = D := rfl

@[simp] theorem lm43GrowthCurve_succ (N D i : ℕ) :
    lm43GrowthCurve N D (i + 1) =
      lm43GrowthCurve N D i + lm43GrowthGain N (lm43GrowthCurve N D i) := rfl

theorem lm43GrowthCurve_mono (N D : ℕ) : Monotone (lm43GrowthCurve N D) := by
  apply monotone_nat_of_le_succ
  intro i
  rw [lm43GrowthCurve_succ]
  exact Nat.le_add_right _ _

theorem lm43GrowthCurve_start_le (N D i : ℕ) :
    D ≤ lm43GrowthCurve N D i := by
  simpa using lm43GrowthCurve_mono N D (Nat.zero_le i)

theorem lm43GrowthCurve_add_mul_gain_le (N D i t : ℕ) :
    lm43GrowthCurve N D i + t * lm43GrowthGain N (lm43GrowthCurve N D i) ≤
      lm43GrowthCurve N D (i + t) := by
  induction t with
  | zero => simp
  | succ t ih =>
      have hmono : lm43GrowthCurve N D i ≤ lm43GrowthCurve N D (i + t) :=
        lm43GrowthCurve_mono N D (Nat.le_add_right i t)
      have hgain := lm43GrowthGain_mono N hmono
      calc
        lm43GrowthCurve N D i + (t + 1) * lm43GrowthGain N (lm43GrowthCurve N D i)
            = (lm43GrowthCurve N D i +
                t * lm43GrowthGain N (lm43GrowthCurve N D i)) +
              lm43GrowthGain N (lm43GrowthCurve N D i) := by ring
        _ ≤ lm43GrowthCurve N D (i + t) +
              lm43GrowthGain N (lm43GrowthCurve N D (i + t)) :=
            Nat.add_le_add ih hgain
        _ = lm43GrowthCurve N D (i + (t + 1)) := by
          rw [show i + (t + 1) = (i + t) + 1 by omega,
            lm43GrowthCurve_succ]

theorem two_lm43GrowthGain_le_expansion
    {N d s : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (s : ℝ)) (hsN : s ≤ N) :
    (((2 * lm43GrowthGain N s : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hCpos := lm43GrowthDenominator_pos (hN.trans' (by omega))
  have hnat : 2 * lm43GrowthGain N s ≤ s / lm43GrowthDenominator N := by
    apply (Nat.le_div_iff_mul_le hCpos).2
    rw [lm43GrowthGain, lm43GrowthDivisor]
    simpa [mul_assoc, mul_comm, mul_left_comm] using
      Nat.div_mul_le_self s (2 * lm43GrowthDenominator N)
  have hcastDiv : ((s / lm43GrowthDenominator N : ℕ) : ℝ) ≤
      (s : ℝ) / (lm43GrowthDenominator N : ℝ) := by
    simpa using (Nat.cast_div_le (α := ℝ)
      (m := s) (n := lm43GrowthDenominator N))
  have hlogpos : 0 < Real.log (N : ℝ) :=
    Real.log_pos (by exact_mod_cast (by omega : 1 < N))
  have hdenpos : (0 : ℝ) < 9216 * Real.log (N : ℝ) ^ 2 := by positivity
  have hden : 9216 * Real.log (N : ℝ) ^ 2 ≤
      (lm43GrowthDenominator N : ℝ) := Nat.le_ceil _
  have hquotient :
      (s : ℝ) / (lm43GrowthDenominator N : ℝ) ≤
        (s : ℝ) / (9216 * Real.log (N : ℝ) ^ 2) :=
    div_le_div_of_nonneg_left (Nat.cast_nonneg s) hdenpos hden
  have hnatReal : ((2 * lm43GrowthGain N s : ℕ) : ℝ) ≤
      ((s / lm43GrowthDenominator N : ℕ) : ℝ) := by
    exact_mod_cast hnat
  exact hnatReal.trans hcastDiv |>.trans hquotient |>.trans
    (lm43_expansion_profile_lower hN hd hcutoff hsN)

noncomputable def concreteLM43BallGrowthScheduleOfTarget
    [Fintype V] (G : SimpleGraph V) (d D workspace radius : ℕ)
    (hN : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (D : ℝ))
    (hworkspace : workspace ≤ lm43GrowthGain (Fintype.card V) D)
    (htarget : Fintype.card V / 2 + 1 ≤
      lm43GrowthCurve (Fintype.card V) D radius) :
    BallGrowthSchedule G (1 / 1024) ((1 / 64) * (d : ℝ)) D workspace radius where
  size := lm43GrowthCurve (Fintype.card V) D
  initial := by simp
  lower := by
    intro i _
    have hDi := lm43GrowthCurve_start_le (Fintype.card V) D i
    have hDreal : (D : ℝ) ≤
        (lm43GrowthCurve (Fintype.card V) D i : ℝ) := by exact_mod_cast hDi
    calc
      ((1 / 64 : ℝ) * (d : ℝ)) / 2 = (d : ℝ) / 128 := by ring
      _ ≤ (D : ℝ) := hcutoff
      _ ≤ _ := hDreal
  target := htarget
  step := by
    intro i _ s his hsNhalf
    let N := Fintype.card V
    change lm43GrowthCurve N D i ≤ s at his
    have hDs : D ≤ s := (lm43GrowthCurve_start_le N D i).trans his
    have hcutoffS : (d : ℝ) / 128 ≤ (s : ℝ) :=
      hcutoff.trans (by exact_mod_cast hDs)
    have hnext : lm43GrowthCurve N D (i + 1) - s ≤ lm43GrowthGain N s := by
      rw [lm43GrowthCurve_succ]
      have hgain := lm43GrowthGain_mono N his
      have hsub : lm43GrowthCurve N D i + lm43GrowthGain N (lm43GrowthCurve N D i) - s ≤
          lm43GrowthGain N (lm43GrowthCurve N D i) := by omega
      exact hsub.trans hgain
    have hgainD : lm43GrowthGain N D ≤ lm43GrowthGain N s :=
      lm43GrowthGain_mono N hDs
    have hnat : workspace + (lm43GrowthCurve N D (i + 1) - s) ≤
        2 * lm43GrowthGain N s := by
      calc
        workspace + (lm43GrowthCurve N D (i + 1) - s) ≤
            lm43GrowthGain N s + lm43GrowthGain N s :=
          Nat.add_le_add (hworkspace.trans hgainD) hnext
        _ = 2 * lm43GrowthGain N s := by omega
    have hnatReal :
        ((workspace + (lm43GrowthCurve N D (i + 1) - s) : ℕ) : ℝ) ≤
          ((2 * lm43GrowthGain N s : ℕ) : ℝ) := by exact_mod_cast hnat
    exact hnatReal.trans <|
      two_lm43GrowthGain_le_expansion hN hd hcutoffS
        (hsNhalf.trans (Nat.div_le_self N 2))

def lm43K (n : ℕ) : ℕ := n / 4

noncomputable def lm43FreshRadius (n : ℕ) : ℕ :=
  3 * lm43GrowthDenominator n

def lm43HalvingRounds (n : ℕ) : ℕ := Nat.log 2 (lm43K n) + 1

noncomputable def lm43FarRadius (n : ℕ) : ℕ :=
  lm43FreshRadius n * lm43HalvingRounds n

def lm43HalvingCenters (n i : ℕ) : ℕ :=
  2 ^ (lm43HalvingRounds n - i)

noncomputable def concreteLM43HalvingSchedule (n : ℕ) :
    HalvingSchedule (lm43K n) (lm43HalvingRounds n) where
  centers := lm43HalvingCenters n
  zero := by
    have hlt : lm43K n < 2 ^ (Nat.log 2 (lm43K n) + 1) :=
      Nat.lt_pow_succ_log_self (by omega : 1 < 2) (lm43K n)
    simpa [lm43HalvingCenters, lm43HalvingRounds] using hlt.le
  step := by
    intro i hi
    let q := lm43HalvingRounds n - (i + 1)
    have hexp : lm43HalvingRounds n - i = q + 1 := by
      dsimp [q]
      omega
    have hnext : lm43HalvingRounds n - (i + 1) = q := rfl
    simp only [lm43HalvingCenters, hexp, hnext, pow_succ]
    omega
  last := by simp [lm43HalvingCenters]

theorem lm43K_target {n : ℕ} (hn : 32 ≤ n)
    (hlarge : 6 * lm43GrowthDenominator n ≤ lm43K n) :
    n / 2 + 1 ≤ lm43GrowthCurve n (lm43K n) (lm43FreshRadius n) := by
  let C := lm43GrowthDenominator n
  let K := lm43K n
  have hCpos : 0 < C := lm43GrowthDenominator_pos (hn.trans' (by omega))
  have htwoCpos : 0 < 2 * C := by omega
  have hq : 3 ≤ K / (2 * C) := by
    apply (Nat.le_div_iff_mul_le htwoCpos).2
    dsimp [K, C] at *
    omega
  have hmodK := Nat.mod_lt K htwoCpos
  have hdecompK := Nat.div_add_mod K (2 * C)
  have hmodSucc : K % (2 * C) + 1 ≤ 2 * C := by omega
  have htwoCSucc : 2 * C + 1 ≤ 3 * C := by omega
  have hremainder : K % (2 * C) + 2 ≤ (K / (2 * C)) * C := by
    calc
      K % (2 * C) + 2 = (K % (2 * C) + 1) + 1 := by omega
      _ ≤ 2 * C + 1 := Nat.add_le_add_right hmodSucc 1
      _ ≤ 3 * C := htwoCSucc
      _ ≤ (K / (2 * C)) * C := Nat.mul_le_mul_right C hq
  have hdecompK' :
      (K / (2 * C)) * (2 * C) + K % (2 * C) = K := by
    simpa [Nat.mul_comm] using hdecompK
  have hKplus :
      K + 2 ≤ (K / (2 * C)) * (2 * C) + (K / (2 * C)) * C := by
    calc
      K + 2 = (K / (2 * C)) * (2 * C) + (K % (2 * C) + 2) := by
        omega
      _ ≤ (K / (2 * C)) * (2 * C) + (K / (2 * C)) * C :=
        Nat.add_le_add_left hremainder _
  have hseedGain : 2 * K + 2 ≤ K + (3 * C) * (K / (2 * C)) := by
    calc
      2 * K + 2 = K + (K + 2) := by omega
      _ ≤ K + ((K / (2 * C)) * (2 * C) + (K / (2 * C)) * C) :=
        Nat.add_le_add_left hKplus _
      _ = K + (3 * C) * (K / (2 * C)) := by ring
  have hmodN := Nat.mod_lt n (by omega : 0 < 4)
  have hdecompN := Nat.div_add_mod n 4
  have hhalf : n / 2 + 1 ≤ 2 * K + 2 := by
    dsimp [K, lm43K]
    omega
  have hiter := lm43GrowthCurve_add_mul_gain_le n K 0 (3 * C)
  have hgain : lm43GrowthGain n K = K / (2 * C) := by
    simp [lm43GrowthGain, lm43GrowthDivisor, C]
  have hcurve : K + (3 * C) * (K / (2 * C)) ≤
      lm43GrowthCurve n K (3 * C) := by
    simpa only [lm43GrowthCurve_zero, zero_add, hgain] using hiter
  calc
    n / 2 + 1 ≤ 2 * K + 2 := hhalf
    _ ≤ K + (3 * C) * (K / (2 * C)) := hseedGain
    _ ≤ lm43GrowthCurve n K (3 * C) := hcurve
    _ = lm43GrowthCurve n (lm43K n) (lm43FreshRadius n) := by
      simp only [K, C, lm43FreshRadius]

theorem exists_lm43_auxiliary_expansion [Fintype V]
    (G : SimpleGraph V) (d workspace L : ℕ)
    (hexp : IsLMExpander G (1 / 1024) ((1 / 64) * (d : ℝ)))
    (W : Finset V)
    (hn : 32 ≤ Fintype.card V) (hd : 1 ≤ d)
    (hdn : d ≤ Fintype.card V)
    (hW : W.card ≤ workspace)
    (hworkspace : workspace ≤
      lm43GrowthGain (Fintype.card V) (lm43K (Fintype.card V)))
    (hroom : workspace + lm43K (Fintype.card V) ≤ Fintype.card V)
    (hLpos : 0 < L) (hLK : L ≤ lm43K (Fintype.card V))
    (hlarge : 6 * lm43GrowthDenominator (Fintype.card V) ≤
      lm43K (Fintype.card V)) :
    ∃ root : V, ∃ E : VertexExpansion G root L
        (lm43FarRadius (Fintype.card V)),
      Disjoint E.verts W := by
  let n := Fintype.card V
  let K := lm43K n
  have hKpos : 0 < K := by dsimp [K, lm43K]; omega
  have hnK : n ≤ 8 * K := by
    have hmod := Nat.mod_lt n (by omega : 0 < 4)
    have hdecomp := Nat.div_add_mod n 4
    dsimp [K, lm43K]
    omega
  have hdK : d ≤ 128 * K := hdn.trans (hnK.trans (by omega))
  have hcutoff : (d : ℝ) / 128 ≤ (K : ℝ) := by
    have hdKreal : (d : ℝ) ≤ 128 * (K : ℝ) := by exact_mod_cast hdK
    linarith
  let growth : BallGrowthSchedule G (1 / 1024) ((1 / 64) * (d : ℝ))
      K workspace (lm43FreshRadius n) :=
    concreteLM43BallGrowthScheduleOfTarget G d K workspace (lm43FreshRadius n)
      hn hd hcutoff hworkspace (lm43K_target hn hlarge)
  have hhalve : 2 * K ≤ n / 2 + 1 := by
    dsimp [K, lm43K]
    omega
  simpa only [n, K, lm43FarRadius] using
    (liuMontgomery_lemma3_12_finite G (1 / 1024)
      ((1 / 64) * (d : ℝ)) hexp W workspace K L
      (lm43FreshRadius n) (lm43HalvingRounds n)
      (lm43FarRadius n) (concreteLM43HalvingSchedule n) growth hW hroom
      hKpos hLpos hLK hhalve (by simp [lm43FarRadius]))

end Erdos63
