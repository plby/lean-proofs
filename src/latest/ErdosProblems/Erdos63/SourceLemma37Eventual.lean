/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.Claim44Eventual
import ErdosProblems.Erdos63.SourceLemma37Geometry

/-!
# Eventual source numerics for Liu--Montgomery Lemma 3.7

This file supplies the eventual arithmetic for the finite constructor in
`SourceLemma37Numerics`.  The degree statement is deliberately conditional
on `lm37SourceMinSize d < M`: without this radius-one guard the literal
`D^2` large sample cannot reach the expander cutoff uniformly for all
`d ≤ N`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## The exact small-label sum -/

/-- The algebraic label bound in `LM37SourceNumericalBounds` is controlled
by the same envelope as the actual bounded-subset count from Lemma 3.5. -/
theorem lm37_smallSample_cast_le_sampleEnvelope
    {N d Ucap degreeIntoU : ℕ}
    (hdegree : degreeIntoU ≤ d)
    (hU : Ucap ≤ SourceLemma35Numerics.deletionCap N) :
    ((∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
        r * ((((r * degreeIntoU) + 1) *
          (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) : ℕ) : ℝ) ≤
      SourceLemma35Numerics.sampleEnvelope N := by
  let Cmax : ℕ := 2048 * SourceLemma35Numerics.cutoff N ^ 2
  let A : ℝ := Real.log (Real.log (N : ℝ)) ^ 2
  let term : ℝ := (SourceLemma35Numerics.cutoff N : ℝ) ^ 3 *
    (Cmax + 1 : ℕ) * Real.exp ((Cmax : ℝ) * A)
  have hA : 0 ≤ A := by dsimp [A]; positivity
  have hcap : (SourceLemma35Numerics.deletionCap N : ℝ) ≤ Real.exp A := by
    simpa [A] using SourceLemma35Numerics.deletionCap_cast_le N
  have hUreal : (Ucap : ℝ) ≤ Real.exp A := by
    exact (by exact_mod_cast hU : (Ucap : ℝ) ≤
      SourceLemma35Numerics.deletionCap N) |>.trans hcap
  have honeExp : (1 : ℝ) ≤ Real.exp A := by
    simpa [Real.one_le_exp_iff] using hA
  have hbase : ((max 1 Ucap : ℕ) : ℝ) ≤ Real.exp A := by
    simp only [Nat.cast_max, Nat.cast_one]
    exact max_le honeExp hUreal
  have hterm : ∀ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
      ((r * ((((r * degreeIntoU) + 1) *
        (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) : ℕ) : ℝ) ≤ term := by
    intro r hr
    have hrmin : SourceLemma35Numerics.minFailedSize d ≤ r := by
      simpa [lm37SourceMinSize] using (Finset.mem_Ico.1 hr).1
    have hrcut : r < SourceLemma35Numerics.cutoff N := by
      simpa [lm37SourceCutoff] using (Finset.mem_Ico.1 hr).2
    have hrle : r ≤ SourceLemma35Numerics.cutoff N := Nat.le_of_lt hrcut
    have hCsource : r * d ≤ Cmax := by
      simpa [Cmax, SourceLemma35Numerics.blockedBudget] using
        SourceLemma35Numerics.blockedBudget_le_of_small_range hrmin hrcut
    have hC : r * degreeIntoU ≤ Cmax :=
      (Nat.mul_le_mul_left r hdegree).trans hCsource
    have hpowBase : (((max 1 Ucap : ℕ) : ℝ) ^ (r * degreeIntoU)) ≤
        (Real.exp A) ^ (r * degreeIntoU) := by
      exact pow_le_pow_left₀ (by positivity) hbase _
    have hpowExponent : (Real.exp A) ^ (r * degreeIntoU) ≤
        (Real.exp A) ^ Cmax := pow_le_pow_right₀ honeExp hC
    have hpowExp : (Real.exp A) ^ Cmax =
        Real.exp ((Cmax : ℝ) * A) := by
      rw [← Real.exp_nat_mul]
    dsimp [term]
    push_cast
    calc
      (r : ℝ) * ((((r : ℝ) * degreeIntoU + 1) *
          max (1 : ℝ) Ucap ^ (r * degreeIntoU)) * (r : ℝ) ^ 2)
          = (r : ℝ) ^ 3 * (((r : ℝ) * degreeIntoU + 1) *
            max (1 : ℝ) Ucap ^ (r * degreeIntoU)) := by ring
      _ ≤ (SourceLemma35Numerics.cutoff N : ℝ) ^ 3 *
          (((Cmax : ℝ) + 1) * Real.exp ((Cmax : ℝ) * A)) := by
        gcongr
        · exact_mod_cast hC
        · simpa only [Nat.cast_max, Nat.cast_one] using
            hpowBase.trans (hpowExponent.trans_eq hpowExp)
      _ = (SourceLemma35Numerics.cutoff N : ℝ) ^ 3 *
          ((Cmax : ℝ) + 1) * Real.exp ((Cmax : ℝ) * A) := by ring
  have hcard : (Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N)).card ≤
      SourceLemma35Numerics.cutoff N := by
    simp [lm37SourceCutoff]
  calc
    ((∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
        r * ((((r * degreeIntoU) + 1) *
          (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) : ℕ) : ℝ)
        = ∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
            ((r * ((((r * degreeIntoU) + 1) *
              (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) : ℕ) : ℝ) := by
          push_cast
          rfl
    _ ≤ ∑ _r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
        term := Finset.sum_le_sum fun r hr ↦ hterm r hr
    _ = ((Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N)).card : ℝ) *
        term := by simp
    _ ≤ (SourceLemma35Numerics.cutoff N : ℝ) * term := by
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hcard) (by positivity)
    _ = SourceLemma35Numerics.sampleEnvelope N := by
      simp only [SourceLemma35Numerics.sampleEnvelope, term, Cmax, A]
      push_cast
      ring

private theorem nat_le_index_half_of_four_mul_cast_le
    {N x : ℕ}
    (hroot : 2 ≤ (N : ℝ) ^ ((1 : ℝ) / 8))
    (hx : ((4 * x : ℕ) : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 8)) :
    x ≤ (SourceLemma35Numerics.indexCard N + 1) / 2 := by
  have hfloor : (N : ℝ) ^ ((1 : ℝ) / 8) / 2 ≤
      (SourceLemma35Numerics.indexCard N : ℝ) := by
    simpa [SourceLemma35Numerics.indexCard] using Parameters.half_le_natFloor hroot
  have htwoReal : ((2 * x : ℕ) : ℝ) ≤
      (SourceLemma35Numerics.indexCard N : ℝ) := by
    calc
      ((2 * x : ℕ) : ℝ) = ((4 * x : ℕ) : ℝ) / 2 := by
        push_cast
        ring
      _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) / 2 := by gcongr
      _ ≤ (SourceLemma35Numerics.indexCard N : ℝ) := hfloor
  have htwo : 2 * x ≤ SourceLemma35Numerics.indexCard N := by
    exact_mod_cast htwoReal
  apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
  omega

/-- Eventual exact small-sample field, uniform in `d` and in every
`degreeIntoU ≤ d`. -/
theorem eventually_lm37_small_sample :
    ∀ᶠ N : ℕ in atTop, ∀ d Ucap degreeIntoU : ℕ,
      degreeIntoU ≤ d → Ucap ≤ SourceLemma35Numerics.deletionCap N →
      ∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
        r * ((((r * degreeIntoU) + 1) *
          (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) ≤
        (SourceLemma35Numerics.indexCard N + 1) / 2 := by
  filter_upwards [SourceLemma35Numerics.eventually_source_ambient_bounds] with N hN
  intro d Ucap degreeIntoU hdegree hU
  let S : ℕ := ∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
    r * ((((r * degreeIntoU) + 1) *
      (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2)
  have hS : (S : ℝ) ≤ SourceLemma35Numerics.sampleEnvelope N := by
    simpa [S] using lm37_smallSample_cast_le_sampleEnvelope hdegree hU
  apply nat_le_index_half_of_four_mul_cast_le hN.2.1
  calc
    ((4 * S : ℕ) : ℝ) = 4 * (S : ℝ) := by norm_num
    _ ≤ 4 * SourceLemma35Numerics.sampleEnvelope N := by
      gcongr
    _ ≤ (N : ℝ) ^ ((1 : ℝ) / 8) := hN.2.2


/-! ## The source deletion envelope dominates every fixed polylogarithm -/

/-- The quasi-polylogarithmic source deletion cap eventually dominates any
fixed multiple of any fixed power of `log N`. -/
theorem eventually_const_mul_log_pow_le_sourceDeletionCap
    (C : ℝ) (hC : 0 < C) (k : ℕ) :
    ∀ᶠ N : ℕ in atTop,
      C * Real.log (N : ℝ) ^ k ≤
        (SourceLemma35Numerics.deletionCap N : ℝ) := by
  have hL : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hll : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp hL
  filter_upwards
      [hL.eventually (eventually_ge_atTop (2 * C)),
       hll.eventually (eventually_ge_atTop ((k + 1 : ℕ) : ℝ))]
      with N hLC hllarge
  let L := Real.log (N : ℝ)
  let ll := Real.log L
  have hLpos : 0 < L := lt_of_lt_of_le (mul_pos (by norm_num) hC) hLC
  have hllone : 1 ≤ ll := by
    dsimp [ll]
    exact (by exact_mod_cast (Nat.le_add_left 1 k) :
      (1 : ℝ) ≤ ((k + 1 : ℕ) : ℝ)) |>.trans hllarge
  have hexpTwo : 2 ≤ Real.exp (ll ^ 2) := by
    apply le_of_lt
    calc
      (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      _ ≤ Real.exp (ll ^ 2) := Real.exp_le_exp.mpr (by nlinarith)
  have hhalf : Real.exp (ll ^ 2) / 2 ≤
      (SourceLemma35Numerics.deletionCap N : ℝ) := by
    simpa [SourceLemma35Numerics.deletionCap, ll, L] using
      Parameters.half_le_natFloor hexpTwo
  apply (show C * L ^ k ≤
      (SourceLemma35Numerics.deletionCap N : ℝ) from ?_)
  refine (show C * L ^ k ≤ Real.exp (ll ^ 2) / 2 from ?_).trans hhalf
  rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
  calc
    C * L ^ k * 2 = (2 * C) * L ^ k := by ring
    _ ≤ L * L ^ k := by
      exact mul_le_mul_of_nonneg_right hLC (pow_nonneg hLpos.le k)
    _ = L ^ (k + 1) := by simp [pow_succ, mul_comm]
    _ = Real.exp ((((k + 1 : ℕ) : ℝ) * ll)) := by
      calc
        L ^ (k + 1) = (Real.exp ll) ^ (k + 1) := by
          rw [Real.exp_log]
          simpa only [ll] using hLpos
        _ = Real.exp (((k + 1 : ℕ) * ll)) := by
          rw [Real.exp_nat_mul]
    _ ≤ Real.exp (ll ^ 2) := by
      apply Real.exp_le_exp.mpr
      have hllnonneg : 0 ≤ ll := zero_le_one.trans hllone
      simpa [pow_two] using mul_le_mul_of_nonneg_right hllarge hllnonneg

/-! ## Canonical robust envelopes -/

/-- The two robust targets have harmless fixed polylogarithmic envelopes.
The deliberately coarse exponent `42` lets us use the already available
bound `maxRadius ≤ targetOrder`. -/
theorem eventually_lm43_target_envelopes :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      (lm43TargetOrder N d : ℝ) ≤ 2 * Real.log (N : ℝ) ^ 14 ∧
      (lm43BallTarget N d : ℝ) ≤ 80 * Real.log (N : ℝ) ^ 42 := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Parameters.eventually_lmExpansionOrder_mul_lmRadius_1024_le_ceil_log14,
       hlog.eventually (eventually_ge_atTop (1 : ℝ)),
       eventually_ge_atTop (32 : ℕ)] with N htarget hL hN
  intro d
  let L := Real.log (N : ℝ)
  let M := lm43TargetOrder N d
  let m := lm43MaxRadius N d
  have hceil : (⌈L ^ 14⌉₊ : ℝ) ≤ 2 * L ^ 14 := by
    apply le_of_lt
    calc
      (⌈L ^ 14⌉₊ : ℝ) < L ^ 14 + 1 :=
        Nat.ceil_lt_add_one (pow_nonneg (zero_le_one.trans hL) 14)
      _ ≤ 2 * L ^ 14 := by
        have : 1 ≤ L ^ 14 := one_le_pow₀ hL
        linarith
  have hMnat : M ≤ ⌈L ^ 14⌉₊ := by
    simpa only [M, lm43TargetOrder, lm47InflatedOrder, L] using htarget
  have hM : (M : ℝ) ≤ 2 * L ^ 14 :=
    (by exact_mod_cast hMnat : (M : ℝ) ≤ (⌈L ^ 14⌉₊ : ℝ)).trans hceil
  have hm : m ≤ M := by
    simpa only [m, M] using lm43MaxRadius_le_targetOrder (d := d) hN
  have hballNat : lm43BallTarget N d ≤ 10 * M ^ 3 := by
    have hmSq : m ^ 2 ≤ M ^ 2 := Nat.pow_le_pow_left hm 2
    dsimp [lm43BallTarget, m, M]
    nlinarith
  constructor
  · simpa only [M, L] using hM
  · calc
      (lm43BallTarget N d : ℝ) ≤ (10 * M ^ 3 : ℕ) := by
        exact_mod_cast hballNat
      _ ≤ 10 * (2 * L ^ 14) ^ 3 := by
        push_cast
        gcongr
      _ = 80 * Real.log (N : ℝ) ^ 42 := by
        dsimp [L]
        ring

/-- Eventually the source envelope contains every robust slow size, and the
robust deleted set is strictly smaller than that envelope. -/
theorem eventually_lm43_maxSlowSize_eq_sourceDeletionCap :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43MaxSlowSize N d = SourceLemma35Numerics.deletionCap N ∧
      lm43DeletionCap N d < SourceLemma35Numerics.deletionCap N := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [eventually_lm43_target_envelopes,
       eventually_const_mul_log_pow_le_sourceDeletionCap 81 (by norm_num) 42,
       eventually_const_mul_log_pow_le_sourceDeletionCap 3 (by norm_num) 1,
       SourceLemma35Numerics.eventually_cutoff_cast_le_two_rpow,
       hlog.eventually (eventually_ge_atTop (1 : ℝ))]
      with N htargets hcapBall hcapCut hcut hL
  intro d
  let L := Real.log (N : ℝ)
  let cap := SourceLemma35Numerics.deletionCap N
  have hL' : 1 ≤ L := by simpa only [L] using hL
  have htargetCap : lm43TargetOrder N d ≤ cap := by
    have hreal : (lm43TargetOrder N d : ℝ) ≤ (cap : ℝ) :=
      (htargets d).1.trans <| by
        calc
          2 * L ^ 14 ≤ 81 * L ^ 42 := by
            have hpow : L ^ 14 ≤ L ^ 42 := pow_le_pow_right₀ hL' (by omega)
            nlinarith [pow_nonneg (zero_le_one.trans hL') 42]
          _ ≤ (cap : ℝ) := by simpa [L, cap] using hcapBall
    exact_mod_cast hreal
  have hballCap : lm43BallTarget N d ≤ cap := by
    have hreal : (lm43BallTarget N d : ℝ) ≤ (cap : ℝ) :=
      (htargets d).2.trans <| by
        calc
          80 * L ^ 42 ≤ 81 * L ^ 42 := by
            nlinarith [pow_nonneg (zero_le_one.trans hL') 42]
          _ ≤ (cap : ℝ) := by simpa [L, cap] using hcapBall
    exact_mod_cast hreal
  have hcutCap : SourceLemma35Numerics.cutoff N ≤ cap := by
    have hrpow : L ^ ((1 : ℝ) / 10) ≤ L :=
      Real.rpow_le_self_of_one_le hL' (by norm_num)
    have hreal : (SourceLemma35Numerics.cutoff N : ℝ) ≤ (cap : ℝ) :=
      hcut.trans <| by
        calc
          2 * L ^ ((1 : ℝ) / 10) ≤ 2 * L := by gcongr
          _ ≤ 3 * L := by nlinarith
          _ ≤ (cap : ℝ) := by simpa [L, cap] using hcapCut
    exact_mod_cast hreal
  have hUstrict : lm43DeletionCap N d < cap := by
    rw [lm43DeletionCap_eq]
    have hUreal : ((6 * lm43TargetOrder N d : ℕ) : ℝ) < (cap : ℝ) := by
      push_cast
      calc
        (6 : ℝ) * lm43TargetOrder N d ≤ 12 * L ^ 14 := by
          have := (htargets d).1
          nlinarith
        _ < 81 * L ^ 42 := by
          have hpow : L ^ 14 ≤ L ^ 42 := pow_le_pow_right₀ hL' (by omega)
          have hpos : 0 < L ^ 42 := pow_pos (zero_lt_one.trans_le hL') 42
          nlinarith
        _ ≤ (cap : ℝ) := by simpa [L, cap] using hcapBall
    exact_mod_cast hUreal
  constructor
  · simp only [lm43MaxSlowSize]
    exact max_eq_left (max_le hcutCap (max_le htargetCap hballCap))
  · exact hUstrict

/-- The final (and hence also the smaller intermediate) robust target lies
below the literal first-slow curve at the source clock `(log log N)^20`. -/
theorem eventually_lm43_ballTarget_le_firstSlowGrowth :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43BallTarget N d ≤ lm37FirstSlowGrowth (lm43AvoidingRadius N) := by
  have hll : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  have hquarter : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ)) ^ ((1 : ℝ) / 4))
      atTop atTop :=
    (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 4)).comp hll
  filter_upwards
      [eventually_lm43_target_envelopes,
       hll.eventually (eventually_ge_atTop (160 : ℝ)),
       hquarter.eventually (eventually_ge_atTop (43 : ℝ)),
       eventually_ge_atTop (3 : ℕ)]
      with N htargets ha hquarterLarge hN
  intro d
  let L := Real.log (N : ℝ)
  let a := Real.log L
  let radius := lm43AvoidingRadius N
  have hapos : 0 < a := by dsimp [a]; linarith
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hceil : a ^ 20 ≤ (radius : ℝ) := by
    simpa only [radius, lm43AvoidingRadius, a, L] using
      (Nat.le_ceil (R := ℝ) (a ^ 20))
  have hrpow : a ^ ((5 : ℝ) / 4) ≤
      (radius : ℝ) ^ ((1 : ℝ) / 16) := by
    calc
      a ^ ((5 : ℝ) / 4) =
          (a ^ (20 : ℕ)) ^ ((1 : ℝ) / 16) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul hapos.le]
        norm_num
      _ ≤ (radius : ℝ) ^ ((1 : ℝ) / 16) :=
        Real.rpow_le_rpow (pow_nonneg hapos.le 20) hceil (by norm_num)
  have hfortythree : 43 * a ≤ a ^ ((5 : ℝ) / 4) := by
    calc
      43 * a ≤ a ^ ((1 : ℝ) / 4) * a := by
        have : 43 ≤ a ^ ((1 : ℝ) / 4) := by
          simpa only [a, L] using hquarterLarge
        exact mul_le_mul_of_nonneg_right this hapos.le
      _ = a ^ ((5 : ℝ) / 4) := by
        calc
          a ^ ((1 : ℝ) / 4) * a =
              a ^ ((1 : ℝ) / 4) * a ^ (1 : ℝ) := by
                rw [Real.rpow_one]
          _ = a ^ ((1 : ℝ) / 4 + 1) := by
            exact (Real.rpow_add hapos _ _).symm
          _ = a ^ ((5 : ℝ) / 4) := by norm_num
  have h160 : (160 : ℝ) ≤ Real.exp a := by
    apply le_of_lt
    calc
      (160 : ℝ) < a + 1 := by linarith
      _ < Real.exp a := Real.add_one_lt_exp (ne_of_gt hapos)
  have hpolyExp : 160 * L ^ 42 ≤
      Real.exp (a ^ ((5 : ℝ) / 4)) := by
    calc
      160 * L ^ 42 ≤ Real.exp a * L ^ 42 := by
        exact mul_le_mul_of_nonneg_right h160 (pow_nonneg hLpos.le 42)
      _ = Real.exp a * Real.exp (42 * a) := by
        congr 1
        calc
          L ^ 42 = (Real.exp a) ^ 42 := by
            rw [Real.exp_log]
            simpa only [a] using hLpos
          _ = Real.exp (42 * a) := by
            simpa only [Nat.cast_ofNat] using (Real.exp_nat_mul a 42).symm
      _ = Real.exp (43 * a) := by rw [← Real.exp_add]; congr 1; ring
      _ ≤ Real.exp (a ^ ((5 : ℝ) / 4)) := Real.exp_le_exp.mpr hfortythree
  have hexpTwo : 2 ≤
      Real.exp ((radius : ℝ) ^ ((1 : ℝ) / 16)) := by
    apply le_of_lt
    calc
      (2 : ℝ) < Real.exp 1 := Real.exp_one_gt_two
      _ ≤ Real.exp ((radius : ℝ) ^ ((1 : ℝ) / 16)) := by
        apply Real.exp_le_exp.mpr
        have : (1 : ℝ) ≤ 43 * a := by nlinarith
        exact this.trans (hfortythree.trans hrpow)
  have hhalf : Real.exp ((radius : ℝ) ^ ((1 : ℝ) / 16)) / 2 ≤
      (lm37FirstSlowGrowth radius : ℝ) := by
    simpa only [lm37FirstSlowGrowth] using Parameters.half_le_natFloor hexpTwo
  have hreal : (lm43BallTarget N d : ℝ) ≤
      (lm37FirstSlowGrowth radius : ℝ) := by
    refine (htargets d |>.2).trans ((show
      80 * L ^ 42 ≤
        Real.exp ((radius : ℝ) ^ ((1 : ℝ) / 16)) / 2 by
      rw [le_div_iff₀ (by norm_num : (0 : ℝ) < 2)]
      calc
        80 * L ^ 42 * 2 = 160 * L ^ 42 := by ring
        _ ≤ Real.exp (a ^ ((5 : ℝ) / 4)) := hpolyExp
        _ ≤ Real.exp ((radius : ℝ) ^ ((1 : ℝ) / 16)) :=
          Real.exp_le_exp.mpr hrpow) |>.trans hhalf)
  exact_mod_cast hreal

/-! ## The common large sample -/

/-- Three copies of the source deletion exponent are still negligible
compared with the eighth-root index. -/
theorem eventually_four_sourceDeletionCap_cube_le_indexRoot :
    ∀ᶠ N : ℕ in atTop,
      (((4 * SourceLemma35Numerics.deletionCap N ^ 3 : ℕ) : ℝ)) ≤
        (N : ℝ) ^ ((1 : ℝ) / 8) := by
  have hlog : Tendsto (fun N : ℕ ↦ Real.log (N : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards
      [Parameters.eventually_const_mul_log_log_pow_le_log 64 2,
       hlog.eventually (eventually_ge_atTop (128 : ℝ)),
       eventually_ge_atTop (1 : ℕ)] with N hll hL hN
  let L := Real.log (N : ℝ)
  let a := Real.log L
  let cap := SourceLemma35Numerics.deletionCap N
  have hLpos : 0 < L := by dsimp [L]; linarith
  have hcap : (cap : ℝ) ≤ Real.exp (a ^ 2) := by
    simpa only [cap, a, L] using SourceLemma35Numerics.deletionCap_cast_le N
  have hcapCube : (cap : ℝ) ^ 3 ≤ Real.exp (3 * a ^ 2) := by
    calc
      (cap : ℝ) ^ 3 ≤ (Real.exp (a ^ 2)) ^ 3 :=
        pow_le_pow_left₀ (Nat.cast_nonneg cap) hcap 3
      _ = Real.exp (3 * a ^ 2) := by rw [← Real.exp_nat_mul]; ring_nf
  have hlogFour : Real.log 4 ≤ 5 * L / 64 := by
    rw [Real.log_four_eq]
    have := Real.log_two_lt_d9
    dsimp [L] at hL ⊢
    nlinarith
  have hfour : (4 : ℝ) ≤ Real.exp (5 * L / 64) := by
    rw [← Real.exp_log (by norm_num : (0 : ℝ) < 4)]
    exact Real.exp_le_exp.mpr hlogFour
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  push_cast
  calc
    (4 : ℝ) * (cap : ℝ) ^ 3 ≤
        Real.exp (5 * L / 64) * Real.exp (3 * a ^ 2) := by gcongr
    _ = Real.exp (5 * L / 64 + 3 * a ^ 2) := by rw [Real.exp_add]
    _ ≤ Real.exp (L / 8) := by
      apply Real.exp_le_exp.mpr
      have : 64 * a ^ 2 ≤ L := by simpa only [a, L] using hll
      nlinarith
    _ = (N : ℝ) ^ ((1 : ℝ) / 8) := by
      rw [Real.rpow_def_of_pos hNpos]
      dsimp [L]
      congr 1
      ring

/-- The robust common endpoint satisfies both large-order fields of the
finite constructor. -/
theorem eventually_lm43_large_sample_and_half :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43MaxSlowSize N d ^ 3 ≤ (lm43R N d + 1) / 2 ∧
      lm43MaxSlowSize N d ^ 3 ≤ N / 2 := by
  filter_upwards
      [eventually_lm43_maxSlowSize_eq_sourceDeletionCap,
       eventually_four_sourceDeletionCap_cube_le_indexRoot,
       SourceLemma35Numerics.eventually_source_ambient_bounds,
       eventually_ge_atTop (1 : ℕ)] with N hD hfour hambient hN
  intro d
  let cap := SourceLemma35Numerics.deletionCap N
  have hlarge : cap ^ 3 ≤ (SourceLemma35Numerics.indexCard N + 1) / 2 :=
    nat_le_index_half_of_four_mul_cast_le hambient.2.1 (by
      simpa only [cap] using hfour)
  have hrootN : (N : ℝ) ^ ((1 : ℝ) / 8) ≤ (N : ℝ) :=
    Real.rpow_le_self_of_one_le (by exact_mod_cast hN) (by norm_num)
  have hfourNat : 4 * cap ^ 3 ≤ N := by
    exact_mod_cast hfour.trans hrootN
  have hhalf : cap ^ 3 ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by omega : 0 < 2)).2
    simpa [mul_comm] using
      (Nat.mul_le_mul_right (cap ^ 3) (by omega : 2 ≤ 4)).trans hfourNat
  rw [hD d |>.1]
  constructor
  · simpa only [lm43R, lm43FamilyTarget, cap] using hlarge
  · simpa only [cap] using hhalf

/-! ## The common deletion workspace -/

/-- The actual-size small-family divisor has a uniform fourth-logarithm
envelope.  The deliberately generous common coefficient is also used by
the large-family branch below. -/
theorem eventually_lm37_smallDivisor_le_commonLogFour :
    ∀ᶠ s : ℕ in atTop,
      (lmGrowthDivisor (lm37SourceSmallBudgetOrder s) : ℝ) ≤
        3000000000 * Real.log (s : ℝ) ^ 4 := by
  filter_upwards [eventually_ge_atTop (960 : ℕ)] with s hs
  let L : ℝ := Real.log (s : ℝ)
  let B : ℕ := lm37SourceSmallBudgetOrder s
  have hspos : 0 < s := by omega
  have hB : B = 960 * s ^ 3 := by
    dsimp [B, lm37SourceSmallBudgetOrder]
    rw [max_eq_right]
    have hspow : 0 < s ^ 3 := Nat.pow_pos hspos
    nlinarith
  have hBpos : 0 < B := by rw [hB]; positivity
  have hBupper : B ≤ s ^ 4 := by
    rw [hB]
    calc
      960 * s ^ 3 ≤ s * s ^ 3 := Nat.mul_le_mul_right (s ^ 3) hs
      _ = s ^ 4 := by ring
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < s))
  have hLone : 1 ≤ L := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hthree : (3 : ℝ) ≤ s := by exact_mod_cast (by omega : 3 ≤ s)
    exact (Real.le_log_iff_exp_le (by positivity)).2 (hexp.le.trans hthree)
  have hlogB : Real.log (B : ℝ) ≤ 4 * L := by
    calc
      Real.log (B : ℝ) ≤ Real.log ((s ^ 4 : ℕ) : ℝ) :=
        Real.log_le_log (by exact_mod_cast hBpos) (by exact_mod_cast hBupper)
      _ = 4 * L := by simp [L, Real.log_pow]
  have hlogBnonneg : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by exact_mod_cast (show 1 ≤ B by omega))
  have hlogBSq : Real.log (B : ℝ) ^ 2 ≤ 16 * L ^ 2 := by
    nlinarith [sq_nonneg (Real.log (B : ℝ) - 4 * L)]
  have hceil : (lmGrowthDenominator B : ℝ) ≤ 147457 * L ^ 2 := by
    apply le_of_lt
    calc
      (lmGrowthDenominator B : ℝ) <
          9216 * Real.log (B : ℝ) ^ 2 + 1 := by
        simpa [lmGrowthDenominator] using
          Nat.ceil_lt_add_one
            (mul_nonneg (by norm_num) (sq_nonneg (Real.log (B : ℝ))))
      _ ≤ 147457 * L ^ 2 := by
        have hLsq : 1 ≤ L ^ 2 := one_le_pow₀ hLone
        nlinarith
  have hdivisor : (lmGrowthDivisor B : ℝ) ≤ 294914 * L ^ 2 := by
    calc
      (lmGrowthDivisor B : ℝ) = 2 * (lmGrowthDenominator B : ℝ) := by
        simp [lmGrowthDivisor]
      _ ≤ 2 * (147457 * L ^ 2) :=
        mul_le_mul_of_nonneg_left hceil (by norm_num)
      _ = 294914 * L ^ 2 := by ring
  calc
    (lmGrowthDivisor (lm37SourceSmallBudgetOrder s) : ℝ) =
        (lmGrowthDivisor B : ℝ) := by rfl
    _ ≤ 294914 * L ^ 2 := hdivisor
    _ ≤ 3000000000 * L ^ 4 := by
      have hLpow : L ^ 2 ≤ L ^ 4 :=
        pow_le_pow_right₀ hLone (by omega)
      nlinarith [sq_nonneg L]
    _ = 3000000000 * Real.log (s : ℝ) ^ 4 := by rfl

/-- At the canonical common endpoint, the large-family divisor has a
fourth-power `log log N` envelope. -/
theorem eventually_lm43_largeDivisor_le_logLogFour :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      (lmGrowthDivisor
          (lm37SourceLargeBudgetOrder (lm43MaxSlowSize N d)) : ℝ) ≤
        294914 * Real.log (Real.log (N : ℝ)) ^ 4 := by
  have hll : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [eventually_lm43_maxSlowSize_eq_sourceDeletionCap,
       hll.eventually (eventually_ge_atTop (32 : ℝ))]
      with N hD ha
  intro d
  let L := Real.log (N : ℝ)
  let a := Real.log L
  let cap := SourceLemma35Numerics.deletionCap N
  let B := lm37SourceLargeBudgetOrder cap
  have hapos : 0 < a := by dsimp [a]; linarith
  have hcapOne : 1 ≤ cap := by
    have hstrict : lm43DeletionCap N d < cap := by
      simpa only [cap] using (hD d).2
    omega
  have hcap : (cap : ℝ) ≤ Real.exp (a ^ 2) := by
    simpa only [cap, a, L] using SourceLemma35Numerics.deletionCap_cast_le N
  have hBnat : B ≤ 992 * cap ^ 3 := by
    dsimp [B, lm37SourceLargeBudgetOrder]
    calc
      max 32 (960 * cap ^ 3) ≤ 32 + 960 * cap ^ 3 := by
        exact max_le (by omega) (by omega)
      _ ≤ 32 * cap ^ 3 + 960 * cap ^ 3 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left 32 (one_le_pow₀ hcapOne)) _
      _ = 992 * cap ^ 3 := by ring
  have h992 : (992 : ℝ) ≤ Real.exp (a ^ 2) := by
    apply le_of_lt
    calc
      (992 : ℝ) < a ^ 2 + 1 := by nlinarith
      _ < Real.exp (a ^ 2) := Real.add_one_lt_exp (by positivity)
  have hBupper : (B : ℝ) ≤ Real.exp (4 * a ^ 2) := by
    calc
      (B : ℝ) ≤ (992 * cap ^ 3 : ℕ) := by exact_mod_cast hBnat
      _ ≤ 992 * (Real.exp (a ^ 2)) ^ 3 := by
        push_cast
        gcongr
      _ ≤ Real.exp (a ^ 2) * (Real.exp (a ^ 2)) ^ 3 := by gcongr
      _ = Real.exp (a ^ 2) * Real.exp (3 * a ^ 2) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ = Real.exp (4 * a ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast (lm37SourceLargeBudgetOrder_large cap).trans' (by omega)
  have hlogB : Real.log (B : ℝ) ≤ 4 * a ^ 2 := by
    have := Real.log_le_log hBpos hBupper
    simpa using this
  have hlogBnonneg : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ B from
        (by omega : 1 ≤ 32).trans (lm37SourceLargeBudgetOrder_large cap)))
  have hlogBSq : Real.log (B : ℝ) ^ 2 ≤ 16 * a ^ 4 := by
    nlinarith [sq_nonneg (Real.log (B : ℝ) - 4 * a ^ 2)]
  have hden : (lmGrowthDivisor B : ℝ) ≤ 294914 * a ^ 4 := by
    have hceil : (lmGrowthDenominator B : ℝ) ≤ 147457 * a ^ 4 := by
      apply le_of_lt
      calc
        (lmGrowthDenominator B : ℝ) <
            9216 * Real.log (B : ℝ) ^ 2 + 1 := by
          simpa only [lmGrowthDenominator] using
            Nat.ceil_lt_add_one
              (mul_nonneg (by norm_num) (sq_nonneg (Real.log (B : ℝ))))
        _ ≤ 147457 * a ^ 4 := by
          have ha4 : 1 ≤ a ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ a)
          nlinarith
    rw [lmGrowthDivisor]
    push_cast
    nlinarith
  rw [hD d |>.1]
  simpa only [B, cap, a, L] using hden

/-- Once `s` is in the large branch, the cutoff converts the preceding
`log log N` envelope into the common fourth-logarithm envelope in `s`. -/
theorem eventually_lm43_largeDivisor_le_commonLogFour :
    ∀ᶠ N : ℕ in atTop, ∀ d s : ℕ, lm37SourceCutoff N ≤ s →
      (lmGrowthDivisor
          (lm37SourceLargeBudgetOrder (lm43MaxSlowSize N d)) : ℝ) ≤
        3000000000 * Real.log (s : ℝ) ^ 4 := by
  have hll : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [eventually_lm43_largeDivisor_le_logLogFour,
       hll.eventually (eventually_ge_atTop (1 : ℝ)),
       eventually_ge_atTop (3 : ℕ)]
      with N hdiv ha hN
  intro d s hcut
  let L := Real.log (N : ℝ)
  let a := Real.log L
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
  have hapos : 0 < a := by dsimp [a]; linarith
  have hcutReal : L ^ ((1 : ℝ) / 10) ≤ (s : ℝ) := by
    calc
      L ^ ((1 : ℝ) / 10) ≤ (lm37SourceCutoff N : ℝ) := by
        simpa only [lm37SourceCutoff, SourceLemma35Numerics.cutoff, L] using
          Nat.le_ceil (L ^ ((1 : ℝ) / 10))
      _ ≤ (s : ℝ) := by exact_mod_cast hcut
  have haTen : a ≤ 10 * Real.log (s : ℝ) := by
    have hlog := Real.log_le_log
      (Real.rpow_pos_of_pos hLpos ((1 : ℝ) / 10)) hcutReal
    rw [Real.log_rpow hLpos] at hlog
    dsimp [a]
    nlinarith
  have hpow : a ^ 4 ≤ (10 * Real.log (s : ℝ)) ^ 4 :=
    pow_le_pow_left₀ hapos.le haTen 4
  have hlogSnonneg : 0 ≤ Real.log (s : ℝ) := by nlinarith
  calc
    (lmGrowthDivisor
        (lm37SourceLargeBudgetOrder (lm43MaxSlowSize N d)) : ℝ) ≤
        294914 * a ^ 4 := by simpa only [a, L] using hdiv d
    _ ≤ 294914 * (10 * Real.log (s : ℝ)) ^ 4 := by gcongr
    _ ≤ 3000000000 * Real.log (s : ℝ) ^ 4 := by
      ring_nf
      nlinarith [pow_nonneg hlogSnonneg 4]

/-- Even the denominator computed at `960 * deletionCap^3` is eventually
at most half of the deletion envelope itself. -/
theorem eventually_two_largeDivisor_le_sourceDeletionCap :
    ∀ᶠ N : ℕ in atTop,
      2 * lmGrowthDivisor
          (lm37SourceLargeBudgetOrder (SourceLemma35Numerics.deletionCap N)) ≤
        SourceLemma35Numerics.deletionCap N := by
  have hll : Tendsto
      (fun N : ℕ ↦ Real.log (Real.log (N : ℝ))) atTop atTop :=
    Real.tendsto_log_atTop.comp
      (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop)
  filter_upwards
      [hll.eventually (eventually_ge_atTop (32 : ℝ)),
       Parameters.eventually_const_mul_log_log_pow_le_log 589828 4,
       eventually_const_mul_log_pow_le_sourceDeletionCap 1 (by norm_num) 1,
       eventually_ge_atTop (3 : ℕ)]
      with N ha hasymp hcapL hN
  let L := Real.log (N : ℝ)
  let a := Real.log L
  let cap := SourceLemma35Numerics.deletionCap N
  let B := lm37SourceLargeBudgetOrder cap
  have hapos : 0 < a := by dsimp [a]; linarith
  have hcapOne : 1 ≤ cap := by
    have hLpos : 0 < L := by
      dsimp [L]
      exact Real.log_pos (by exact_mod_cast (show 1 < N by omega))
    have hLone : (1 : ℝ) ≤ L := by
      rw [← Real.exp_log hLpos]
      exact Real.one_le_exp hapos.le
    have : (1 : ℝ) ≤ (cap : ℝ) :=
      hLone.trans (by simpa [L, cap] using hcapL)
    exact_mod_cast this
  have hcap : (cap : ℝ) ≤ Real.exp (a ^ 2) := by
    simpa only [cap, a, L] using SourceLemma35Numerics.deletionCap_cast_le N
  have hBnat : B ≤ 992 * cap ^ 3 := by
    dsimp [B, lm37SourceLargeBudgetOrder]
    calc
      max 32 (960 * cap ^ 3) ≤ 32 + 960 * cap ^ 3 := by
        exact max_le (by omega) (by omega)
      _ ≤ 32 * cap ^ 3 + 960 * cap ^ 3 := by
        exact Nat.add_le_add_right
          (Nat.mul_le_mul_left 32 (one_le_pow₀ hcapOne)) _
      _ = 992 * cap ^ 3 := by ring
  have h992 : (992 : ℝ) ≤ Real.exp (a ^ 2) := by
    apply le_of_lt
    calc
      (992 : ℝ) < a ^ 2 + 1 := by nlinarith
      _ < Real.exp (a ^ 2) := Real.add_one_lt_exp (by positivity)
  have hBupper : (B : ℝ) ≤ Real.exp (4 * a ^ 2) := by
    calc
      (B : ℝ) ≤ (992 * cap ^ 3 : ℕ) := by exact_mod_cast hBnat
      _ ≤ 992 * (Real.exp (a ^ 2)) ^ 3 := by
        push_cast
        gcongr
      _ ≤ Real.exp (a ^ 2) * (Real.exp (a ^ 2)) ^ 3 := by gcongr
      _ = Real.exp (a ^ 2) * Real.exp (3 * a ^ 2) := by
        rw [← Real.exp_nat_mul]
        ring_nf
      _ = Real.exp (4 * a ^ 2) := by rw [← Real.exp_add]; congr 1; ring
  have hBpos : (0 : ℝ) < B := by
    exact_mod_cast (lm37SourceLargeBudgetOrder_large cap).trans' (by omega)
  have hlogB : Real.log (B : ℝ) ≤ 4 * a ^ 2 := by
    have := Real.log_le_log hBpos hBupper
    simpa using this
  have hlogBnonneg : 0 ≤ Real.log (B : ℝ) :=
    Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ B from
        (by omega : 1 ≤ 32).trans (lm37SourceLargeBudgetOrder_large cap)))
  have hlogBSq : Real.log (B : ℝ) ^ 2 ≤ 16 * a ^ 4 := by
    nlinarith [sq_nonneg (Real.log (B : ℝ) - 4 * a ^ 2)]
  have hden : (lmGrowthDivisor B : ℝ) ≤ 294914 * a ^ 4 := by
    have hceil : (lmGrowthDenominator B : ℝ) ≤ 147457 * a ^ 4 := by
      apply le_of_lt
      calc
        (lmGrowthDenominator B : ℝ) <
            9216 * Real.log (B : ℝ) ^ 2 + 1 := by
          simpa only [lmGrowthDenominator] using
            Nat.ceil_lt_add_one
              (mul_nonneg (by norm_num) (sq_nonneg (Real.log (B : ℝ))))
        _ ≤ 147457 * a ^ 4 := by
          have ha4 : 1 ≤ a ^ 4 := one_le_pow₀ (by linarith : (1 : ℝ) ≤ a)
          nlinarith
    rw [lmGrowthDivisor]
    push_cast
    nlinarith
  have hreal : ((2 * lmGrowthDivisor B : ℕ) : ℝ) ≤ (cap : ℝ) := by
    push_cast
    calc
      (2 : ℝ) * lmGrowthDivisor B ≤ 589828 * a ^ 4 := by nlinarith
      _ ≤ L := by simpa only [a, L] using hasymp
      _ ≤ (cap : ℝ) := by simpa [L, cap] using hcapL
  have hnat : 2 * lmGrowthDivisor B ≤ cap := by exact_mod_cast hreal
  simpa only [B, cap] using hnat

/-- The canonical robust deletion set fits strictly in the large-family
gain at the common source endpoint. -/
theorem eventually_lm43_deletion_workspace :
    ∀ᶠ N : ℕ in atTop, ∀ d : ℕ,
      lm43DeletionCap N d <
        lm37SourceLargeBudget (lm43MaxSlowSize N d)
          (lm43MaxSlowSize N d ^ 2 * lm37SourceCutoff N) := by
  filter_upwards
      [eventually_lm43_maxSlowSize_eq_sourceDeletionCap,
       eventually_two_largeDivisor_le_sourceDeletionCap,
       SourceLemma35Numerics.eventually_source_ambient_bounds]
      with N hD hdiv hcut
  intro d
  let cap := SourceLemma35Numerics.deletionCap N
  let C := lmGrowthDivisor (lm37SourceLargeBudgetOrder cap)
  have hcapPos : 0 < cap := (Nat.zero_le _).trans_lt (hD d).2
  have hCpos : 0 < C := lmGrowthDivisor_pos
    ((lm37SourceLargeBudgetOrder_large cap).trans' (by omega))
  have hDlt : lm43DeletionCap N d < cap := by
    simpa only [cap] using (hD d).2
  have hdiv' : 2 * C ≤ cap := by
    simpa only [C, cap] using hdiv
  have hUone : lm43DeletionCap N d + 1 ≤ cap := by omega
  have hCle : C ≤ cap := by omega
  have hproduct : (lm43DeletionCap N d + 1) * C ≤
      cap ^ 2 * lm37SourceCutoff N := by
    calc
      (lm43DeletionCap N d + 1) * C ≤ cap * cap := Nat.mul_le_mul hUone hCle
      _ = cap ^ 2 := by ring
      _ ≤ cap ^ 2 * lm37SourceCutoff N :=
        Nat.le_mul_of_pos_right _ hcut.1
  rw [hD d |>.1]
  simp only [lm37SourceLargeBudget, lmGrowthGain]
  rw [Nat.lt_iff_add_one_le, Nat.le_div_iff_mul_le hCpos]
  simpa only [C] using hproduct

/-! ## The reusable uniform finite package -/

/-- Above one global degree threshold, every robust source target below the
final ball target satisfies the exact finite numerical record.  Uniformity
in `N` follows by requiring `d ≤ N`. -/
theorem exists_lm43_sourceNumericalBounds_threshold :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      ∀ M : ℕ, M ≤ lm43BallTarget N d → lm37SourceMinSize d < M →
        LM37SourceNumericalBounds N d (lm43DeletionCap N d)
          (lm43R N d) (lm43BallRadius N d) M (lm43DegreeInto N d)
          (lm43MaxSlowSize N d) (lm43R N d) := by
  obtain ⟨dSmall, hdSmall⟩ :=
    (eventually_atTop.1 eventually_lm37_small_workspace)
  have hcapNine : ∀ᶠ N : ℕ in atTop,
      9 ≤ SourceLemma35Numerics.deletionCap N := by
    filter_upwards
        [eventually_const_mul_log_pow_le_sourceDeletionCap 9 (by norm_num) 0]
        with N hN
    have : (9 : ℝ) ≤ (SourceLemma35Numerics.deletionCap N : ℝ) := by
      simpa using hN
    exact_mod_cast this
  have hambient : ∀ᶠ N : ℕ in atTop, ∀ d M : ℕ,
      dSmall ≤ d → 4096 ≤ d →
      M ≤ lm43BallTarget N d → lm37SourceMinSize d < M →
        LM37SourceNumericalBounds N d (lm43DeletionCap N d)
          (lm43R N d) (lm43BallRadius N d) M (lm43DegreeInto N d)
          (lm43MaxSlowSize N d) (lm43R N d) := by
    filter_upwards
        [eventually_lm43_maxSlowSize_eq_sourceDeletionCap,
         eventually_lm43_ballTarget_le_firstSlowGrowth,
         eventually_lm43_large_sample_and_half,
         eventually_lm37_small_sample,
         eventually_lm43_deletion_workspace,
         SourceLemma35Numerics.eventually_source_ambient_bounds,
         eventually_lm43_R_pos, hcapNine]
        with N hD hgrowth hlarge hsmall hdelete hambient hR hcap9
    intro d M hdSmall' hdLarge hM hguard
    have hD9 : 9 ≤ lm43MaxSlowSize N d := by rw [hD d |>.1]; exact hcap9
    have hMD : M ≤ lm43MaxSlowSize N d :=
      hM.trans (lm43BallTarget_le_maxSlowSize N d)
    have hU : lm43DeletionCap N d ≤
        SourceLemma35Numerics.deletionCap N := Nat.le_of_lt (hD d).2
    have hdegree : lm43DegreeInto N d ≤ d := by
      simp only [lm43DegreeInto]
      omega
    refine
      { degree_large := hdLarge
        index := le_rfl
        target_le_D := hMD
        target_growth := hM.trans (hgrowth d)
        cutoff_pos := hambient.1
        cutoff_le_D := ?_
        D_pos := hD9.trans' (by omega)
        T_pos := hR d
        large_sample := (hlarge d).1
        small_sample := ?_
        degree_upper := source_degree_upper_of_minSize_lt_target hguard hMD hD9 hambient.1
        half := (hlarge d).2
        deletion_workspace := hdelete d
        small_workspace := ?_ }
    · simpa only [lm37SourceCutoff] using lm43Cutoff_le_maxSlowSize N d
    · exact hsmall d (lm43DeletionCap N d) (lm43DegreeInto N d) hdegree hU
    · intro r hr _
      simpa only [lm43DegreeInto] using hdSmall d hdSmall' r hr
  obtain ⟨N₀, hN₀⟩ := eventually_atTop.1 hambient
  refine ⟨max 4096 (max dSmall N₀), ?_⟩
  intro d hd N hdN M hM hguard
  apply hN₀ N
  · exact (le_max_right dSmall N₀).trans ((le_max_right 4096 _).trans hd) |>.trans hdN
  · exact (le_max_left dSmall N₀).trans ((le_max_right 4096 _).trans hd)
  · exact (le_max_left 4096 _).trans hd
  · exact hM
  · exact hguard

/-- Constructor-level form of the uniform robust source theorem. -/
theorem exists_lm43_sourceBounds_threshold :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      ∀ M contact : ℕ, M ≤ lm43BallTarget N d →
        lm37SourceMinSize d < M →
          Nonempty (LM37SourceBounds N d (lm43DeletionCap N d)
            (lm43R N d) contact (lm43BallRadius N d) M
            (lm43DegreeInto N d) (lm43MaxSlowSize N d) (lm43R N d)) := by
  obtain ⟨d₀, hd₀⟩ := exists_lm43_sourceNumericalBounds_threshold
  refine ⟨d₀, ?_⟩
  intro d hd N hdN M contact hM hguard
  exact ⟨concreteLM37SourceBounds N d (lm43DeletionCap N d)
    (lm43R N d) contact (lm43BallRadius N d) M (lm43DegreeInto N d)
    (lm43MaxSlowSize N d) (lm43R N d) (hd₀ d hd N hdN M hM hguard)⟩

/-! ## Candidate-local geometry at the canonical parameters -/

/-- An explicit degree threshold pushes the candidate minimum radius beyond
any prescribed fixed route tail. -/
theorem routeTail_le_lm43MinRadius_sq
    (S : ℕ) {N d : ℕ} (hd : 64 * 2 ^ S ≤ d) :
    S ≤ lm43MinRadius N d ^ 2 := by
  let n := lm43CoreDegree N d + 1
  have hcore : 2 ^ S ≤ lm43CoreDegree N d := by
    simp only [lm43CoreDegree]
    exact (Nat.le_div_iff_mul_le (by norm_num : 0 < 64)).2 (by
      simpa [mul_comm] using hd)
  have hpowPos : 0 < 2 ^ S := by positivity
  have hcorePos : 0 < lm43CoreDegree N d := hpowPos.trans_le hcore
  have hn : 2 ≤ n := by dsimp [n]; omega
  have hpow : 2 ^ S ≤ n := hcore.trans (by dsimp [n]; omega)
  have hlog : S ≤ Nat.log 2 n :=
    Nat.le_log_of_pow_le (by omega) hpow
  have hdiv : 0 < lmGrowthDivisor n := lmGrowthDivisor_pos hn
  have hround : S ≤ lmGrowthRounds n := by
    rw [lmGrowthRounds]
    calc
      S ≤ Nat.log 2 n := hlog
      _ ≤ Nat.log 2 n + 1 := by omega
      _ ≤ 2 * lmGrowthDivisor n * (Nat.log 2 n + 1) :=
        Nat.le_mul_of_pos_left _ (mul_pos (by omega) hdiv)
  have hmin : S ≤ lm43MinRadius N d := by
    calc
      S ≤ lmGrowthRounds n := hround
      _ ≤ 5 * lmGrowthRounds n := Nat.le_mul_of_pos_left _ (by omega)
      _ = lm43MinRadius N d := by
        simp only [lm43MinRadius, lm43MinRadiusFrom, lm43CoreRadius, n]
  have hd64 : 64 ≤ d := by
    have hpowOne : 1 ≤ 2 ^ S := one_le_pow₀ (by omega)
    have : 64 ≤ 64 * 2 ^ S := by
      simpa using Nat.mul_le_mul_left 64 hpowOne
    exact this.trans hd
  have hminPos : 0 < lm43MinRadius N d := lm43MinRadius_pos hd64
  exact hmin.trans (by
    simpa [pow_two] using
      Nat.le_mul_of_pos_right (lm43MinRadius N d) hminPos)

/-- One absolute degree threshold supplies the candidate-local route
geometry for both canonical robust source radii. -/
theorem exists_lm43_sourceGeometricBounds_threshold :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      LM37SourceGeometricBounds N d (lm43MinRadius N d)
        (lm43AvoidingRadius N) (lm43MaxSlowSize N d) := by
  obtain ⟨routeTail, hroute⟩ := eventually_atTop.1
    (eventually_lm37_firstSlow_route_of_divisor_log_bound
      3000000000 (by norm_num))
  obtain ⟨smallTail, hsmall⟩ :=
    eventually_atTop.1 eventually_lm37_smallDivisor_le_commonLogFour
  obtain ⟨largeTail, hlarge⟩ :=
    eventually_atTop.1 eventually_lm43_largeDivisor_le_commonLogFour
  let commonTail := max 1 (max routeTail smallTail)
  refine ⟨max (64 * 2 ^ commonTail) largeTail, ?_⟩
  intro d hd N hdN
  have hdCommon : 64 * 2 ^ commonTail ≤ d :=
    (le_max_left _ largeTail).trans hd
  have hlargeN : largeTail ≤ N :=
    (le_max_right (64 * 2 ^ commonTail) largeTail).trans hd |>.trans hdN
  have htailMin : commonTail ≤ lm43MinRadius N d ^ 2 :=
    routeTail_le_lm43MinRadius_sq commonTail hdCommon
  have hreach : ∀ ell s, lm43MinRadius N d ^ 2 ≤ s → 0 < ell →
      ell ≤ lm43AvoidingRadius N → lm37FirstSlowGrowth (ell - 1) < s →
      lm37FirstSlowStepLoss ell + (11 * Nat.sqrt s + 1) + 2 * ell ≤
        lm37SourceNeighborBudget (lm43MaxSlowSize N d)
          (lm37SourceCutoff N) s := by
    intro ell s hmin hell _ hslow
    have hsCommon : commonTail ≤ s := htailMin.trans (hmin.trans le_rfl)
    have hsRoute : routeTail ≤ s :=
      (le_max_left routeTail smallTail).trans
        ((le_max_right 1 _).trans hsCommon)
    have hsSmall : smallTail ≤ s :=
      (le_max_right routeTail smallTail).trans
        ((le_max_right 1 _).trans hsCommon)
    let cost := lm37FirstSlowStepLoss ell +
      (11 * Nat.sqrt s + 1) + 2 * ell
    by_cases hscut : s < lm37SourceCutoff N
    · let Q := lmGrowthDivisor (lm37SourceSmallBudgetOrder s)
      have hQpos : 0 < Q := lmGrowthDivisor_pos
        ((by omega : 2 ≤ 32).trans (lm37SourceSmallBudgetOrder_large s))
      have hmul : Q * cost ≤ s := by
        apply hroute s hsRoute Q ell
        · simpa only [Q] using hsmall s hsSmall
        · exact hell
        · exact hslow
      have hcost : cost ≤ s / Q := by
        apply (Nat.le_div_iff_mul_le hQpos).2
        simpa [mul_comm] using hmul
      simpa only [lm37SourceNeighborBudget, if_pos hscut,
        lm37SourceSmallBudget, lmGrowthGain, Q, cost] using hcost
    · let Q := lmGrowthDivisor
        (lm37SourceLargeBudgetOrder (lm43MaxSlowSize N d))
      have hQpos : 0 < Q := lmGrowthDivisor_pos
        ((by omega : 2 ≤ 32).trans
          (lm37SourceLargeBudgetOrder_large (lm43MaxSlowSize N d)))
      have hcut : lm37SourceCutoff N ≤ s := Nat.le_of_not_gt hscut
      have hmul : Q * cost ≤ s := by
        apply hroute s hsRoute Q ell
        · simpa only [Q] using hlarge N hlargeN d s hcut
        · exact hell
        · exact hslow
      have hcost : cost ≤ s / Q := by
        apply (Nat.le_div_iff_mul_le hQpos).2
        simpa [mul_comm] using hmul
      simpa only [lm37SourceNeighborBudget, if_neg hscut,
        lm37SourceLargeBudget, lmGrowthGain, Q, cost] using hcost
  exact
    { reach := hreach
      final := by
        intro ell s hmin hell hellRadius hslow
        have h := hreach ell s hmin hell hellRadius hslow
        omega }


/-! ## Routed source package assembly -/

/-- Once the candidate-local geometric estimate is available uniformly,
the three routed source calls have one common uniform threshold.  Claim 4.5
uses `targetOrder`; Claim 4.6 and the final call use `ballTarget`. -/
theorem exists_lm43_routedSourceNumericalPackage_threshold_of_geometry
    (hgeometry : ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      LM37SourceGeometricBounds N d (lm43MinRadius N d)
        (lm43AvoidingRadius N) (lm43MaxSlowSize N d)) :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      LM43RoutedSourceNumericalPackage N d := by
  obtain ⟨dNumerical, hNumerical⟩ :=
    exists_lm43_sourceNumericalBounds_threshold
  obtain ⟨dGeometry, hGeometry⟩ := hgeometry
  obtain ⟨NRadius, hRadius⟩ :=
    eventually_atTop.1 eventually_lm43_candidateRadius_pos
  refine ⟨max dNumerical (max dGeometry NRadius), ?_⟩
  intro d hd N hdN
  have hdNumerical : dNumerical ≤ d := (le_max_left _ _).trans hd
  have hdGeometry : dGeometry ≤ d :=
    (le_max_left dGeometry NRadius).trans ((le_max_right dNumerical _).trans hd)
  have hNRadius : NRadius ≤ N :=
    (le_max_right dGeometry NRadius).trans
      ((le_max_right dNumerical _).trans hd) |>.trans hdN
  have hmaxRadius : 0 < lm43MaxRadius N d := by
    simpa only [lm43MaxRadius] using hRadius N hNRadius d
  have htargetBall : lm43TargetOrder N d ≤ lm43BallTarget N d :=
    lm43TargetOrder_le_ballTarget N d hmaxRadius
  have hgeom : LM37SourceGeometricBounds N d (lm43MinRadius N d)
      (lm43AvoidingRadius N) (lm43MaxSlowSize N d) :=
    hGeometry d hdGeometry N hdN
  refine
    { claim45 := ?_
      claim46 := ?_
      final := ?_ }
  · intro hguard
    exact
      { source := by
          simpa only [lm43HighRadius, lm43BallRadius] using
            hNumerical d hdNumerical N hdN (lm43TargetOrder N d)
              htargetBall hguard
        geometry := by
          simpa only [lm43HighRadius] using hgeom }
  · intro hguard
    exact
      { source := hNumerical d hdNumerical N hdN (lm43BallTarget N d)
          le_rfl hguard
        geometry := by
          simpa only [lm43BallRadius] using hgeom }
  · intro hguard
    exact
      { source := hNumerical d hdNumerical N hdN (lm43BallTarget N d)
          le_rfl hguard
        geometry := by
          simpa only [lm43BallRadius] using hgeom }

/-- The three canonical source routes have one common uniform threshold. -/
theorem exists_lm43_routedSourceNumericalPackage_threshold :
    ∃ d₀ : ℕ, ∀ d : ℕ, d₀ ≤ d → ∀ N : ℕ, d ≤ N →
      LM43RoutedSourceNumericalPackage N d :=
  exists_lm43_routedSourceNumericalPackage_threshold_of_geometry
    exists_lm43_sourceGeometricBounds_threshold

end Erdos63
