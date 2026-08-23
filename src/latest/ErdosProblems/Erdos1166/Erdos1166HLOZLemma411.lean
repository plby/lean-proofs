/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos1166.Erdos1166HLOZScreeningAssembly
import ErdosProblems.Erdos1166.Erdos1166HLOZUrn

/-!
The deterministic probability assembly in HLOZ Lemma 4.11.  This file
formalizes the passage from the initial estimate (4.47) and the one-step
estimate (4.48) to the uniform stretched-log estimate (4.44).
-/

open Filter Asymptotics
open scoped BigOperators Topology

namespace Erdos1166.HLOZLemma411

/-- The geometric thresholds used in the successive screening levels. -/
def geometricThreshold (ρ₁ R : ℝ) (l : ℕ) : ℝ :=
  ρ₁ * R ^ (l - 1)

@[simp]
lemma geometricThreshold_one (ρ₁ R : ℝ) :
    geometricThreshold ρ₁ R 1 = ρ₁ := by
  simp [geometricThreshold]

/-- Geometric thresholds never fall below the first threshold. -/
lemma geometricThreshold_le (ρ₁ R : ℝ) (hρ : 0 ≤ ρ₁) (hR : 1 ≤ R)
    {l : ℕ} (_hl : 1 ≤ l) :
    ρ₁ ≤ geometricThreshold ρ₁ R l := by
  unfold geometricThreshold
  have hpow : (1 : ℝ) ≤ R ^ (l - 1) := one_le_pow₀ hR
  simpa only [mul_one] using mul_le_mul_of_nonneg_left hpow hρ

/-- Division-free finite geometric-series identity for the thresholds. -/
lemma sum_geometricThreshold_mul_sub (ρ₁ R : ℝ) (n : ℕ) :
    (∑ k ∈ Finset.range n, geometricThreshold ρ₁ R (k + 1)) * (R - 1) =
      ρ₁ * (R ^ n - 1) := by
  simp_rw [geometricThreshold, show ∀ k : ℕ, k + 1 - 1 = k by omega]
  rw [← Finset.mul_sum, mul_assoc, geom_sum_mul]

/-- The exponentially small errors at geometrically increasing thresholds
sum to at most the number of levels times the first error. -/
lemma sum_exp_neg_geometricThreshold_le
    (ρ₁ R c : ℝ) (hρ : 0 ≤ ρ₁) (hR : 1 ≤ R) (hc : 0 ≤ c) (n : ℕ) :
    ∑ k ∈ Finset.range n,
        Real.exp (-c * geometricThreshold ρ₁ R (k + 1)) ≤
      (n : ℝ) * Real.exp (-c * ρ₁) := by
  calc
    ∑ k ∈ Finset.range n,
        Real.exp (-c * geometricThreshold ρ₁ R (k + 1)) ≤
        ∑ _k ∈ Finset.range n, Real.exp (-c * ρ₁) := by
      apply Finset.sum_le_sum
      intro k hk
      apply Real.exp_le_exp.mpr
      have hthreshold := geometricThreshold_le ρ₁ R hρ hR
        (show 1 ≤ k + 1 by omega)
      nlinarith
    _ = (n : ℝ) * Real.exp (-c * ρ₁) := by simp

/-- Iterating exactly the source one-step estimate (4.48).  The index `n`
counts the transitions from level `1` through level `n+1`. -/
lemma source_recursion_geometric_bound
    (q : ℕ → ℝ) (m n : ℕ) (ρ₁ R c c₁ a : ℝ)
    (hρ : 0 ≤ ρ₁) (hR : 1 ≤ R) (hc : 0 ≤ c)
    (hstep : ∀ k < n,
      q (k + 2) ≤ q (k + 1) +
        Real.exp (-c * geometricThreshold ρ₁ R (k + 2)) +
        Real.exp (-c₁ * (m : ℝ) ^ a)) :
    q (n + 1) ≤ q 1 +
      (n : ℝ) * Real.exp (-c * ρ₁) +
      (n : ℝ) * Real.exp (-c₁ * (m : ℝ) ^ a) := by
  induction n with
  | zero => simp
  | succ n ih =>
      have hprev := ih (fun k hk ↦ hstep k (hk.trans (Nat.lt_succ_self n)))
      have hone := hstep n (Nat.lt_succ_self n)
      have hthreshold := geometricThreshold_le ρ₁ R hρ hR
        (show 1 ≤ n + 2 by omega)
      have herr : Real.exp (-c * geometricThreshold ρ₁ R (n + 2)) ≤
          Real.exp (-c * ρ₁) := by
        apply Real.exp_le_exp.mpr
        nlinarith
      calc
        q (n + 1 + 1) ≤ q (n + 1) +
            Real.exp (-c * geometricThreshold ρ₁ R (n + 2)) +
            Real.exp (-c₁ * (m : ℝ) ^ a) := by
          simpa only [Nat.succ_eq_add_one, Nat.add_assoc] using hone
        _ ≤ (q 1 + (n : ℝ) * Real.exp (-c * ρ₁) +
              (n : ℝ) * Real.exp (-c₁ * (m : ℝ) ^ a)) +
            Real.exp (-c * ρ₁) +
            Real.exp (-c₁ * (m : ℝ) ^ a) := by gcongr
        _ = q 1 + ((n + 1 : ℕ) : ℝ) * Real.exp (-c * ρ₁) +
            ((n + 1 : ℕ) : ℝ) * Real.exp (-c₁ * (m : ℝ) ^ a) := by
          push_cast
          ring

/-- A positive power eventually dominates any fixed multiple of `log²`. -/
lemma eventually_const_mul_log_sq_le_rpow
    {c c₁ a : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (ha : 0 < a) :
    ∀ᶠ m : ℕ in atTop,
      c * Real.log (m : ℝ) ^ 2 ≤ c₁ * (m : ℝ) ^ a := by
  have hlog :=
    Erdos1166.HLOZScreeningAssembly.eventually_log_rpow_le_rpow
      (p := (2 : ℝ)) (by linarith : 0 < a / 2)
  have hrpow : Tendsto (fun m : ℕ ↦ (m : ℝ) ^ (a / 2)) atTop atTop :=
    (tendsto_rpow_atTop (by linarith : 0 < a / 2)).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))
  have hlarge := hrpow.eventually (eventually_ge_atTop (c / c₁))
  filter_upwards [hlog, hlarge, eventually_ge_atTop 1] with m hlog hlarge hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hhalf0 : 0 ≤ (m : ℝ) ^ (a / 2) := Real.rpow_nonneg hmpos.le _
  have hc_le : c ≤ c₁ * (m : ℝ) ^ (a / 2) := by
    simpa only [mul_comm] using (div_le_iff₀ hc₁).mp hlarge
  have hlog' : Real.log (m : ℝ) ^ 2 ≤ (m : ℝ) ^ (a / 2) := by
    simpa only [Real.rpow_two] using hlog
  calc
    c * Real.log (m : ℝ) ^ 2 ≤ c * (m : ℝ) ^ (a / 2) := by
      gcongr
    _ ≤ c₁ * ((m : ℝ) ^ (a / 2) * (m : ℝ) ^ (a / 2)) := by
      calc
        c * (m : ℝ) ^ (a / 2) ≤
            (c₁ * (m : ℝ) ^ (a / 2)) * (m : ℝ) ^ (a / 2) :=
          mul_le_mul_of_nonneg_right hc_le hhalf0
        _ = c₁ * ((m : ℝ) ^ (a / 2) * (m : ℝ) ^ (a / 2)) := by ring
    _ = c₁ * (m : ℝ) ^ a := by
      rw [← Real.rpow_add hmpos]
      congr 2
      ring

/-- A polynomial number of `exp (-c log² m)` errors is absorbed while
retaining the explicit safe constant `c/2` in the exponent. -/
lemma eventually_three_rpow_mul_exp_neg_log_sq_le
    {c b : ℝ} (hc : 0 < c) (hb : 0 ≤ b) :
    ∀ᶠ m : ℕ in atTop,
      3 * (m : ℝ) ^ b * Real.exp (-c * Real.log (m : ℝ) ^ 2) ≤
        Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := by
  let A : ℝ := Real.log 3 + b
  have hA0 : 0 ≤ A := by
    dsimp [A]
    positivity
  have hthresholdReal : ∀ᶠ x : ℝ in atTop,
      max 1 (2 * A / c) ≤ Real.log x :=
    Real.tendsto_log_atTop.eventually
      (eventually_ge_atTop (max 1 (2 * A / c)))
  have hthreshold :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).eventually hthresholdReal
  filter_upwards [hthreshold, eventually_ge_atTop 1] with m hlog hm
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hL1 : (1 : ℝ) ≤ Real.log (m : ℝ) :=
    (le_max_left _ _).trans hlog
  have hLA : 2 * A / c ≤ Real.log (m : ℝ) :=
    (le_max_right _ _).trans hlog
  have hpoly : Real.log 3 + b * Real.log (m : ℝ) ≤
      (c / 2) * Real.log (m : ℝ) ^ 2 := by
    have hA_le : A ≤ (c / 2) * Real.log (m : ℝ) := by
      have hmul := (div_le_iff₀ hc).mp hLA
      nlinarith
    have hbL : b * Real.log (m : ℝ) ≤ A * Real.log (m : ℝ) := by
      gcongr
      dsimp [A]
      nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
    calc
      Real.log 3 + b * Real.log (m : ℝ) ≤
          A * Real.log (m : ℝ) := by
        dsimp [A]
        nlinarith [Real.log_pos (by norm_num : (1 : ℝ) < 3)]
      _ ≤ ((c / 2) * Real.log (m : ℝ)) * Real.log (m : ℝ) := by
        gcongr
      _ = (c / 2) * Real.log (m : ℝ) ^ 2 := by ring
  rw [Real.rpow_def_of_pos hmpos]
  calc
    3 * Real.exp (Real.log (m : ℝ) * b) *
          Real.exp (-c * Real.log (m : ℝ) ^ 2) =
        Real.exp (Real.log 3) * Real.exp (Real.log (m : ℝ) * b) *
          Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      rw [Real.exp_log (by norm_num : (0 : ℝ) < 3)]
    _ =
        Real.exp (Real.log 3 + b * Real.log (m : ℝ) -
          c * Real.log (m : ℝ) ^ 2) := by
      rw [← Real.exp_add, ← Real.exp_add]
      congr 1
      ring
    _ ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := by
      apply Real.exp_le_exp.mpr
      nlinarith

/-- HLOZ Lemma 4.11, equations (4.47)--(4.48) to (4.44), as a strongest
arithmetic assembly theorem.  The hypotheses `hq₁` and `hstep` are exactly
the source base and recursive estimates.  The number of transitions is at
most `m^b`, and the first geometric threshold is at least `log² m`.

The conclusion has the explicit safe constant `c₂ = c/2`. -/
theorem eventually_hloz_lemma_4_11_assembly
    {c c₁ a b R : ℝ} (hc : 0 < c) (hc₁ : 0 < c₁) (ha : 0 < a)
    (hb : 0 ≤ b) (hR : 1 ≤ R) :
    ∀ᶠ m : ℕ in atTop, ∀ (q : ℕ → ℝ) (n : ℕ) (ρ₁ : ℝ),
      Real.log (m : ℝ) ^ 2 ≤ ρ₁ →
      ((n + 1 : ℕ) : ℝ) ≤ (m : ℝ) ^ b →
      q 1 ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) →
      (∀ k < n,
        q (k + 2) ≤ q (k + 1) +
          Real.exp (-c * geometricThreshold ρ₁ R (k + 2)) +
          Real.exp (-c₁ * (m : ℝ) ^ a)) →
      q (n + 1) ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := by
  have hstretch := eventually_const_mul_log_sq_le_rpow hc hc₁ ha
  have habsorb := eventually_three_rpow_mul_exp_neg_log_sq_le hc hb
  filter_upwards [hstretch, habsorb, eventually_ge_atTop 1] with m hstretch habsorb hm
  intro q n ρ₁ hρ hlevels hq₁ hstep
  have hmpos : (0 : ℝ) < m := by exact_mod_cast (show 0 < m by omega)
  have hlog0 : 0 ≤ Real.log (m : ℝ) :=
    Real.log_nonneg (by exact_mod_cast hm)
  have hρ0 : 0 ≤ ρ₁ := (sq_nonneg _).trans hρ
  have hnlevels : (n : ℝ) ≤ (m : ℝ) ^ b := by
    calc
      (n : ℝ) ≤ ((n + 1 : ℕ) : ℝ) := by push_cast; linarith
      _ ≤ (m : ℝ) ^ b := hlevels
  have hM1 : (1 : ℝ) ≤ (m : ℝ) ^ b :=
    Real.one_le_rpow (by exact_mod_cast hm) hb
  have hrhoError : Real.exp (-c * ρ₁) ≤
      Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hstretchError : Real.exp (-c₁ * (m : ℝ) ^ a) ≤
      Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
    apply Real.exp_le_exp.mpr
    nlinarith
  have hiter := source_recursion_geometric_bound q m n ρ₁ R c c₁ a
    hρ0 hR hc.le hstep
  calc
    q (n + 1) ≤ q 1 + (n : ℝ) * Real.exp (-c * ρ₁) +
        (n : ℝ) * Real.exp (-c₁ * (m : ℝ) ^ a) := hiter
    _ ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) +
        (m : ℝ) ^ b * Real.exp (-c * Real.log (m : ℝ) ^ 2) +
        (m : ℝ) ^ b * Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      gcongr
    _ ≤ 3 * (m : ℝ) ^ b *
        Real.exp (-c * Real.log (m : ℝ) ^ 2) := by
      have he0 : 0 ≤ Real.exp (-c * Real.log (m : ℝ) ^ 2) := (Real.exp_pos _).le
      nlinarith
    _ ≤ Real.exp (-(c / 2) * Real.log (m : ℝ) ^ 2) := habsorb

end Erdos1166.HLOZLemma411
