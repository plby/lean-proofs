/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.SourceLemma37
import ErdosProblems.Erdos63.GrowthSchedule

/-!
# Source-faithful numerical constructors for Lemma 3.7

This graph-free file uses the literal first-slow profile
`floor(exp(ell^(1/16)))`.  The available-neighbour budget is the canonical
`lmGrowthGain`, evaluated at the auxiliary order `max 32 (960 * D^3)`.
Consequently its denominator has order `log(D)^2`, as required by the source
profile, rather than order `log(N)^2`.
-/

open Filter Finset
open scoped BigOperators

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-- The comparison curve from the proof of Lemma 3.7. -/
noncomputable def lm37FirstSlowGrowth (ell : ℕ) : ℕ :=
  ⌊Real.exp ((ell : ℝ) ^ ((1 : ℝ) / 16))⌋₊

/-- The exact pointwise loss from radius `ell - 1` to radius `ell`. -/
noncomputable def lm37FirstSlowStepLoss (ell : ℕ) : ℕ :=
  lm37FirstSlowGrowth ell - lm37FirstSlowGrowth (ell - 1)

/-- An auxiliary order containing every replicated large set. -/
def lm37SourceLargeBudgetOrder (D : ℕ) : ℕ :=
  max 32 (960 * D ^ 3)

/-- The corresponding auxiliary order for one actual small size. -/
def lm37SourceSmallBudgetOrder (r : ℕ) : ℕ :=
  max 32 (960 * r ^ 3)

/-- Large-family budgets use the common endpoint `D`. -/
noncomputable def lm37SourceLargeBudget (D s : ℕ) : ℕ :=
  lmGrowthGain (lm37SourceLargeBudgetOrder D) s

/-- Small-family budgets use the actual size `r`, not the ambient endpoint.
This is what makes the estimate uniform when `N` grows and `d` is fixed above
the eventual global degree threshold. -/
noncomputable def lm37SourceSmallBudget (r s : ℕ) : ℕ :=
  lmGrowthGain (lm37SourceSmallBudgetOrder r) s

/-- The pointwise budget switches exactly at the source cutoff. -/
noncomputable def lm37SourceNeighborBudget (D cutoff s : ℕ) : ℕ :=
  if s < cutoff then lm37SourceSmallBudget s s else lm37SourceLargeBudget D s

theorem lm37SourceLargeBudgetOrder_large (D : ℕ) :
    32 ≤ lm37SourceLargeBudgetOrder D :=
  le_max_left _ _

theorem lm37SourceSmallBudgetOrder_large (r : ℕ) :
    32 ≤ lm37SourceSmallBudgetOrder r :=
  le_max_left _ _

theorem cube_le_lm37SourceLargeBudgetOrder {D s : ℕ} (hs : s ≤ D ^ 3) :
    s ≤ lm37SourceLargeBudgetOrder D := by
  calc
    s ≤ D ^ 3 := hs
    _ ≤ 960 * D ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ lm37SourceLargeBudgetOrder D := le_max_right _ _

theorem cube_le_lm37SourceSmallBudgetOrder (r : ℕ) :
    r ^ 3 ≤ lm37SourceSmallBudgetOrder r := by
  calc
    r ^ 3 ≤ 960 * r ^ 3 := Nat.le_mul_of_pos_left _ (by omega)
    _ ≤ lm37SourceSmallBudgetOrder r := le_max_right _ _

theorem lm37SourceLargeBudget_mono (D : ℕ) :
    Monotone (lm37SourceLargeBudget D) :=
  lmGrowthGain_mono _

/-- Replication commutes with the division budget in the required direction. -/
theorem mul_lmGrowthGain_le (B q r : ℕ) :
    q * lmGrowthGain B r ≤ lmGrowthGain B (q * r) := by
  let C := lmGrowthDivisor B
  by_cases hC : C = 0
  · simp [lmGrowthGain, C, hC]
  · have hCpos : 0 < C := Nat.pos_of_ne_zero hC
    apply (Nat.le_div_iff_mul_le hCpos).2
    change q * (r / C) * C ≤ q * r
    calc
      q * (r / C) * C = q * ((r / C) * C) := by ring
      _ ≤ q * r := Nat.mul_le_mul_left q (Nat.div_mul_le_self r C)

/-- Two source budgets fit inside the exact LM expansion profile. -/
theorem two_lm37SourceLargeBudget_le_expansion
    {d D s : ℕ} (hd : 1 ≤ d)
    (hlower : (d : ℝ) / 128 ≤ (s : ℝ))
    (hupper : s ≤ D ^ 3) :
    (((2 * lm37SourceLargeBudget D s : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  exact two_lmGrowthGain_le_expansion
    (lm37SourceLargeBudgetOrder_large D) hd hlower
      (cube_le_lm37SourceLargeBudgetOrder hupper)

theorem two_lm37SourceSmallBudget_le_expansion
    {d r : ℕ} (hd : 1 ≤ d)
    (hlower : (d : ℝ) / 128 ≤ ((r ^ 3 : ℕ) : ℝ)) :
    (((2 * lm37SourceSmallBudget r (r ^ 3) : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) (r ^ 3) *
        ((r ^ 3 : ℕ) : ℝ) := by
  exact two_lmGrowthGain_le_expansion
    (lm37SourceSmallBudgetOrder_large r) hd hlower
      (cube_le_lm37SourceSmallBudgetOrder r)

/-- The source budget is superadditive over finite families. -/
theorem sum_lm37SourceLargeBudget_le
    {I : Type*} [DecidableEq I] (D : ℕ) (J : Finset I) (f : I → ℕ) :
    ∑ i ∈ J, lm37SourceLargeBudget D (f i) ≤
      lm37SourceLargeBudget D (∑ i ∈ J, f i) := by
  simp only [lm37SourceLargeBudget, lmGrowthGain]
  induction J using Finset.induction_on with
  | empty => simp
  | @insert i J hi ih =>
      rw [sum_insert hi, sum_insert hi]
      calc
        f i / lmGrowthDivisor (lm37SourceLargeBudgetOrder D) +
              ∑ j ∈ J, f j / lmGrowthDivisor (lm37SourceLargeBudgetOrder D) ≤
            f i / lmGrowthDivisor (lm37SourceLargeBudgetOrder D) +
              (∑ j ∈ J, f j) / lmGrowthDivisor (lm37SourceLargeBudgetOrder D) :=
          Nat.add_le_add_left ih _
        _ ≤ (f i + ∑ j ∈ J, f j) /
              lmGrowthDivisor (lm37SourceLargeBudgetOrder D) :=
          Nat.div_add_div_le_add_div

/-- Named finite estimates sufficient for the literal source split. -/
structure LM37SourceNumericalBounds
    (N d Ucap Icard radius M degreeIntoU D T : ℕ) : Prop where
  degree_large : 4096 ≤ d
  index : T ≤ Icard
  target_le_D : M ≤ D
  target_growth : M ≤ lm37FirstSlowGrowth radius
  cutoff_pos : 0 < lm37SourceCutoff N
  cutoff_le_D : lm37SourceCutoff N ≤ D
  D_pos : 0 < D
  T_pos : 0 < T
  large_sample : D ^ 3 ≤ (T + 1) / 2
  small_sample :
    ∑ r ∈ Finset.Ico (lm37SourceMinSize d) (lm37SourceCutoff N),
      r * ((((r * degreeIntoU) + 1) *
        (max 1 Ucap) ^ (r * degreeIntoU)) * r ^ 2) ≤ (T + 1) / 2
  degree_upper : d ≤ 128 * (D ^ 2 * lm37SourceCutoff N)
  half : D ^ 3 ≤ N / 2
  deletion_workspace :
    Ucap < lm37SourceLargeBudget D (D ^ 2 * lm37SourceCutoff N)
  small_workspace : ∀ r : ℕ,
    lm37SourceMinSize d ≤ r → r < lm37SourceCutoff N →
      r * degreeIntoU < lm37SourceSmallBudget r (r ^ 3)

private theorem source_small_lower
    {d r : ℕ} (hd : 4096 ≤ d) (hr : lm37SourceMinSize d ≤ r) :
    ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤ ((r ^ 3 : ℕ) : ℝ) := by
  have hdiv : d / 1024 ≤ r :=
    (le_max_right 1 (d / 1024)).trans hr
  have hrlarge : 4 ≤ r := by omega
  have hdround : d ≤ 1024 * r + 1023 := by omega
  have hrSq : 16 ≤ r ^ 2 := by nlinarith
  have hnat : d ≤ 128 * r ^ 3 := by
    calc
      d ≤ 1024 * r + 1023 := hdround
      _ ≤ 2048 * r := by omega
      _ = 128 * r * 16 := by ring
      _ ≤ 128 * r * r ^ 2 := Nat.mul_le_mul_left (128 * r) hrSq
      _ = 128 * r ^ 3 := by ring
  have hreal : (d : ℝ) ≤ 128 * ((r ^ 3 : ℕ) : ℝ) := by
    exact_mod_cast hnat
  norm_num at hreal ⊢
  linarith

/-- In the nontrivial branch, the bootstrap guard bounds `d` by the fixed
slow endpoint.  Thus `D` never has to be enlarged to order `sqrt(d)`. -/
theorem source_degree_upper_of_minSize_lt_target
    {N d M D : ℕ}
    (hsmall : lm37SourceMinSize d < M) (hMD : M ≤ D)
    (hD : 9 ≤ D) (hcut : 0 < lm37SourceCutoff N) :
    d ≤ 128 * (D ^ 2 * lm37SourceCutoff N) := by
  have hdiv : d / 1024 < M :=
    (le_max_right 1 (d / 1024)).trans_lt hsmall
  have hd : d ≤ 1024 * D + 1023 := by omega
  have hcutOne : 1 ≤ lm37SourceCutoff N := hcut
  nlinarith

/-- The actual-size denominator is eventually much smaller than its size. -/
theorem eventually_lm37_small_divisor :
    ∀ᶠ r : ℕ in atTop,
      2048 * lmGrowthDivisor (lm37SourceSmallBudgetOrder r) ≤ r := by
  have hasymp :=
    Parameters.eventually_const_mul_log_pow_le_self (604000000 : ℝ) 2
  have hasympNat := tendsto_natCast_atTop_atTop.eventually hasymp
  filter_upwards [hasympNat, eventually_ge_atTop (960 : ℕ)] with r hasympR hr
  let L : ℝ := Real.log (r : ℝ)
  let B : ℕ := lm37SourceSmallBudgetOrder r
  have hrpos : 0 < r := by omega
  have hB : B = 960 * r ^ 3 := by
    dsimp [B, lm37SourceSmallBudgetOrder]
    rw [max_eq_right]
    have hrpos : 0 < r := by omega
    have hrpowpos : 0 < r ^ 3 := Nat.pow_pos hrpos
    nlinarith
  have hBpos : 0 < B := by rw [hB]; positivity
  have hBupper : B ≤ r ^ 4 := by
    rw [hB]
    calc
      960 * r ^ 3 ≤ r * r ^ 3 := Nat.mul_le_mul_right (r ^ 3) hr
      _ = r ^ 4 := by ring
  have hlogrpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos (by exact_mod_cast (by omega : 1 < r))
  have hLone : 1 ≤ L := by
    have hexp : Real.exp 1 < 3 := Real.exp_one_lt_d9.trans (by norm_num)
    have hthree : (3 : ℝ) ≤ r := by exact_mod_cast (by omega : 3 ≤ r)
    exact (Real.le_log_iff_exp_le (by positivity)).2 (hexp.le.trans hthree)
  have hlogB : Real.log (B : ℝ) ≤ 4 * L := by
    calc
      Real.log (B : ℝ) ≤ Real.log ((r ^ 4 : ℕ) : ℝ) :=
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
  have hreal : ((2048 * lmGrowthDivisor B : ℕ) : ℝ) ≤ (r : ℝ) := by
    push_cast
    calc
      (2048 : ℝ) * lmGrowthDivisor B ≤
          2048 * (294914 * L ^ 2) := by gcongr
      _ ≤ 604000000 * L ^ 2 := by nlinarith [sq_nonneg L]
      _ ≤ (r : ℝ) := by simpa [L] using hasympR
  exact_mod_cast hreal

/-- Consequently the blocked trace `r * (d/2)` fits in one actual-size
budget for every sufficiently large global degree, uniformly in `N`. -/
theorem eventually_lm37_small_workspace :
    ∀ᶠ d : ℕ in atTop, ∀ r : ℕ,
      lm37SourceMinSize d ≤ r →
        r * (d / 2) < lm37SourceSmallBudget r (r ^ 3) := by
  obtain ⟨R, hR⟩ := (eventually_atTop.1 eventually_lm37_small_divisor)
  filter_upwards [eventually_ge_atTop (1024 * R)] with d hd
  intro r hr
  have hRr : R ≤ r := by
    have : R ≤ d / 1024 := by omega
    exact this.trans ((le_max_right 1 (d / 1024)).trans hr)
  have hden := hR r hRr
  let C := lmGrowthDivisor (lm37SourceSmallBudgetOrder r)
  have hCpos : 0 < C := lmGrowthDivisor_pos
    ((lm37SourceSmallBudgetOrder_large r).trans' (by omega))
  have hdiv : 2048 * r ^ 2 ≤ r ^ 3 / C := by
    apply (Nat.le_div_iff_mul_le hCpos).2
    have := Nat.mul_le_mul_right (r ^ 2) hden
    dsimp [C] at this ⊢
    nlinarith
  have hdegree : d ≤ 1024 * r + 1023 := by
    have : d / 1024 ≤ r := (le_max_right 1 (d / 1024)).trans hr
    omega
  have hrpos : 0 < r := by
    have : 0 < lm37SourceMinSize d := lm37SourceMinSize_pos d
    omega
  have hblocked : r * (d / 2) < 2048 * r ^ 2 := by
    have : d / 2 ≤ 512 * r + 511 := by omega
    nlinarith
  exact hblocked.trans_le (by
    simpa [lm37SourceSmallBudget, lmGrowthGain, C] using hdiv)

/-- Build the exact source package.  Its lower, upper, rate, and recurrence
fields are derived from the finite estimates above. -/
noncomputable def concreteLM37SourceBounds
    (N d Ucap Icard contact radius M degreeIntoU D T : ℕ)
    (b : LM37SourceNumericalBounds N d Ucap Icard radius M degreeIntoU D T) :
    LM37SourceBounds N d Ucap Icard contact radius M degreeIntoU D T where
  growth := lm37FirstSlowGrowth
  neighborBudget := lm37SourceNeighborBudget D (lm37SourceCutoff N)
  largeBudget := lm37SourceLargeBudget D
  stepLoss := lm37FirstSlowStepLoss
  cutoff_pos := b.cutoff_pos
  index := b.index
  target_le_D := b.target_le_D
  target_growth := b.target_growth
  jump := by
    intro ell _ _
    simp only [lm37FirstSlowStepLoss]
    omega
  D_pos := b.D_pos
  T_pos := b.T_pos
  large_sample := b.large_sample
  small_sample := b.small_sample
  large_lower := by
    have hreal : (d : ℝ) ≤
        128 * (((D ^ 2 * lm37SourceCutoff N : ℕ) : ℝ)) := by
      exact_mod_cast b.degree_upper
    norm_num at hreal ⊢
    linarith
  large_upper := b.half
  large_rate := by
    intro s hs hS
    have hgain := lm37SourceLargeBudget_mono D hs
    have hstrict : Ucap + lm37SourceLargeBudget D s <
        2 * lm37SourceLargeBudget D s := by
      calc
        Ucap + lm37SourceLargeBudget D s <
            lm37SourceLargeBudget D s + lm37SourceLargeBudget D s :=
          Nat.add_lt_add_right (b.deletion_workspace.trans_le hgain) _
        _ = 2 * lm37SourceLargeBudget D s := by omega
    have hlower : (d : ℝ) / 128 ≤ (s : ℝ) := by
      have hbase : (d : ℝ) / 128 ≤
          ((D ^ 2 * lm37SourceCutoff N : ℕ) : ℝ) := by
        have hreal : (d : ℝ) ≤
            128 * (((D ^ 2 * lm37SourceCutoff N : ℕ) : ℝ)) := by
          exact_mod_cast b.degree_upper
        linarith
      exact hbase.trans (by exact_mod_cast hs)
    exact (by exact_mod_cast hstrict :
      ((Ucap + lm37SourceLargeBudget D s : ℕ) : ℝ) <
        ((2 * lm37SourceLargeBudget D s : ℕ) : ℝ)) |>.trans_le
          (two_lm37SourceLargeBudget_le_expansion
            (b.degree_large.trans' (by omega)) hlower hS)
  small_lower := by
    intro r hr _
    exact source_small_lower b.degree_large hr
  small_upper := by
    intro r _ hcut
    have hrD : r ≤ D := (Nat.le_of_lt hcut).trans b.cutoff_le_D
    exact (Nat.pow_le_pow_left hrD 3).trans b.half
  small_rate := by
    intro r hr hcut
    have hreplicate : r ^ 2 * lm37SourceSmallBudget r r ≤
        lm37SourceSmallBudget r (r ^ 3) := by
      have h := mul_lmGrowthGain_le (lm37SourceSmallBudgetOrder r) (r ^ 2) r
      simpa [lm37SourceSmallBudget, pow_succ] using h
    have hstrict : r * degreeIntoU +
        r ^ 2 * lm37SourceSmallBudget r r <
          2 * lm37SourceSmallBudget r (r ^ 3) := by
      calc
        r * degreeIntoU + r ^ 2 * lm37SourceSmallBudget r r <
            lm37SourceSmallBudget r (r ^ 3) +
              lm37SourceSmallBudget r (r ^ 3) :=
          Nat.add_lt_add_of_lt_of_le (b.small_workspace r hr hcut) hreplicate
        _ = 2 * lm37SourceSmallBudget r (r ^ 3) := by omega
    have hlower := source_small_lower b.degree_large hr
    have hbudgetAtR : lm37SourceNeighborBudget D (lm37SourceCutoff N) r =
        lm37SourceSmallBudget r r := by
      simp [lm37SourceNeighborBudget, hcut]
    rw [hbudgetAtR]
    have hstrictReal :
        ((r * degreeIntoU + r ^ 2 * lm37SourceSmallBudget r r : ℕ) : ℝ) <
          ((2 * lm37SourceSmallBudget r (r ^ 3) : ℕ) : ℝ) := by
      exact_mod_cast hstrict
    exact hstrictReal.trans_le
      (two_lm37SourceSmallBudget_le_expansion
        (b.degree_large.trans' (by omega)) (by
          convert hlower using 1 <;> ring))

/-- Family aggregation is automatic for a package built by the constructor. -/
theorem concreteLM37SourceBounds_largeBudgetSum
    {I : Type*} [DecidableEq I]
    (N d Ucap Icard contact radius M degreeIntoU D T : ℕ)
    (b : LM37SourceNumericalBounds N d Ucap Icard radius M degreeIntoU D T)
    (J : Finset I) (f : I → ℕ)
    (hf : ∀ i ∈ J, lm37SourceCutoff N ≤ f i) :
    ∑ i ∈ J,
        (concreteLM37SourceBounds N d Ucap Icard contact radius M
          degreeIntoU D T b).neighborBudget (f i) ≤
      (concreteLM37SourceBounds N d Ucap Icard contact radius M
        degreeIntoU D T b).largeBudget (∑ i ∈ J, f i) := by
  simp only [concreteLM37SourceBounds, lm37SourceNeighborBudget]
  rw [Finset.sum_congr rfl (fun i hi ↦ if_neg (not_lt.mpr (hf i hi)))]
  exact sum_lm37SourceLargeBudget_le D J f

/-! ## Candidate-local route budgets -/

/-- The remaining geometric estimates for routing from a source slow ball.
They are stated using `Nat.sqrt s`, so they are independent of the ambient
maximum candidate radius.  Any particular candidate end of radius `m` is
contained in a slow ball of order `s`, hence supplies `m² ≤ s` and therefore
`m ≤ sqrt s`.

This package is intentionally separate from `LM37SourceNumericalBounds`:
the latter is exactly what is needed to construct `LM37SourceBounds`, while
these two inequalities discharge the candidate-local path costs in Claims
4.5, 4.6, and the final two-ended call. -/
structure LM37SourceGeometricBounds (N d minRadius radius D : ℕ) : Prop where
  reach : ∀ ell s, minRadius ^ 2 ≤ s → 0 < ell → ell ≤ radius →
    lm37FirstSlowGrowth (ell - 1) < s →
    lm37FirstSlowStepLoss ell + (11 * Nat.sqrt s + 1) + 2 * ell ≤
      lm37SourceNeighborBudget D (lm37SourceCutoff N) s
  final : ∀ ell s, minRadius ^ 2 ≤ s → 0 < ell → ell ≤ radius →
    lm37FirstSlowGrowth (ell - 1) < s →
    lm37FirstSlowStepLoss ell + 10 * Nat.sqrt s ≤
      lm37SourceNeighborBudget D (lm37SourceCutoff N) s

/-- The exact Claim 4.5/4.6 neighbor inequality with the actual candidate
radius.  The only geometric input is `candidateRadius² ≤ s`; no ambient
`maxRadius` occurs. -/
theorem lm37Source_reach_neighbor_of_radius_sq_le
    {N d minRadius radius D ell s candidateRadius : ℕ}
    (g : LM37SourceGeometricBounds N d minRadius radius D)
    (hminCandidate : minRadius ≤ candidateRadius)
    (hell : 0 < ell) (hellRadius : ell ≤ radius)
    (hslow : lm37FirstSlowGrowth (ell - 1) < s)
    (hcandidate : candidateRadius ^ 2 ≤ s) :
    lm37FirstSlowStepLoss ell + (11 * candidateRadius + 1) + 2 * ell ≤
      lm37SourceNeighborBudget D (lm37SourceCutoff N) s := by
  have hrSqrt : candidateRadius ≤ Nat.sqrt s := by
    apply Nat.le_sqrt.mpr
    simpa [pow_two] using hcandidate
  have hminSq : minRadius ^ 2 ≤ s :=
    (Nat.pow_le_pow_left hminCandidate 2).trans hcandidate
  exact (by
    have h := g.reach ell s hminSq hell hellRadius hslow
    omega)

/-- Candidate-local form of the final two-ended route inequality. -/
theorem lm37Source_final_neighbor_of_radius_sq_le
    {N d minRadius radius D ell s candidateRadius : ℕ}
    (g : LM37SourceGeometricBounds N d minRadius radius D)
    (hminCandidate : minRadius ≤ candidateRadius)
    (hell : 0 < ell) (hellRadius : ell ≤ radius)
    (hslow : lm37FirstSlowGrowth (ell - 1) < s)
    (hcandidate : candidateRadius ^ 2 ≤ s) :
    lm37FirstSlowStepLoss ell + 10 * candidateRadius ≤
      lm37SourceNeighborBudget D (lm37SourceCutoff N) s := by
  have hrSqrt : candidateRadius ≤ Nat.sqrt s := by
    apply Nat.le_sqrt.mpr
    simpa [pow_two] using hcandidate
  have hminSq : minRadius ^ 2 ≤ s :=
    (Nat.pow_le_pow_left hminCandidate 2).trans hcandidate
  exact (by
    have h := g.final ell s hminSq hell hellRadius hslow
    omega)

/-! ## Radius-one retained-size dichotomies -/

/-- For large degree, every candidate radius supplies the source lower size
in one of the two honest ways: either its end already has enough vertices,
or deleting the local route costs from half the minimum degree still leaves
the required radius-one bootstrap size. -/
theorem lm37SourceMinSize_le_sq_or_reach_retained
    {d candidateRadius : ℕ} (hd : 2 ^ 20 ≤ d) :
    lm37SourceMinSize d ≤ candidateRadius ^ 2 ∨
      lm37SourceMinSize d ≤
        d - d / 2 - (11 * candidateRadius + 1) - 2 := by
  let q := d / 1024
  have hqPos : 1 ≤ q := by dsimp [q]; omega
  have hmin : lm37SourceMinSize d = q := by
    simp [lm37SourceMinSize, SourceLemma35Numerics.minFailedSize, q, hqPos]
  rw [hmin]
  by_cases hsquare : q ≤ candidateRadius ^ 2
  · exact Or.inl hsquare
  · right
    have hqMul : q * 1024 ≤ d := by
      simpa [q] using Nat.div_mul_le_self d 1024
    have hrMul : (candidateRadius ^ 2 + 1) * 1024 ≤ d := by
      have : candidateRadius ^ 2 + 1 ≤ q := by omega
      exact (Nat.mul_le_mul_right 1024 this).trans (by
        simpa [mul_comm] using hqMul)
    have hqFour : 4 * q ≤ d := by
      calc
        4 * q ≤ 1024 * q := by nlinarith
        _ ≤ d := by simpa [mul_comm] using hqMul
    have hcostFour : 4 * (11 * candidateRadius + 3) ≤ d := by
      have hrle : candidateRadius ≤ candidateRadius ^ 2 + 1 := by
        nlinarith
      calc
        4 * (11 * candidateRadius + 3) ≤
            44 * (candidateRadius ^ 2 + 1) + 12 := by nlinarith
        _ ≤ 1024 * (candidateRadius ^ 2 + 1) := by nlinarith
        _ ≤ d := by simpa [mul_comm] using hrMul
    have htwice : 2 * (q + (11 * candidateRadius + 3)) ≤ d := by
      nlinarith
    omega

/-- Final two-ended version.  Its degree loss is smaller, while the seed has
twice the candidate end order. -/
theorem lm37SourceMinSize_le_two_sq_or_final_retained
    {d candidateRadius : ℕ} (hd : 2 ^ 20 ≤ d) :
    lm37SourceMinSize d ≤ 2 * candidateRadius ^ 2 ∨
      lm37SourceMinSize d ≤ d - d / 2 - 10 * candidateRadius := by
  rcases lm37SourceMinSize_le_sq_or_reach_retained
      (d := d) (candidateRadius := candidateRadius) hd with hsquare | hdegree
  · exact Or.inl (hsquare.trans (Nat.le_mul_of_pos_left _ (by omega)))
  · exact Or.inr (hdegree.trans (by omega))

/-- A source numerical certificate together with its candidate-local route
estimates. -/
structure LM37RoutedSourceNumericalBounds
    (N d Ucap Icard minRadius radius M degreeIntoU D T : ℕ) : Prop where
  source : LM37SourceNumericalBounds N d Ucap Icard radius M degreeIntoU D T
  geometry : LM37SourceGeometricBounds N d minRadius radius D

/-- Routed numerical bounds construct the same exact source package; their
additional geometry is consumed by the robust scalar wrapper. -/
noncomputable def concreteLM37RoutedSourceBounds
    (N d Ucap Icard contact minRadius radius M degreeIntoU D T : ℕ)
    (b : LM37RoutedSourceNumericalBounds N d Ucap Icard minRadius radius M
      degreeIntoU D T) :
    LM37SourceBounds N d Ucap Icard contact radius M degreeIntoU D T :=
  concreteLM37SourceBounds N d Ucap Icard contact radius M degreeIntoU D T
    b.source

/-- Eventual finite estimates give eventual exact source packages. -/
theorem eventually_concreteLM37SourceBounds
    (d Ucap Icard contact radius M degreeIntoU D T : ℕ → ℕ)
    (hb : ∀ᶠ N : ℕ in atTop,
      LM37SourceNumericalBounds N (d N) (Ucap N) (Icard N) (radius N)
        (M N) (degreeIntoU N) (D N) (T N)) :
    ∀ᶠ N : ℕ in atTop,
      Nonempty (LM37SourceBounds N (d N) (Ucap N) (Icard N) (contact N)
        (radius N) (M N) (degreeIntoU N) (D N) (T N)) := by
  filter_upwards [hb] with N hN
  exact ⟨concreteLM37SourceBounds N (d N) (Ucap N) (Icard N)
    (contact N) (radius N) (M N) (degreeIntoU N) (D N) (T N) hN⟩

/-- Honest eventual wrapper for the routed source package.  All
large-sample, small-workspace, and candidate-local geometric restrictions
remain visible in the hypothesis; the theorem introduces no uniformity that
is false for the literal `D²` sample. -/
theorem eventually_concreteLM37RoutedSourceBounds
    (d Ucap Icard contact minRadius radius M degreeIntoU D T : ℕ → ℕ)
    (hb : ∀ᶠ N : ℕ in atTop,
      LM37RoutedSourceNumericalBounds N (d N) (Ucap N) (Icard N)
        (minRadius N) (radius N) (M N) (degreeIntoU N) (D N) (T N)) :
    ∀ᶠ N : ℕ in atTop,
      Nonempty (LM37SourceBounds N (d N) (Ucap N) (Icard N) (contact N)
        (radius N) (M N) (degreeIntoU N) (D N) (T N)) := by
  filter_upwards [hb] with N hN
  exact ⟨concreteLM37RoutedSourceBounds N (d N) (Ucap N) (Icard N)
    (contact N) (minRadius N) (radius N) (M N) (degreeIntoU N) (D N) (T N)
    hN⟩

/-- Conditional form used by robust Lemma 4.3.  If the radius-one bootstrap
already has size at least `M`, no Lemma 3.7 package is needed.  Only the
complementary branch `minSize < M` constructs the source bounds; in
particular, this guard supplies the required upper-degree estimate without
ever enlarging `D` as a function of `d`. -/
theorem eventually_concreteLM37SourceBounds_of_minSize_lt
    (d Ucap Icard contact radius M degreeIntoU D T : ℕ → ℕ)
    (hb : ∀ᶠ N : ℕ in atTop,
      lm37SourceMinSize (d N) < M N →
        LM37SourceNumericalBounds N (d N) (Ucap N) (Icard N) (radius N)
          (M N) (degreeIntoU N) (D N) (T N)) :
    ∀ᶠ N : ℕ in atTop,
      lm37SourceMinSize (d N) < M N →
        Nonempty (LM37SourceBounds N (d N) (Ucap N) (Icard N) (contact N)
          (radius N) (M N) (degreeIntoU N) (D N) (T N)) := by
  filter_upwards [hb] with N hN hsmall
  exact ⟨concreteLM37SourceBounds N (d N) (Ucap N) (Icard N)
    (contact N) (radius N) (M N) (degreeIntoU N) (D N) (T N) (hN hsmall)⟩

end Erdos63
