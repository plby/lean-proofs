/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
Copyright (c) 2026 Boris Alexeev. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/

import ErdosProblems.Erdos63.AdjusterBase
import ErdosProblems.Erdos63.Claim44Numerics
import ErdosProblems.Erdos63.GrowthSchedule
import ErdosProblems.Erdos63.SourceLemma37

/-!
# Numerical scales for Liu--Montgomery Claims 4.5 and 4.6

This file is deliberately graph-free.  It supplies a concrete specialization
of the size-correlated Lemma 3.7 package used twice in the proof of Lemma 4.3.
The specialization is useful whenever the radius-one seed is already above
the expander cutoff.  In that regime the small-set sampling interval is empty,
so the very expensive contact-trace sum disappears completely.

The remaining large-set profile is the same one used throughout the project:
`s / (2 * ceil (9216 * log(N)^2))`.  Its floor is superadditive, which also
discharges the family-dependent `largeBudgetSum` premise in Claims 4.5 and
4.6.
-/

open Finset Set SimpleGraph
open scoped BigOperators SimpleGraph

namespace Erdos63

attribute [local instance] Classical.propDecidable Classical.decEq

/-! ## Superadditivity of the canonical gain -/

/-- Natural division is superadditive in its numerator. -/
theorem sum_div_le_div_sum {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ) (q : ℕ) :
    ∑ i ∈ J, f i / q ≤ (∑ i ∈ J, f i) / q := by
  classical
  induction J using Finset.induction_on with
  | empty => simp
  | @insert a J ha ih =>
      simp only [sum_insert, ha, not_false_eq_true]
      calc
        f a / q + ∑ i ∈ J, f i / q ≤
            f a / q + (∑ i ∈ J, f i) / q := Nat.add_le_add_left ih _
        _ ≤ (f a + ∑ i ∈ J, f i) / q :=
          Nat.div_add_div_le_add_div

/-- The canonical Liu--Montgomery gain is superadditive over a finite family. -/
theorem sum_lmGrowthGain_le_lmGrowthGain_sum {I : Type*} [DecidableEq I]
    (N : ℕ) (J : Finset I) (f : I → ℕ) :
    ∑ i ∈ J, lmGrowthGain N (f i) ≤
      lmGrowthGain N (∑ i ∈ J, f i) := by
  simpa only [lmGrowthGain] using
    sum_div_le_div_sum J f (lmGrowthDivisor N)

/-! ## The large-only correlated scale -/

/-- The one-step loss of the canonical multiplicative comparison curve. -/
noncomputable def lm37StepLoss (N cutoff : ℕ) (ell : ℕ) : ℕ :=
  lmGrowthGain N (lmGrowthCurve N cutoff (ell - 1))

/-! ## A flexible canonical-curve constructor -/

/-- Named arithmetic obligations for a correlated Lemma 3.7 scale using the
canonical multiplicative curve.  Unlike `LM37CorrelatedScale`, this structure
does not ask the caller to prove the recurrence jump: it is forced by
`lmGrowthCurve` and discharged by `concreteLM37CanonicalScale` below.

Keeping the sampling and rate estimates as fields is useful for the full
Claims 4.5/4.6 regime, where the interval `minSize ≤ r < cutoff` can be
nonempty and its contact-trace sum is handled by a separate eventual estimate.
-/
structure LM37CanonicalBounds
    (N d Ucap Icard radius M degreeIntoU minSize cutoff D T qLarge : ℕ)
    (qSmall neighborBudget blockedBudget largeBudget : ℕ → ℕ) : Prop where
  index : T ≤ Icard
  target_le_D : M ≤ D
  target_growth : M ≤ lmGrowthCurve N minSize radius
  blocked_profile : ∀ s, minSize ≤ s → s < cutoff →
    s * degreeIntoU ≤ blockedBudget s
  minSize_pos : 0 < minSize
  cutoff_pos : 0 < cutoff
  D_pos : 0 < D
  T_pos : 0 < T
  qSmall_pos : ∀ r, minSize ≤ r → r < cutoff → 0 < qSmall r
  large_sample : qLarge * D ≤ (T + 1) / 2
  small_sample :
    ∑ r ∈ Finset.Ico minSize cutoff,
      r * (((blockedBudget r + 1) * (max 1 Ucap) ^ blockedBudget r) *
        qSmall r) ≤ (T + 1) / 2
  large_lower : ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤
    ((qLarge * cutoff : ℕ) : ℝ)
  large_upper : ((qLarge * D : ℕ) : ℝ) ≤ (N : ℝ) / 2
  large_rate : ∀ s, qLarge * cutoff ≤ s → s ≤ qLarge * D →
    (((Ucap + largeBudget s : ℕ) : ℝ) <
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  small_lower : ∀ r, minSize ≤ r → r < cutoff →
    ((1 / 64 : ℝ) * (d : ℝ)) / 2 ≤
      ((qSmall r * r : ℕ) : ℝ)
  small_upper : ∀ r, minSize ≤ r → r < cutoff →
    ((qSmall r * r : ℕ) : ℝ) ≤ (N : ℝ) / 2
  small_rate : ∀ r, minSize ≤ r → r < cutoff →
    (((blockedBudget r + qSmall r * neighborBudget r : ℕ) : ℝ) <
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ))
        (qSmall r * r) * ((qSmall r * r : ℕ) : ℝ))

/-- Turn the named full-regime numerical obligations into the exact scale
consumed by the candidate-indexed Claims 4.5 and 4.6. -/
noncomputable def concreteLM37CanonicalScale
    (N d Ucap Icard contact radius M degreeIntoU minSize cutoff D T qLarge : ℕ)
    (qSmall neighborBudget blockedBudget largeBudget : ℕ → ℕ)
    (b : LM37CanonicalBounds N d Ucap Icard radius M degreeIntoU
      minSize cutoff D T qLarge qSmall neighborBudget blockedBudget largeBudget) :
    LM37CorrelatedScale N Ucap Icard contact radius M degreeIntoU
      (1 / 1024) ((1 / 64) * (d : ℝ)) where
  growth := lmGrowthCurve N minSize
  minSize := minSize
  cutoff := cutoff
  D := D
  T := T
  qLarge := qLarge
  qSmall := qSmall
  neighborBudget := neighborBudget
  blockedBudget := blockedBudget
  largeBudget := largeBudget
  stepLoss := lm37StepLoss N minSize
  index := b.index
  target_le_D := b.target_le_D
  target_growth := b.target_growth
  jump := by
    intro ell hell _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
    simp [lm37StepLoss, Nat.succ_eq_add_one]
  blocked_profile := b.blocked_profile
  minSize_pos := b.minSize_pos
  cutoff_pos := b.cutoff_pos
  D_pos := b.D_pos
  T_pos := b.T_pos
  qSmall_pos := b.qSmall_pos
  large_sample := b.large_sample
  small_sample := b.small_sample
  large_lower := b.large_lower
  large_upper := b.large_upper
  large_rate := b.large_rate
  small_lower := b.small_lower
  small_upper := b.small_upper
  small_rate := b.small_rate

/-! ## The source small/large split -/

/-- Number of copies of an `r`-vertex slow ball needed to reach the expander
cutoff `d/128`.  The outer maximum makes the profile positive even when
`d = 0`; the applications use `d ≥ 1`. -/
noncomputable def lm37SampleMultiplicity (d r : ℕ) : ℕ :=
  max 1 ⌈(d : ℝ) / (128 * (r : ℝ))⌉₊

theorem lm37SampleMultiplicity_pos (d r : ℕ) :
    0 < lm37SampleMultiplicity d r := by
  simp [lm37SampleMultiplicity]

/-- By construction, the replicated slow ball reaches `d/128`. -/
theorem lm37SampleMultiplicity_lower {d r : ℕ} (hr : 0 < r) :
    (d : ℝ) / 128 ≤ ((lm37SampleMultiplicity d r * r : ℕ) : ℝ) := by
  have hrreal : (0 : ℝ) < (r : ℝ) := by exact_mod_cast hr
  have hceil : (d : ℝ) / (128 * (r : ℝ)) ≤
      (⌈(d : ℝ) / (128 * (r : ℝ))⌉₊ : ℝ) := Nat.le_ceil _
  have hmaxNat : ⌈(d : ℝ) / (128 * (r : ℝ))⌉₊ ≤
      lm37SampleMultiplicity d r := le_max_right _ _
  have hmax : (⌈(d : ℝ) / (128 * (r : ℝ))⌉₊ : ℝ) ≤
      (lm37SampleMultiplicity d r : ℝ) := by exact_mod_cast hmaxNat
  calc
    (d : ℝ) / 128 = ((d : ℝ) / (128 * (r : ℝ))) * r := by
      field_simp [ne_of_gt hrreal]
      <;> ring
    _ ≤ (lm37SampleMultiplicity d r : ℝ) * r := by
      gcongr
      exact hceil.trans hmax
    _ = ((lm37SampleMultiplicity d r * r : ℕ) : ℝ) := by
      norm_num

/-- A deliberately slower gain for the correlated source split.  Relative to
`lmGrowthGain`, another factor four is reserved: one copy pays for the actual
ball jump, one for its geometric barrier, and six remain for blocked/deleted
vertices after replication. -/
noncomputable def lm37SourceGain (N s : ℕ) : ℕ :=
  s / (4 * lmGrowthDivisor N)

noncomputable def lm37SourceCurve (N D : ℕ) : ℕ → ℕ
  | 0 => D
  | i + 1 => lm37SourceCurve N D i + lm37SourceGain N (lm37SourceCurve N D i)

noncomputable def lm37SourceStepLoss (N D ell : ℕ) : ℕ :=
  lm37SourceGain N (lm37SourceCurve N D (ell - 1))

theorem lm37SourceGain_mono (N : ℕ) : Monotone (lm37SourceGain N) := by
  intro a b hab
  exact Nat.div_le_div_right hab

theorem lm37SourceCurve_start_le (N D i : ℕ) :
    D ≤ lm37SourceCurve N D i := by
  induction i with
  | zero => exact le_rfl
  | succ i ih =>
      exact ih.trans (Nat.le_add_right _ _)

/-- A second slow gain pays for the candidate core and limited-contact path
once the first gain has paid for the comparison-curve jump.  This is the
pointwise inequality needed by the `hneighbor` premise of Claims 4.5/4.6. -/
theorem lm37SourceStepLoss_add_cost_le_neighbor
    {N D ell s cost : ℕ}
    (hslow : lm37SourceCurve N D (ell - 1) < s)
    (hcost : cost ≤ lm37SourceGain N s) :
    lm37SourceStepLoss N D ell + cost ≤ 2 * lm37SourceGain N s := by
  have hstep : lm37SourceStepLoss N D ell ≤ lm37SourceGain N s := by
    exact lm37SourceGain_mono N (Nat.le_of_lt hslow)
  omega

/-- Eight slow gains fit inside the fixed Liu--Montgomery expansion profile. -/
theorem eight_lm37SourceGain_le_expansion
    {N d s : ℕ} (hN : 32 ≤ N) (hd : 1 ≤ d)
    (hcutoff : (d : ℝ) / 128 ≤ (s : ℝ)) (hsN : s ≤ N) :
    (((8 * lm37SourceGain N s : ℕ) : ℝ)) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ) := by
  have hdiv : 0 < lmGrowthDivisor N :=
    lmGrowthDivisor_pos (hN.trans' (by omega))
  have hfour : 4 * lm37SourceGain N s ≤ lmGrowthGain N s := by
    apply (Nat.le_div_iff_mul_le hdiv).2
    change 4 * (s / (4 * lmGrowthDivisor N)) * lmGrowthDivisor N ≤ s
    calc
      4 * (s / (4 * lmGrowthDivisor N)) * lmGrowthDivisor N =
          (s / (4 * lmGrowthDivisor N)) * (4 * lmGrowthDivisor N) := by ring
      _ ≤ s := Nat.div_mul_le_self _ _
  have height : 8 * lm37SourceGain N s ≤ 2 * lmGrowthGain N s := by omega
  have hcast : (((8 * lm37SourceGain N s : ℕ) : ℝ)) ≤
      (((2 * lmGrowthGain N s : ℕ) : ℝ)) := by exact_mod_cast height
  exact hcast.trans
    (two_lmGrowthGain_le_expansion hN hd hcutoff hsN)

theorem sum_lm37SourceGain_le_lm37SourceGain_sum
    {I : Type*} [DecidableEq I] (N : ℕ) (J : Finset I) (f : I → ℕ) :
    ∑ i ∈ J, lm37SourceGain N (f i) ≤
      lm37SourceGain N (∑ i ∈ J, f i) := by
  simpa only [lm37SourceGain] using
    sum_div_le_div_sum J f (4 * lmGrowthDivisor N)

/-- The genuinely nonempty-small-range arithmetic remaining in the source
split.  Every field is a finite numerical inequality.  In particular, no
graph, path, expansion, or candidate occurs here.

The workspace hypotheses are deliberately stated before coercion to `ℝ`.
The constructor reserves two canonical gains at the replicated size; the
fixed deletion (large case), or the blocked trace plus replicated available
neighborhood (small case), must fit strictly below those gains. -/
structure LM37SourceSplitBounds
    (N d Ucap Icard radius M degreeIntoU minSize cutoff D T : ℕ) : Prop where
  card_large : 32 ≤ N
  degree_pos : 1 ≤ d
  index : T ≤ Icard
  target_le_D : M ≤ D
  target_growth : M ≤ lm37SourceCurve N minSize radius
  minSize_pos : 0 < minSize
  cutoff_pos : 0 < cutoff
  D_pos : 0 < D
  T_pos : 0 < T
  large_sample : lm37SampleMultiplicity d cutoff * D ≤ (T + 1) / 2
  small_sample :
    ∑ r ∈ Finset.Ico minSize cutoff,
      r * ((((r * degreeIntoU) + 1) * (max 1 Ucap) ^ (r * degreeIntoU)) *
        lm37SampleMultiplicity d r) ≤ (T + 1) / 2
  large_upper : lm37SampleMultiplicity d cutoff * D ≤ N / 2
  deletion_workspace :
    Ucap < 6 * lm37SourceGain N (lm37SampleMultiplicity d cutoff * cutoff)
  small_upper : ∀ r, minSize ≤ r → r < cutoff →
    lm37SampleMultiplicity d r * r ≤ N / 2
  small_workspace : ∀ r, minSize ≤ r → r < cutoff →
    r * degreeIntoU +
        lm37SampleMultiplicity d r * (2 * lm37SourceGain N r) <
      8 * lm37SourceGain N (lm37SampleMultiplicity d r * r)

/-- Concrete nonempty-small-range scale matching the two cases in the source
proof of Lemma 3.7. -/
noncomputable def concreteLM37SourceSplitScale
    (N d Ucap Icard contact radius M degreeIntoU minSize cutoff D T : ℕ)
    (b : LM37SourceSplitBounds N d Ucap Icard radius M degreeIntoU
      minSize cutoff D T) :
    LM37CorrelatedScale N Ucap Icard contact radius M degreeIntoU
      (1 / 1024) ((1 / 64) * (d : ℝ)) where
  growth := lm37SourceCurve N minSize
  minSize := minSize
  cutoff := cutoff
  D := D
  T := T
  qLarge := lm37SampleMultiplicity d cutoff
  qSmall := lm37SampleMultiplicity d
  neighborBudget := fun r ↦ 2 * lm37SourceGain N r
  blockedBudget := fun r ↦ r * degreeIntoU
  largeBudget := fun r ↦ 2 * lm37SourceGain N r
  stepLoss := lm37SourceStepLoss N minSize
  index := b.index
  target_le_D := b.target_le_D
  target_growth := b.target_growth
  jump := by
    intro ell hell _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
    simp [lm37SourceCurve, lm37SourceStepLoss, Nat.succ_eq_add_one]
  blocked_profile := by
    intro s _ _
    exact le_rfl
  minSize_pos := b.minSize_pos
  cutoff_pos := b.cutoff_pos
  D_pos := b.D_pos
  T_pos := b.T_pos
  qSmall_pos := by
    intro r _ _
    exact lm37SampleMultiplicity_pos d r
  large_sample := b.large_sample
  small_sample := b.small_sample
  large_lower := by
    convert lm37SampleMultiplicity_lower (d := d) b.cutoff_pos using 1 <;>
      norm_num <;> ring
  large_upper := by
    have hcast : ((lm37SampleMultiplicity d cutoff * D : ℕ) : ℝ) ≤
        ((N / 2 : ℕ) : ℝ) := by exact_mod_cast b.large_upper
    exact hcast.trans (by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := 2)))
  large_rate := by
    intro s hs hS
    let q := lm37SampleMultiplicity d cutoff
    have hbase : q * cutoff ≤ s := by simpa only [q] using hs
    have hgain : lm37SourceGain N (q * cutoff) ≤ lm37SourceGain N s :=
      lm37SourceGain_mono N hbase
    have hstrict : Ucap + 2 * lm37SourceGain N s <
        8 * lm37SourceGain N s := by
      calc
        Ucap + 2 * lm37SourceGain N s <
            6 * lm37SourceGain N s + 2 * lm37SourceGain N s :=
          Nat.add_lt_add_right (b.deletion_workspace.trans_le
            (Nat.mul_le_mul_left 6 (by simpa only [q] using hgain))) _
        _ = 8 * lm37SourceGain N s := by omega
    have hcast : (((Ucap + 2 * lm37SourceGain N s : ℕ) : ℝ)) <
        (((8 * lm37SourceGain N s : ℕ) : ℝ)) := by exact_mod_cast hstrict
    have hcutoff : (d : ℝ) / 128 ≤ (s : ℝ) :=
      (lm37SampleMultiplicity_lower (d := d) b.cutoff_pos).trans
        (by exact_mod_cast hbase)
    have hsN : s ≤ N := by
      exact hS.trans (b.large_upper.trans (Nat.div_le_self N 2))
    exact hcast.trans_le
      (eight_lm37SourceGain_le_expansion b.card_large b.degree_pos hcutoff hsN)
  small_lower := by
    intro r hr _
    convert lm37SampleMultiplicity_lower (d := d)
      (b.minSize_pos.trans_le hr) using 1 <;> norm_num <;> ring
  small_upper := by
    intro r hr hcut
    have hcast : ((lm37SampleMultiplicity d r * r : ℕ) : ℝ) ≤
        ((N / 2 : ℕ) : ℝ) := by exact_mod_cast b.small_upper r hr hcut
    exact hcast.trans (by
      simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := 2)))
  small_rate := by
    intro r hr hcut
    have hwork := b.small_workspace r hr hcut
    have hcast :
        (((r * degreeIntoU + lm37SampleMultiplicity d r *
            (2 * lm37SourceGain N r) : ℕ) : ℝ)) <
          (((8 * lm37SourceGain N (lm37SampleMultiplicity d r * r) : ℕ) : ℝ)) := by
      exact_mod_cast hwork
    have hrpos : 0 < r := b.minSize_pos.trans_le hr
    have hcutoff := lm37SampleMultiplicity_lower (d := d) hrpos
    have hsN : lm37SampleMultiplicity d r * r ≤ N :=
      (b.small_upper r hr hcut).trans (Nat.div_le_self N 2)
    exact hcast.trans_le (eight_lm37SourceGain_le_expansion
      b.card_large b.degree_pos hcutoff hsN)

/-- The large-family aggregation premise is automatic for the source-split
scale as well. -/
theorem concreteLM37SourceSplitScale_largeBudgetSum
    {I : Type*} [DecidableEq I]
    (N d Ucap Icard contact radius M degreeIntoU minSize cutoff D T : ℕ)
    (b : LM37SourceSplitBounds N d Ucap Icard radius M degreeIntoU
      minSize cutoff D T)
    (J : Finset I) (f : I → ℕ) :
    ∑ i ∈ J,
        (concreteLM37SourceSplitScale N d Ucap Icard contact radius M
          degreeIntoU minSize cutoff D T b).neighborBudget (f i) ≤
      (concreteLM37SourceSplitScale N d Ucap Icard contact radius M
        degreeIntoU minSize cutoff D T b).largeBudget (∑ i ∈ J, f i) := by
  change ∑ i ∈ J, 2 * lm37SourceGain N (f i) ≤
    2 * lm37SourceGain N (∑ i ∈ J, f i)
  rw [← Finset.mul_sum]
  exact Nat.mul_le_mul_left 2 (sum_lm37SourceGain_le_lm37SourceGain_sum N J f)

/-- Eventual source-split bounds give eventual exact correlated scales. -/
theorem eventually_concreteLM37SourceSplitScale
    (d Ucap Icard contact radius M degreeIntoU minSize cutoff D T : ℕ → ℕ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop,
      LM37SourceSplitBounds n (d n) (Ucap n) (Icard n) (radius n)
        (M n) (degreeIntoU n) (minSize n) (cutoff n) (D n) (T n)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Nonempty (LM37CorrelatedScale n (Ucap n) (Icard n) (contact n)
        (radius n) (M n) (degreeIntoU n) (1 / 1024)
          ((1 / 64) * (d n : ℝ))) := by
  filter_upwards [hb] with n hn
  exact ⟨concreteLM37SourceSplitScale n (d n) (Ucap n) (Icard n)
    (contact n) (radius n) (M n) (degreeIntoU n) (minSize n) (cutoff n)
      (D n) (T n) hn⟩

/-- Pure arithmetic assumptions for the large-only specialization of
`LM37CorrelatedScale`.

`cutoff` is also used as `minSize`.  Thus all fields quantified over
`minSize ≤ r < cutoff` are vacuous.  The strict workspace inequality says
that one canonical gain pays for the fixed deletion, leaving a second gain
for the available neighborhood. -/
structure LM37LargeOnlyBounds
    (N d Ucap Icard radius M D cutoff : ℕ) : Prop where
  card_large : 32 ≤ N
  degree_pos : 1 ≤ d
  cutoff_pos : 0 < cutoff
  index_pos : 0 < Icard
  D_pos : 0 < D
  target_le_D : M ≤ D
  target_growth : M ≤ lmGrowthCurve N cutoff radius
  cutoff_above_expander : (d : ℝ) / 128 ≤ (cutoff : ℝ)
  deletion_lt_gain : Ucap < lmGrowthGain N cutoff
  sample : D ≤ (Icard + 1) / 2
  half : D ≤ N / 2

/-- The concrete graph-free correlated scale for Claims 4.5 and 4.6.

The parameters `contact` and `degreeIntoU` occur in the downstream geometric
application, but disappear from this specialization because the small-size
range is empty. -/
noncomputable def concreteLM37LargeOnlyScale
    (N d Ucap Icard contact radius M degreeIntoU D cutoff : ℕ)
    (b : LM37LargeOnlyBounds N d Ucap Icard radius M D cutoff) :
    LM37CorrelatedScale N Ucap Icard contact radius M degreeIntoU
      (1 / 1024) ((1 / 64) * (d : ℝ)) where
  growth := lmGrowthCurve N cutoff
  minSize := cutoff
  cutoff := cutoff
  D := D
  T := Icard
  qLarge := 1
  qSmall := fun _ ↦ 1
  neighborBudget := lmGrowthGain N
  blockedBudget := fun _ ↦ 0
  largeBudget := lmGrowthGain N
  stepLoss := lm37StepLoss N cutoff
  index := le_rfl
  target_le_D := b.target_le_D
  target_growth := b.target_growth
  jump := by
    intro ell hell _
    obtain ⟨j, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : ell ≠ 0)
    simp [lm37StepLoss, Nat.succ_eq_add_one]
  blocked_profile := by
    intro s hs hscutoff
    omega
  minSize_pos := b.cutoff_pos
  cutoff_pos := b.cutoff_pos
  D_pos := b.D_pos
  T_pos := b.index_pos
  qSmall_pos := by simp
  large_sample := by simpa using b.sample
  small_sample := by simp
  large_lower := by
    convert b.cutoff_above_expander using 1 <;> norm_num <;> ring
  large_upper := by
    have hnat : D ≤ N / 2 := b.half
    have hcast : (D : ℝ) ≤ (N / 2 : ℕ) := by exact_mod_cast hnat
    calc
      (((1 * D : ℕ) : ℝ)) = (D : ℝ) := by simp
      _ ≤ (N / 2 : ℕ) := hcast
      _ ≤ (N : ℝ) / 2 := by
        simpa using (Nat.cast_div_le (α := ℝ) (m := N) (n := 2))
  large_rate := by
    intro s hs hS
    simp only [one_mul] at hs hS
    have hcutoff : cutoff ≤ s := hs
    have hgain : lmGrowthGain N cutoff ≤ lmGrowthGain N s :=
      lmGrowthGain_mono N hcutoff
    have hstrict : Ucap + lmGrowthGain N s < 2 * lmGrowthGain N s := by
      calc
        Ucap + lmGrowthGain N s <
            lmGrowthGain N s + lmGrowthGain N s :=
          Nat.add_lt_add_right (b.deletion_lt_gain.trans_le hgain) _
        _ = 2 * lmGrowthGain N s := by omega
    have hcast : (((Ucap + lmGrowthGain N s : ℕ) : ℝ)) <
        (((2 * lmGrowthGain N s : ℕ) : ℝ)) := by
      exact_mod_cast hstrict
    exact hcast.trans_le <| two_lmGrowthGain_le_expansion
      b.card_large b.degree_pos
        (b.cutoff_above_expander.trans (by exact_mod_cast hcutoff))
        (hS.trans (b.half.trans (Nat.div_le_self N 2)))
  small_lower := by
    intro r hr hrcutoff
    omega
  small_upper := by
    intro r hr hrcutoff
    omega
  small_rate := by
    intro r hr hrcutoff
    omega

/-- The family-dependent budget premise in both Claim 4.5 and Claim 4.6 is
automatic for `concreteLM37LargeOnlyScale`. -/
theorem concreteLM37LargeOnlyScale_largeBudgetSum
    {I : Type*} [DecidableEq I]
    (N d Ucap Icard contact radius M degreeIntoU D cutoff : ℕ)
    (b : LM37LargeOnlyBounds N d Ucap Icard radius M D cutoff)
    (J : Finset I) (f : I → ℕ) :
    ∑ i ∈ J,
        (concreteLM37LargeOnlyScale N d Ucap Icard contact radius M
          degreeIntoU D cutoff b).neighborBudget (f i) ≤
      (concreteLM37LargeOnlyScale N d Ucap Icard contact radius M
        degreeIntoU D cutoff b).largeBudget (∑ i ∈ J, f i) := by
  change ∑ i ∈ J, lmGrowthGain N (f i) ≤
    lmGrowthGain N (∑ i ∈ J, f i)
  exact sum_lmGrowthGain_le_lmGrowthGain_sum N J f

/-- Eventual bounds immediately give an eventual concrete correlated scale.
This is the form used when all parameters are functions of the ambient graph
order. -/
theorem eventually_concreteLM37LargeOnlyScale
    (d Ucap Icard contact radius M degreeIntoU D cutoff : ℕ → ℕ)
    (hb : ∀ᶠ n : ℕ in Filter.atTop,
      LM37LargeOnlyBounds n (d n) (Ucap n) (Icard n) (radius n)
        (M n) (D n) (cutoff n)) :
    ∀ᶠ n : ℕ in Filter.atTop,
      Nonempty (LM37CorrelatedScale n (Ucap n) (Icard n) (contact n)
        (radius n) (M n) (degreeIntoU n) (1 / 1024)
          ((1 / 64) * (d n : ℝ))) := by
  filter_upwards [hb] with n hn
  exact ⟨concreteLM37LargeOnlyScale n (d n) (Ucap n) (Icard n)
    (contact n) (radius n) (M n) (degreeIntoU n) (D n) (cutoff n) hn⟩

/-! ## Pointwise Claim 4.4 source parameters -/

/-- The remaining graph-free hypotheses for the source-radius Claim 4.4
certificate.  The two `LM44LM311Bounds` fields are deliberately kept
range-uniform: the order of the bipartite expander extracted in Claim 4.4 is
not known in advance, but only lies strictly above `coreDegree` and at most
`N`.

This is a pointwise package.  Establishing it eventually is a separate
asymptotic problem, while its conversion to the exact `LM44Scale` consumed by
Claim 4.4 is completely formal. -/
structure LM44FiveRoundsPointwiseBounds
    (N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R initialDegree coreDegree : ℕ) : Prop where
  deleted_le : deletedCap ≤ 10 * targetOrder
  deletion_proper : deletedCap +
    lm44BallCap protectedCap R maxRadius Delta separation < N
  initial_density : ∀ u ≤ deletedCap,
    initialDegree * (N - u) ≤
      ((N - u) - 100 * targetOrder ^ 2) * (d - d / 2)
  retained_density : (8 * coreDegree) * N +
    2 * (lm44BallCap protectedCap R maxRadius Delta separation * Delta) ≤
      initialDegree * (N - deletedCap)
  core_large : 32 ≤ coreDegree
  target_pos : 0 < targetOrder
  totalRadius_pos : 1 ≤ totalRadius
  maxRadius_le : maxRadius ≤ totalRadius
  star_budget : targetOrder +
    lm44StarBudget deletedCap maxRadius targetOrder ≤ Delta
  radius_bounds : ∀ n', coreDegree < n' → n' ≤ N →
    minRadius ≤ 5 * lmGrowthRounds n' ∧
      5 * lmGrowthRounds n' ≤ maxRadius
  connector_seed : ∀ n' D L, coreDegree < n' → n' ≤ N → 0 < D →
    L ≤ lm311GirthBudget n' →
    lm311AdaptiveSeed coreDegree ≤ (5 * lmGrowthRounds n') ^ 2 * D ∨
      lm311AdaptiveSeed coreDegree +
        max (lm42SquareWorkspace D (5 * lmGrowthRounds n') L)
          (lm42CubeWorkspace D (5 * lmGrowthRounds n') L) ≤ coreDegree - 1
  num_one : ∀ n', coreDegree < n' → n' ≤ N →
    LM44LM311Bounds n' coreDegree ((5 * lmGrowthRounds n') ^ 3)
  num_square : ∀ n', coreDegree < n' → n' ≤ N →
    LM44LM311Bounds n' coreDegree
      ((5 * lmGrowthRounds n') ^ 3 * (5 * lmGrowthRounds n') ^ 2)

/-- Convert the pointwise source inequalities into the literal `LM44Scale`.
In particular, this theorem supplies both k=4 Lemma 3.11 certificates and
both adaptive Lemma 4.2 connector schedules; callers do not have to assemble
either dependent record by hand. -/
noncomputable def concreteLM44ScaleFiveRoundsOfPointwiseBounds
    {N d targetOrder totalRadius Delta deletedCap protectedCap separation
      minRadius maxRadius R initialDegree coreDegree : ℕ}
    (b : LM44FiveRoundsPointwiseBounds N d targetOrder totalRadius Delta
      deletedCap protectedCap separation minRadius maxRadius R initialDegree
        coreDegree) :
    SmallSimpleAdjusterCandidate.LM44Scale N d targetOrder totalRadius Delta
      deletedCap protectedCap separation minRadius maxRadius R
        ((1 / 64) * (coreDegree : ℝ)) := by
  apply SmallSimpleAdjusterCandidate.concreteLM44ScaleFiveRounds N d
    targetOrder totalRadius Delta deletedCap protectedCap separation minRadius
    maxRadius R initialDegree coreDegree b.deleted_le b.deletion_proper
    b.initial_density b.retained_density b.core_large b.target_pos
    b.totalRadius_pos b.maxRadius_le b.star_budget b.radius_bounds b.connector_seed
  · intro n' hn' hN'
    exact concreteLM44LM311Numerics (b.num_one n' hn' hN')
  · intro n' hn' hN'
    exact concreteLM44LM311Numerics (b.num_square n' hn' hN')

/-! ## Pointwise graph-free tail of the robust assembly -/

/-- A family-independent upper bound for the static workspace built between
Claims 4.5 and 4.6.  `Claim46Aux.card_claim46WorkspaceOf_le` turns this number
into the corresponding bound for every surviving family of cardinality
`2 * R`. -/
def lm43Claim46WorkspaceCap
    (deletedCap R maxRadius Delta ballRadius : ℕ) : ℕ :=
  deletedCap + 2 * R *
    ((2 * maxRadius ^ 2 + 10 * maxRadius) +
      2 * maxRadius ^ 2 * (Delta + 1) ^ ballRadius)

/-- Every graph-free hypothesis in
`SmallSimpleAdjusterCandidate.false_of_claim45_claim46_and_final`, together
with family-independent strengthening of the two workspace hypotheses and
of the two final connector-rate hypotheses.

The three finite-family sum fields are universe-polymorphic so that the same
certificate can be instantiated with each of the three proof-carrying
candidate subtypes occurring in the robust theorem.  Graph facts
(`hdeleted`, degree bounds, nonexistence of a target, and the final
neighbor-degree statement) intentionally do not occur here. -/
structure LM43RobustScalarCertificate
    (N d separation highRadius targetRadius ballRadius minRadius maxRadius
      targetOrder totalRadius Delta deletedCap R degreeInto ballTarget
      finalConnectorQ finalConnectorRadius : ℕ)
    (scale45 : LM37CorrelatedScale N deletedCap R 2 highRadius targetOrder
      degreeInto (1 / 1024) ((1 / 64) * (d : ℝ)))
    (scale46 : LM37CorrelatedScale N deletedCap R 2 ballRadius targetOrder
      degreeInto (1 / 1024) ((1 / 64) * (d : ℝ)))
    (scaleFinal : LM37CorrelatedScale N deletedCap R 0 ballRadius ballTarget
      degreeInto (1 / 1024) ((1 / 64) * (d : ℝ))) : Prop where
  high_separated : highRadius + highRadius ≤ separation
  ball_separated : ballRadius + ballRadius ≤ separation
  ball_le_high : ballRadius ≤ highRadius
  target_pos : 0 < targetOrder
  right_budget : targetOrder +
    (deletedCap + 10 * maxRadius + (maxRadius + 1) + (highRadius + 1)) ≤
      Delta
  left_budget : targetOrder +
    (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta
  claim45_radius : maxRadius + highRadius + 1 ≤ totalRadius
  card_large : 32 ≤ N
  degree_pos : 1 ≤ d
  degree_le_card : d ≤ N
  claim46_workspace :
    lm43Claim46WorkspaceCap deletedCap R maxRadius Delta ballRadius ≤
      lm43GrowthGain N (lm43K N)
  claim46_room :
    lm43Claim46WorkspaceCap deletedCap R maxRadius Delta ballRadius +
      lm43K N ≤ N
  target_le_K : targetOrder ≤ lm43K N
  denominator_le_K : 6 * lm43GrowthDenominator N ≤ lm43K N
  claim45_start : scale45.growth 0 < minRadius ^ 2
  claim45_start_one : scale45.growth 1 < minRadius ^ 2
  claim45_minSize : scale45.minSize ≤ minRadius ^ 2
  claim45_neighbor : ∀ ell s, 0 < ell → ell ≤ highRadius →
    scale45.growth (ell - 1) < s →
    scale45.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
      scale45.neighborBudget s
  claim45_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, scale45.neighborBudget (f i) ≤
      scale45.largeBudget (∑ i ∈ J, f i)
  claim46_start : scale46.growth 0 < minRadius ^ 2
  claim46_start_one : scale46.growth 1 < minRadius ^ 2
  claim46_minSize : scale46.minSize ≤ minRadius ^ 2
  claim46_neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
    scale46.growth (ell - 1) < s →
    scale46.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
      scale46.neighborBudget s
  claim46_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, scale46.neighborBudget (f i) ≤
      scale46.largeBudget (∑ i ∈ J, f i)
  claim46_left_radius :
    maxRadius + targetRadius + 2 * lm43FarRadius N ≤ totalRadius
  claim46_right_radius : maxRadius + ballRadius ≤ totalRadius
  final_start : scaleFinal.growth 0 < 2 * minRadius ^ 2
  final_start_one : scaleFinal.growth 1 < 2 * minRadius ^ 2
  final_minSize : scaleFinal.minSize ≤ 2 * minRadius ^ 2
  final_neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
    scaleFinal.growth (ell - 1) < s →
    scaleFinal.stepLoss ell + 10 * maxRadius ≤
      scaleFinal.neighborBudget s
  final_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, scaleFinal.neighborBudget (f i) ≤
      scaleFinal.largeBudget (∑ i ∈ J, f i)
  ball_lower : ((1 / 64) * (d : ℝ)) / 2 ≤ (ballTarget : ℝ)
  target_lower : ((1 / 64) * (d : ℝ)) / 2 ≤ (targetOrder : ℝ)
  ball_rate : ∀ s, ballTarget ≤ s → s ≤ N / 2 →
    (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  target_rate : ∀ s, targetOrder ≤ s → s ≤ N / 2 →
    (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  ball_steps : N / 2 + 1 ≤
    ballTarget + finalConnectorRadius * finalConnectorQ
  target_steps : N / 2 + 1 ≤
    targetOrder + finalConnectorRadius * finalConnectorQ
  final_radius : ballRadius + 2 * finalConnectorRadius ≤ targetRadius

/-- The graph-free certificate for the source-sample robust assembly.

This is the certificate used on the final critical path.  Its three Lemma
3.7 records use the literal `D²` and `r²` samples from the paper, and its
radius-one hypotheses stop at `lm37SourceMinSize d`; the graph theorem then
obtains that size from the minimum degree.  Thus this interface does not
silently require a polylogarithmic candidate end to dominate `d`. -/
structure LM43RobustSourceScalarCertificate
    (N d separation highRadius targetRadius ballRadius minRadius maxRadius
      targetOrder totalRadius Delta deletedCap degreeInto
      maxSlow45 maxSlow46 maxSlowFinal finalM finalConnectorQ
      finalConnectorRadius : ℕ)
    (bounds45 : LM37SourceReachBounds N d deletedCap 2 highRadius targetOrder
      degreeInto maxSlow45)
    (bounds46 : LM37SourceReachBounds N d deletedCap 2 ballRadius targetOrder
      degreeInto maxSlow46)
    (boundsFinal : LM37SourceFinalTwoEndBounds N d deletedCap 0 ballRadius
      finalM targetOrder degreeInto maxSlowFinal) : Type where
  high_separated : highRadius + highRadius ≤ separation
  ball_separated : ballRadius + ballRadius ≤ separation
  ball_le_high : ballRadius ≤ highRadius
  target_pos : 0 < targetOrder
  right_budget : targetOrder +
    (deletedCap + 10 * maxRadius + (maxRadius + 1) + (highRadius + 1)) ≤
      Delta
  left_budget : targetOrder +
    (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta
  claim45_radius : maxRadius + highRadius + 1 ≤ totalRadius
  card_large : 32 ≤ N
  degree_pos : 1 ≤ d
  degree_le_card : d ≤ N
  workspaceCap : ℕ
  claim46_workspace :
    lm43Claim46WorkspaceCap deletedCap (SourceLemma35Numerics.indexCard N)
      maxRadius Delta ballRadius ≤ workspaceCap
  claim46_workspace_gain : workspaceCap ≤
    lm43GrowthGain N (lm43K N)
  claim46_room : workspaceCap + lm43K N ≤ N
  target_le_K : targetOrder ≤ lm43K N
  denominator_le_K : 6 * lm43GrowthDenominator N ≤ lm43K N
  claim45_start : bounds45.growth 0 < minRadius ^ 2
  claim45_start_one : bounds45.growth 1 < lm37SourceMinSize d
  claim45_retained : lm37SourceMinSize d ≤
    d - degreeInto - (11 * maxRadius + 1) - 2
  claim45_neighbor : ∀ ell s, 0 < ell → ell ≤ highRadius →
    bounds45.growth (ell - 1) < s →
    bounds45.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
      bounds45.neighborBudget s
  claim45_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, bounds45.neighborBudget (f i) ≤
      bounds45.largeBudget (∑ i ∈ J, f i)
  claim46_start : bounds46.growth 0 < minRadius ^ 2
  claim46_start_one : bounds46.growth 1 < lm37SourceMinSize d
  claim46_retained : lm37SourceMinSize d ≤
    d - degreeInto - (11 * maxRadius + 1) - 2
  claim46_neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
    bounds46.growth (ell - 1) < s →
    bounds46.stepLoss ell + (11 * maxRadius + 1) + 2 * ell ≤
      bounds46.neighborBudget s
  claim46_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, bounds46.neighborBudget (f i) ≤
      bounds46.largeBudget (∑ i ∈ J, f i)
  claim46_left_radius :
    maxRadius + targetRadius + 2 * lm43FarRadius N ≤ totalRadius
  claim46_right_radius : maxRadius + ballRadius ≤ totalRadius
  final_start : boundsFinal.growth 0 < 2 * minRadius ^ 2
  final_start_one : boundsFinal.growth 1 < lm37SourceMinSize d
  final_retained : lm37SourceMinSize d ≤
    d - degreeInto - 10 * maxRadius
  final_neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
    boundsFinal.growth (ell - 1) < s →
    boundsFinal.stepLoss ell + 10 * maxRadius ≤
      boundsFinal.neighborBudget s
  final_largeBudgetSum : ∀ {I : Type*} [DecidableEq I]
    (J : Finset I) (f : I → ℕ),
    ∑ i ∈ J, boundsFinal.neighborBudget (f i) ≤
      boundsFinal.largeBudget (∑ i ∈ J, f i)
  ball_lower : ((1 / 64) * (d : ℝ)) / 2 ≤
    ((10 * finalM ^ 2 * targetOrder : ℕ) : ℝ)
  target_lower : ((1 / 64) * (d : ℝ)) / 2 ≤ (targetOrder : ℝ)
  ball_rate : ∀ s, 10 * finalM ^ 2 * targetOrder ≤ s → s ≤ N / 2 →
    (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  target_rate : ∀ s, targetOrder ≤ s → s ≤ N / 2 →
    (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
      expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ))
  ball_steps : N / 2 + 1 ≤
    10 * finalM ^ 2 * targetOrder + finalConnectorRadius * finalConnectorQ
  target_steps : N / 2 + 1 ≤
    targetOrder + finalConnectorRadius * finalConnectorQ
  final_radius : ballRadius + 2 * finalConnectorRadius ≤ targetRadius

/-- Construct the robust scalar certificate from the three source-split
Lemma 3.7 bound records.  Superadditivity discharges all three
family-dependent large-budget hypotheses automatically. -/
noncomputable def concreteLM43RobustSourceSplitScalarCertificate
    (N d separation highRadius targetRadius ballRadius minRadius maxRadius
      targetOrder totalRadius Delta deletedCap R degreeInto ballTarget
      finalConnectorQ finalConnectorRadius
      min45 cutoff45 D45 T45 min46 cutoff46 D46 T46
      minFinal cutoffFinal DFinal TFinal : ℕ)
    (b45 : LM37SourceSplitBounds N d deletedCap R highRadius targetOrder
      degreeInto min45 cutoff45 D45 T45)
    (b46 : LM37SourceSplitBounds N d deletedCap R ballRadius targetOrder
      degreeInto min46 cutoff46 D46 T46)
    (bFinal : LM37SourceSplitBounds N d deletedCap R ballRadius ballTarget
      degreeInto minFinal cutoffFinal DFinal TFinal)
    (hhighSep : highRadius + highRadius ≤ separation)
    (hballSep : ballRadius + ballRadius ≤ separation)
    (hballHigh : ballRadius ≤ highRadius)
    (htarget : 0 < targetOrder)
    (hrightBudget : targetOrder +
      (deletedCap + 10 * maxRadius + (maxRadius + 1) + (highRadius + 1)) ≤
        Delta)
    (hleftBudget : targetOrder +
      (deletedCap + 10 * maxRadius + targetOrder) ≤ Delta)
    (h45radius : maxRadius + highRadius + 1 ≤ totalRadius)
    (hn : 32 ≤ N) (hd : 1 ≤ d) (hdN : d ≤ N)
    (hworkspace :
      lm43Claim46WorkspaceCap deletedCap R maxRadius Delta ballRadius ≤
        lm43GrowthGain N (lm43K N))
    (hroom : lm43Claim46WorkspaceCap deletedCap R maxRadius Delta ballRadius +
      lm43K N ≤ N)
    (hTargetK : targetOrder ≤ lm43K N)
    (hdenominator : 6 * lm43GrowthDenominator N ≤ lm43K N)
    (h45start : lm37SourceCurve N min45 0 < minRadius ^ 2)
    (h45startOne : lm37SourceCurve N min45 1 < minRadius ^ 2)
    (h45min : min45 ≤ minRadius ^ 2)
    (h45neighbor : ∀ ell s, 0 < ell → ell ≤ highRadius →
      lm37SourceCurve N min45 (ell - 1) < s →
      lm37SourceStepLoss N min45 ell + (11 * maxRadius + 1) + 2 * ell ≤
        2 * lm37SourceGain N s)
    (h46start : lm37SourceCurve N min46 0 < minRadius ^ 2)
    (h46startOne : lm37SourceCurve N min46 1 < minRadius ^ 2)
    (h46min : min46 ≤ minRadius ^ 2)
    (h46neighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      lm37SourceCurve N min46 (ell - 1) < s →
      lm37SourceStepLoss N min46 ell + (11 * maxRadius + 1) + 2 * ell ≤
        2 * lm37SourceGain N s)
    (hleftRadius : maxRadius + targetRadius + 2 * lm43FarRadius N ≤
      totalRadius)
    (hrightRadius : maxRadius + ballRadius ≤ totalRadius)
    (hFinalStart : lm37SourceCurve N minFinal 0 < 2 * minRadius ^ 2)
    (hFinalStartOne : lm37SourceCurve N minFinal 1 < 2 * minRadius ^ 2)
    (hFinalMin : minFinal ≤ 2 * minRadius ^ 2)
    (hFinalNeighbor : ∀ ell s, 0 < ell → ell ≤ ballRadius →
      lm37SourceCurve N minFinal (ell - 1) < s →
      lm37SourceStepLoss N minFinal ell + 10 * maxRadius ≤
        2 * lm37SourceGain N s)
    (hBallLower : ((1 / 64) * (d : ℝ)) / 2 ≤ (ballTarget : ℝ))
    (hTargetLower : ((1 / 64) * (d : ℝ)) / 2 ≤ (targetOrder : ℝ))
    (hBallRate : ∀ s, ballTarget ≤ s → s ≤ N / 2 →
      (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hTargetRate : ∀ s, targetOrder ≤ s → s ≤ N / 2 →
      (((deletedCap + 10 * maxRadius + finalConnectorQ : ℕ) : ℝ) ≤
        expansionEpsilon (1 / 1024) ((1 / 64) * (d : ℝ)) s * (s : ℝ)))
    (hBallSteps : N / 2 + 1 ≤
      ballTarget + finalConnectorRadius * finalConnectorQ)
    (hTargetSteps : N / 2 + 1 ≤
      targetOrder + finalConnectorRadius * finalConnectorQ)
    (hFinalRadius : ballRadius + 2 * finalConnectorRadius ≤ targetRadius) :
    let scale45 := concreteLM37SourceSplitScale N d deletedCap R 2 highRadius
      targetOrder degreeInto min45 cutoff45 D45 T45 b45
    let scale46 := concreteLM37SourceSplitScale N d deletedCap R 2 ballRadius
      targetOrder degreeInto min46 cutoff46 D46 T46 b46
    let scaleFinal := concreteLM37SourceSplitScale N d deletedCap R 0 ballRadius
      ballTarget degreeInto minFinal cutoffFinal DFinal TFinal bFinal
    LM43RobustScalarCertificate N d separation highRadius targetRadius ballRadius
      minRadius maxRadius targetOrder totalRadius Delta deletedCap R degreeInto
      ballTarget finalConnectorQ finalConnectorRadius scale45 scale46
        scaleFinal := by
  dsimp
  refine
    { high_separated := hhighSep
      ball_separated := hballSep
      ball_le_high := hballHigh
      target_pos := htarget
      right_budget := hrightBudget
      left_budget := hleftBudget
      claim45_radius := h45radius
      card_large := hn
      degree_pos := hd
      degree_le_card := hdN
      claim46_workspace := hworkspace
      claim46_room := hroom
      target_le_K := hTargetK
      denominator_le_K := hdenominator
      claim45_start := h45start
      claim45_start_one := h45startOne
      claim45_minSize := h45min
      claim45_neighbor := h45neighbor
      claim45_largeBudgetSum := ?_
      claim46_start := h46start
      claim46_start_one := h46startOne
      claim46_minSize := h46min
      claim46_neighbor := h46neighbor
      claim46_largeBudgetSum := ?_
      claim46_left_radius := hleftRadius
      claim46_right_radius := hrightRadius
      final_start := hFinalStart
      final_start_one := hFinalStartOne
      final_minSize := hFinalMin
      final_neighbor := hFinalNeighbor
      final_largeBudgetSum := ?_
      ball_lower := hBallLower
      target_lower := hTargetLower
      ball_rate := hBallRate
      target_rate := hTargetRate
      ball_steps := hBallSteps
      target_steps := hTargetSteps
      final_radius := hFinalRadius }
  · intro I _ J f
    exact concreteLM37SourceSplitScale_largeBudgetSum N d deletedCap R 2
      highRadius targetOrder degreeInto min45 cutoff45 D45 T45 b45 J f
  · intro I _ J f
    exact concreteLM37SourceSplitScale_largeBudgetSum N d deletedCap R 2
      ballRadius targetOrder degreeInto min46 cutoff46 D46 T46 b46 J f
  · intro I _ J f
    exact concreteLM37SourceSplitScale_largeBudgetSum N d deletedCap R 0
      ballRadius ballTarget degreeInto minFinal cutoffFinal DFinal TFinal bFinal J f

end Erdos63
