/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperExceptionalMassBridge
import ErdosProblems.Erdos446.SmirnovCardinalBounds
import ErdosProblems.Erdos446.SmirnovFirstCrossingSum
import ErdosProblems.Erdos446.ShiftedAbelConvolution

/-!
# Erdős Problem 446: reciprocal-factorial mass of a crowding layer

This file is the finite occupancy version of Ford's four-factor split in
(32f)--(32h).  The basic operation `occupancyTake c n` retains the first
`n` objects of an occupancy vector (cells are read from left to right).
This lets us split a crowding witness into the first `l-g-1` objects, the
next `g`, the crossing object, and the suffix, without introducing labelled
points or a measure-theoretic ordered-simplex argument.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-! ## Rank truncation of an occupancy vector -/

/-- Occupancy vector formed by the first `n` objects, reading cells from
left to right. -/
def occupancyTake {v : ℕ} (c : Fin v → ℕ) (n : ℕ) : Fin v → ℕ :=
  fun i ↦ min (c i) (n - occupancyPrefix c i.val)

theorem occupancyPrefix_succ {v : ℕ} (c : Fin v → ℕ)
    {h : ℕ} (hh : h < v) :
    occupancyPrefix c (h + 1) = occupancyPrefix c h + c ⟨h, hh⟩ := by
  rw [occupancyPrefix_eq_sum_take_ofFn,
    occupancyPrefix_eq_sum_take_ofFn, List.sum_take_succ]
  · rw [List.getElem_ofFn]
  · simpa only [List.length_ofFn] using hh

theorem occupancyTake_eq_prefixMin_sub {v : ℕ} (c : Fin v → ℕ)
    (n : ℕ) (i : Fin v) :
    occupancyTake c n i =
      min (occupancyPrefix c (i.val + 1)) n -
        min (occupancyPrefix c i.val) n := by
  have hsucc : occupancyPrefix c (i.val + 1) =
      occupancyPrefix c i.val + c i := by
    simpa only [Fin.eta] using occupancyPrefix_succ c i.isLt
  rw [occupancyTake, hsucc]
  by_cases hpn : occupancyPrefix c i.val ≤ n
  · by_cases hpcn : occupancyPrefix c i.val + c i ≤ n
    · rw [min_eq_left hpcn, min_eq_left hpn]
      omega
    · rw [min_eq_right (Nat.le_of_not_ge hpcn), min_eq_left hpn]
      omega
  · have hnp : n ≤ occupancyPrefix c i.val := Nat.le_of_not_ge hpn
    rw [min_eq_right hnp, min_eq_right (hnp.trans (Nat.le_add_right _ _))]
    omega

theorem occupancyPrefix_occupancyTake {v : ℕ} (c : Fin v → ℕ)
    (n : ℕ) {h : ℕ} (hh : h ≤ v) :
    occupancyPrefix (occupancyTake c n) h = min (occupancyPrefix c h) n := by
  induction h with
  | zero => simp [occupancyPrefix_zero]
  | succ h ih =>
      have hhv : h < v := by omega
      rw [occupancyPrefix_succ _ hhv, ih (by omega)]
      have htake := occupancyTake_eq_prefixMin_sub c n ⟨h, hhv⟩
      have htake' : occupancyTake c n ⟨h, hhv⟩ =
          min (occupancyPrefix c (h + 1)) n -
            min (occupancyPrefix c h) n := by
        simpa only [Fin.eta] using htake
      rw [htake']
      have hmono : occupancyPrefix c h ≤ occupancyPrefix c (h + 1) :=
        occupancyPrefix_mono c (Nat.le_succ h)
      omega

theorem sum_occupancyTake {v : ℕ} (c : Fin v → ℕ) (n : ℕ) :
    (∑ i, occupancyTake c n i) = min (∑ i, c i) n := by
  rw [← occupancyPrefix_at_length, ← occupancyPrefix_at_length,
    occupancyPrefix_occupancyTake c n le_rfl]

theorem occupancyTake_le {v : ℕ} (c : Fin v → ℕ) (n : ℕ) (i : Fin v) :
    occupancyTake c n i ≤ c i := by
  exact min_le_left _ _

theorem occupancyTake_mono {v : ℕ} (c : Fin v → ℕ) :
    Monotone (occupancyTake c) := by
  intro m n hmn i
  dsimp [occupancyTake]
  exact min_le_min_left _ (Nat.sub_le_sub_right hmn _)

/-- Objects with ranks in `[a,b)`. -/
def occupancyRankInterval {v : ℕ} (c : Fin v → ℕ)
    (a b : ℕ) : Fin v → ℕ :=
  fun i ↦ occupancyTake c b i - occupancyTake c a i

theorem occupancyTake_add_rankInterval {v : ℕ} (c : Fin v → ℕ)
    {a b : ℕ} (hab : a ≤ b) (i : Fin v) :
    occupancyTake c a i + occupancyRankInterval c a b i =
      occupancyTake c b i := by
  dsimp [occupancyRankInterval]
  exact Nat.add_sub_of_le (occupancyTake_mono c hab i)

theorem sum_occupancyRankInterval {v : ℕ} {c : Fin v → ℕ}
    {a b total : ℕ} (hc : ∑ i, c i = total)
    (hab : a ≤ b) (hb : b ≤ total) :
    (∑ i, occupancyRankInterval c a b i) = b - a := by
  have ha : a ≤ total := hab.trans hb
  have hsumA := sum_occupancyTake c a
  have hsumB := sum_occupancyTake c b
  rw [hc, min_eq_right ha] at hsumA
  rw [hc, min_eq_right hb] at hsumB
  have hpoint := fun i : Fin v ↦ occupancyTake_add_rankInterval c hab i
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin v)))
    (s₂ := Finset.univ) rfl (fun i _ ↦ hpoint i)
  simp only [Finset.sum_add_distrib] at hsum
  rw [hsumA, hsumB] at hsum
  omega

/-- The tail after the first `n` objects. -/
def occupancyDrop {v : ℕ} (c : Fin v → ℕ) (n : ℕ) : Fin v → ℕ :=
  fun i ↦ c i - occupancyTake c n i

theorem occupancyTake_add_drop {v : ℕ} (c : Fin v → ℕ)
    (n : ℕ) (i : Fin v) :
    occupancyTake c n i + occupancyDrop c n i = c i := by
  exact Nat.add_sub_of_le (occupancyTake_le c n i)

theorem sum_occupancyDrop {v : ℕ} {c : Fin v → ℕ}
    {n total : ℕ} (hc : ∑ i, c i = total) (hn : n ≤ total) :
    (∑ i, occupancyDrop c n i) = total - n := by
  have htake := sum_occupancyTake c n
  rw [hc, min_eq_right hn] at htake
  have hsum := Finset.sum_congr (s₁ := (Finset.univ : Finset (Fin v)))
    (s₂ := Finset.univ) rfl
    (fun i _ ↦ occupancyTake_add_drop c n i)
  simp only [Finset.sum_add_distrib, hc, htake] at hsum
  omega

/-! ## Factorial weight of a rank split -/

theorem factorial_mul_factorial_le_factorial_add (a b : ℕ) :
    a.factorial * b.factorial ≤ (a + b).factorial := by
  exact Nat.le_of_dvd (Nat.factorial_pos _)
    (Nat.factorial_mul_factorial_dvd_factorial_add a b)

theorem compositionFactorial_mul_le_of_pointwise_add
    {v : ℕ} (a b c : Fin v → ℕ)
    (hc : ∀ i, a i + b i = c i) :
    compositionFactorial a * compositionFactorial b ≤
      compositionFactorial c := by
  dsimp [compositionFactorial]
  rw [← Finset.prod_mul_distrib]
  apply Finset.prod_le_prod (fun _ _ ↦ by positivity)
  intro i hi
  rw [← hc i]
  exact_mod_cast factorial_mul_factorial_le_factorial_add (a i) (b i)

theorem inv_compositionFactorial_le_mul_of_pointwise_add
    {v : ℕ} (a b c : Fin v → ℕ)
    (hc : ∀ i, a i + b i = c i) :
    1 / compositionFactorial c ≤
      (1 / compositionFactorial a) * (1 / compositionFactorial b) := by
  have hmul := compositionFactorial_mul_le_of_pointwise_add a b c hc
  have hpos : 0 < compositionFactorial a * compositionFactorial b := by
    dsimp [compositionFactorial]
    positivity
  have hinv := one_div_le_one_div_of_le hpos hmul
  calc
    1 / compositionFactorial c ≤
        1 / (compositionFactorial a * compositionFactorial b) := hinv
    _ = (1 / compositionFactorial a) *
        (1 / compositionFactorial b) := by field_simp

/-! ## Unconditional uniform Smirnov estimate -/

/-- Ford's one-sided Smirnov estimate with a deliberately generous absolute
constant.  The large/small case split is useful downstream because it removes
all auxiliary hypotheses from the crowding lemma. -/
theorem smirnovProbability_le_uniform
    {k u v w : ℕ} (hk : 0 < k) (hw : 0 < w)
    (hrel : u + v = k + w) :
    smirnovProbability k u v ≤
      2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k + 1 : ℕ) := by
  by_cases hv0 : v = 0
  · subst v
    simp [smirnovProbability, smirnovOccupancyMass, smirnovOccupancies,
      compositionsOf, hk.ne']
    positivity
  have hv : 0 < v := by omega
  have hprob := smirnovProbability_le_one (k := k) (u := u) hv
  have hkR : (0 : ℝ) < (k + 1 : ℕ) := by positivity
  by_cases hk100 : 100 ≤ k
  · by_cases hu10 : 10 * u ≤ k
    · by_cases hwSq : w * w ≤ k
      · have hwkR : 10 * (w : ℝ) ≤ k := by
          by_contra hnot
          have hlt : (k : ℝ) < 10 * w := lt_of_not_ge hnot
          have hk100R : (100 : ℝ) ≤ k := by exact_mod_cast hk100
          have hwSqR : (w : ℝ) * w ≤ k := by exact_mod_cast hwSq
          nlinarith
        have hwk : 10 * w ≤ k := by exact_mod_cast hwkR
        have htrunc : 2 * w + 2 ≤ v := by omega
        have hfail := exp_mul_truncated_words_le_card_failedBarrierWords
          hrel htrunc
        have hcentral := smirnovProbability_le_twentyfour_of_cardinal_lower
          hk100 hu10 hwSq hw hrel hfail
        calc
          smirnovProbability k u v ≤
              24 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 / (k : ℝ) := hcentral
          _ ≤ 2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 /
                (k + 1 : ℕ) := by
            have hkR' : (0 : ℝ) < k := by exact_mod_cast hk
            have hk1 : (k + 1 : ℕ) ≤ 100 * k := by omega
            have hk1R : ((k + 1 : ℕ) : ℝ) ≤ 100 * (k : ℝ) := by
              exact_mod_cast hk1
            have hnon : 0 ≤ (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 := by positivity
            apply (div_le_div_iff₀ hkR' hkR).2
            nlinarith
      · have hwLarge : k < w * w := lt_of_not_ge hwSq
        have hwLargeR : (k : ℝ) < (w : ℝ) ^ 2 := by
          rw [pow_two]
          exact_mod_cast hwLarge
        have hk1R' : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
          exact_mod_cast (show k + 1 ≤ 2 * k by omega)
        have huOne : (1 : ℝ) ≤ ((u + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ u + 1 by omega)
        have hwOne : (w : ℝ) ^ 2 ≤ ((w + 1 : ℕ) : ℝ) ^ 2 := by
          exact_mod_cast (Nat.pow_le_pow_left (show w ≤ w + 1 by omega) 2)
        have hnum : ((k + 1 : ℕ) : ℝ) ≤
            2400 * ((u + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 := by
          calc
            ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := hk1R'
            _ ≤ 2 * (w : ℝ) ^ 2 := by nlinarith
            _ ≤ 2 * ((w + 1 : ℕ) : ℝ) ^ 2 := by gcongr
            _ ≤ 2400 * ((u + 1 : ℕ) : ℝ) *
                ((w + 1 : ℕ) : ℝ) ^ 2 := by
              have hsq : 0 ≤ ((w + 1 : ℕ) : ℝ) ^ 2 := by positivity
              nlinarith
        apply hprob.trans
        apply (le_div_iff₀ hkR).2
        simpa only [Nat.cast_add, Nat.cast_one, one_mul] using hnum
    · have huLarge : k < 10 * u := lt_of_not_ge hu10
      have huLargeR : (k : ℝ) < 10 * (u : ℝ) := by exact_mod_cast huLarge
      have hwOne : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) ^ 2 := by
        have hwCast : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show 1 ≤ w + 1 by omega)
        nlinarith
      have hk1R' : ((k + 1 : ℕ) : ℝ) ≤ 2 * (k : ℝ) := by
        exact_mod_cast (show k + 1 ≤ 2 * k by omega)
      have hnum : ((k + 1 : ℕ) : ℝ) ≤
          2400 * ((u + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 := by
        have huCast : (u : ℝ) ≤ ((u + 1 : ℕ) : ℝ) := by
          exact_mod_cast (show u ≤ u + 1 by omega)
        nlinarith
      apply hprob.trans
      apply (le_div_iff₀ hkR).2
      simpa only [Nat.cast_add, Nat.cast_one, one_mul] using hnum
  · have hkSmall : k < 100 := lt_of_not_ge hk100
    have hk1 : (k + 1 : ℕ) ≤ 100 := by omega
    have huOne : (1 : ℝ) ≤ ((u + 1 : ℕ) : ℝ) := by
      exact_mod_cast (show 1 ≤ u + 1 by omega)
    have hwOne : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) ^ 2 := by
      have hwCast : (1 : ℝ) ≤ ((w + 1 : ℕ) : ℝ) := by
        exact_mod_cast (show 1 ≤ w + 1 by omega)
      nlinarith
    have hnum : ((k + 1 : ℕ) : ℝ) ≤
        2400 * ((u + 1 : ℕ) : ℝ) * ((w + 1 : ℕ) : ℝ) ^ 2 := by
      have hk1R' : ((k + 1 : ℕ) : ℝ) ≤ 100 := by exact_mod_cast hk1
      nlinarith
    apply hprob.trans
    apply (le_div_iff₀ hkR).2
    simpa only [Nat.cast_add, Nat.cast_one, one_mul] using hnum

/-! ## Zero padding of the four factors -/

def zeroComposition (n : ℕ) : Fin n → ℕ := fun _ ↦ 0

theorem compositionFactorial_zeroComposition (n : ℕ) :
    compositionFactorial (zeroComposition n) = 1 := by
  simp [compositionFactorial, zeroComposition]

def prefixLift (v p : ℕ) (hp : p ≤ v) (a : Fin p → ℕ) : Fin v → ℕ :=
  splitAtCompositionEquiv v p hp (a, zeroComposition (v - p))

theorem prefixLift_injective (v p : ℕ) (hp : p ≤ v) :
    Function.Injective (prefixLift v p hp) := by
  intro a b hab
  have := (splitAtCompositionEquiv v p hp).injective hab
  exact congrArg Prod.fst this

def prefixLiftEmbedding (v p : ℕ) (hp : p ≤ v) :
    (Fin p → ℕ) ↪ (Fin v → ℕ) :=
  ⟨prefixLift v p hp, prefixLift_injective v p hp⟩

theorem compositionFactorial_prefixLift (v p : ℕ) (hp : p ≤ v)
    (a : Fin p → ℕ) :
    compositionFactorial (prefixLift v p hp a) = compositionFactorial a := by
  rw [prefixLift, compositionFactorial_splitAtCompositionEquiv,
    compositionFactorial_zeroComposition, mul_one]

theorem sum_prefixLift (v p : ℕ) (hp : p ≤ v) (a : Fin p → ℕ) :
    (∑ i, prefixLift v p hp a i) = ∑ i, a i := by
  rw [prefixLift, sum_splitAtCompositionEquiv]
  simp [zeroComposition]

def suffixLift (v p : ℕ) (hp : p ≤ v) (b : Fin (v - p) → ℕ) :
    Fin v → ℕ :=
  splitAtCompositionEquiv v p hp (zeroComposition p, b)

theorem suffixLift_injective (v p : ℕ) (hp : p ≤ v) :
    Function.Injective (suffixLift v p hp) := by
  intro a b hab
  have := (splitAtCompositionEquiv v p hp).injective hab
  exact congrArg Prod.snd this

def suffixLiftEmbedding (v p : ℕ) (hp : p ≤ v) :
    (Fin (v - p) → ℕ) ↪ (Fin v → ℕ) :=
  ⟨suffixLift v p hp, suffixLift_injective v p hp⟩

theorem compositionFactorial_suffixLift (v p : ℕ) (hp : p ≤ v)
    (b : Fin (v - p) → ℕ) :
    compositionFactorial (suffixLift v p hp b) = compositionFactorial b := by
  rw [suffixLift, compositionFactorial_splitAtCompositionEquiv,
    compositionFactorial_zeroComposition, one_mul]

theorem sum_suffixLift (v p : ℕ) (hp : p ≤ v)
    (b : Fin (v - p) → ℕ) :
    (∑ i, suffixLift v p hp b i) = ∑ i, b i := by
  rw [suffixLift, sum_splitAtCompositionEquiv]
  simp [zeroComposition]

/-- Pad a composition by zeros on both sides. -/
def intervalLift (v start len : ℕ) (hsl : start + len ≤ v)
    (b : Fin len → ℕ) : Fin v → ℕ :=
  suffixLift v start (start.le_add_right len |>.trans hsl)
    (prefixLift (v - start) len (by omega) b)

theorem intervalLift_injective (v start len : ℕ)
    (hsl : start + len ≤ v) :
    Function.Injective (intervalLift v start len hsl) := by
  intro a b hab
  apply prefixLift_injective (v - start) len (by omega)
  apply suffixLift_injective v start (by omega)
  exact hab

def intervalLiftEmbedding (v start len : ℕ) (hsl : start + len ≤ v) :
    (Fin len → ℕ) ↪ (Fin v → ℕ) :=
  ⟨intervalLift v start len hsl, intervalLift_injective v start len hsl⟩

theorem compositionFactorial_intervalLift
    (v start len : ℕ) (hsl : start + len ≤ v) (b : Fin len → ℕ) :
    compositionFactorial (intervalLift v start len hsl b) =
      compositionFactorial b := by
  rw [intervalLift, compositionFactorial_suffixLift,
    compositionFactorial_prefixLift]

theorem sum_intervalLift (v start len : ℕ) (hsl : start + len ≤ v)
    (b : Fin len → ℕ) :
    (∑ i, intervalLift v start len hsl b i) = ∑ i, b i := by
  rw [intervalLift, sum_suffixLift, sum_prefixLift]

theorem reciprocalFactorialMassOver_map_prefixLift
    {v p : ℕ} (hp : p ≤ v) (I : Finset (Fin p → ℕ)) :
    reciprocalFactorialMassOver (I.map (prefixLiftEmbedding v p hp)) =
      reciprocalFactorialMassOver I := by
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  change 1 / compositionFactorial (prefixLift v p hp a) = _
  rw [compositionFactorial_prefixLift]

theorem reciprocalFactorialMassOver_map_suffixLift
    {v p : ℕ} (hp : p ≤ v) (I : Finset (Fin (v - p) → ℕ)) :
    reciprocalFactorialMassOver (I.map (suffixLiftEmbedding v p hp)) =
      reciprocalFactorialMassOver I := by
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  change 1 / compositionFactorial (suffixLift v p hp a) = _
  rw [compositionFactorial_suffixLift]

theorem reciprocalFactorialMassOver_map_intervalLift
    {v start len : ℕ} (hsl : start + len ≤ v)
    (I : Finset (Fin len → ℕ)) :
    reciprocalFactorialMassOver (I.map
      (intervalLiftEmbedding v start len hsl)) =
      reciprocalFactorialMassOver I := by
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
    Finset.sum_map]
  apply Finset.sum_congr rfl
  intro a ha
  change 1 / compositionFactorial (intervalLift v start len hsl a) = _
  rw [compositionFactorial_intervalLift]

def compositionLeftPart (v p : ℕ) (hp : p ≤ v) (c : Fin v → ℕ) :
    Fin p → ℕ := ((splitAtCompositionEquiv v p hp).symm c).1

def compositionRightPart (v p : ℕ) (hp : p ≤ v) (c : Fin v → ℕ) :
    Fin (v - p) → ℕ := ((splitAtCompositionEquiv v p hp).symm c).2

theorem splitAt_leftRight (v p : ℕ) (hp : p ≤ v) (c : Fin v → ℕ) :
    splitAtCompositionEquiv v p hp
      (compositionLeftPart v p hp c, compositionRightPart v p hp c) = c := by
  exact (splitAtCompositionEquiv v p hp).apply_symm_apply c

theorem occupancyPrefix_splitAt_le_crowding
    (v p : ℕ) (hp : p ≤ v)
    (a : Fin p → ℕ) (b : Fin (v - p) → ℕ)
    {t : ℕ} (ht : t ≤ p) :
    occupancyPrefix (splitAtCompositionEquiv v p hp (a, b)) t =
      occupancyPrefix a t := by
  rw [occupancyPrefix_eq_sum_take_ofFn,
    ofFn_splitAtCompositionEquiv, List.take_append_of_le_length]
  · rw [occupancyPrefix_eq_sum_take_ofFn]
  · simpa using ht

theorem sum_compositionLeftPart (v p : ℕ) (hp : p ≤ v)
    (c : Fin v → ℕ) :
    (∑ i, compositionLeftPart v p hp c i) = occupancyPrefix c p := by
  rw [← occupancyPrefix_splitAt_left v p hp
    (compositionLeftPart v p hp c) (compositionRightPart v p hp c),
    splitAt_leftRight]

theorem sum_compositionRightPart (v p : ℕ) (hp : p ≤ v)
    (c : Fin v → ℕ) :
    (∑ i, compositionRightPart v p hp c i) =
      (∑ i, c i) - occupancyPrefix c p := by
  have hsum := sum_splitAtCompositionEquiv v p hp
    (compositionLeftPart v p hp c) (compositionRightPart v p hp c)
  rw [splitAt_leftRight, sum_compositionLeftPart] at hsum
  omega

theorem prefixLift_leftPart_eq_of_prefix_total
    {v p : ℕ} (hp : p ≤ v) {c : Fin v → ℕ}
    (hfull : occupancyPrefix c p = ∑ i, c i) :
    prefixLift v p hp (compositionLeftPart v p hp c) = c := by
  have hsumRight : ∑ i, compositionRightPart v p hp c i = 0 := by
    rw [sum_compositionRightPart, hfull, Nat.sub_self]
  have hright : compositionRightPart v p hp c = zeroComposition (v - p) := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ ↦ Nat.zero_le _)).mp hsumRight i (Finset.mem_univ i)
    simpa [zeroComposition] using hi
  rw [prefixLift, ← hright, splitAt_leftRight]

theorem suffixLift_rightPart_eq_of_prefix_zero
    {v p : ℕ} (hp : p ≤ v) {c : Fin v → ℕ}
    (hzero : occupancyPrefix c p = 0) :
    suffixLift v p hp (compositionRightPart v p hp c) = c := by
  have hsumLeft : ∑ i, compositionLeftPart v p hp c i = 0 := by
    rw [sum_compositionLeftPart, hzero]
  have hleft : compositionLeftPart v p hp c = zeroComposition p := by
    funext i
    have hi := (Finset.sum_eq_zero_iff_of_nonneg
      (fun _ _ ↦ Nat.zero_le _)).mp hsumLeft i (Finset.mem_univ i)
    simpa [zeroComposition] using hi
  rw [suffixLift, ← hleft, splitAt_leftRight]

theorem intervalLift_middlePart_eq_of_support
    {v start len : ℕ} (hsl : start + len ≤ v)
    {c : Fin v → ℕ}
    (hleft : occupancyPrefix c start = 0)
    (hright : occupancyPrefix c (start + len) = ∑ i, c i) :
    intervalLift v start len hsl
      (compositionLeftPart (v - start) len (by omega)
        (compositionRightPart v start (by omega) c)) = c := by
  let tail := compositionRightPart v start (by omega) c
  have htailLift : suffixLift v start (by omega) tail = c :=
    suffixLift_rightPart_eq_of_prefix_zero (by omega) hleft
  have hprefTail : occupancyPrefix tail len = ∑ i, tail i := by
    have hadd := occupancyPrefix_splitAt_add v start (by omega)
      (compositionLeftPart v start (by omega) c) tail
      (show len ≤ v - start by omega)
    rw [splitAt_leftRight] at hadd
    have hsumTail := sum_compositionRightPart v start (by omega) c
    rw [hleft, Nat.sub_zero] at hsumTail
    rw [hright, sum_compositionLeftPart, hleft, zero_add] at hadd
    exact (hsumTail.trans hadd).symm
  rw [intervalLift]
  change suffixLift v start _
      (prefixLift (v - start) len _
        (compositionLeftPart (v - start) len _ tail)) = c
  rw [prefixLift_leftPart_eq_of_prefix_total _ hprefTail]
  exact htailLift

/-! ## The fixed-rank crowding event -/

/-- Finite occupancy form of (32f).  The `l`-th object lies in cell
`l-u`, while the `(l-g)`-th object lies no earlier than cell `l-u-s`.
The first condition uses the right endpoint of the half-open cell. -/
def fordCrowdingOccupanciesAt (k u v g s l : ℕ) :
    Finset (Fin v → ℕ) :=
  (smirnovOccupancies k u v).filter fun c ↦
    l ≤ occupancyPrefix c (l - u + 1) ∧
      occupancyPrefix c (l - u - s) < l - g

theorem mem_fordCrowdingOccupanciesAt
    {k u v g s l : ℕ} {c : Fin v → ℕ} :
    c ∈ fordCrowdingOccupanciesAt k u v g s l ↔
      c ∈ smirnovOccupancies k u v ∧
      l ≤ occupancyPrefix c (l - u + 1) ∧
      occupancyPrefix c (l - u - s) < l - g := by
  simp [fordCrowdingOccupanciesAt]

/-- The four rank pieces used in Ford's split. -/
def crowdingRankCode {v : ℕ} (c : Fin v → ℕ) (g l : ℕ) :
    (Fin v → ℕ) × (Fin v → ℕ) ×
      (Fin v → ℕ) × (Fin v → ℕ) :=
  (occupancyTake c (l - g - 1),
    occupancyRankInterval c (l - g - 1) (l - 1),
    occupancyRankInterval c (l - 1) l,
    occupancyDrop c l)

theorem crowdingRankCode_reassembles
    {v : ℕ} (c : Fin v → ℕ) {g l : ℕ} (hgl : g + 1 ≤ l)
    (i : Fin v) :
    (crowdingRankCode c g l).1 i +
        (crowdingRankCode c g l).2.1 i +
        (crowdingRankCode c g l).2.2.1 i +
        (crowdingRankCode c g l).2.2.2 i = c i := by
  have hA : l - g - 1 ≤ l - 1 := by omega
  have hB : l - 1 ≤ l := by omega
  have hab := occupancyTake_add_rankInterval c hA i
  have habc := occupancyTake_add_rankInterval c hB i
  have habcd := occupancyTake_add_drop c l i
  dsimp [crowdingRankCode]
  omega

theorem crowdingRankCode_injective_on
    {v g l : ℕ} (hgl : g + 1 ≤ l) :
    Set.InjOn (fun c : Fin v → ℕ ↦ crowdingRankCode c g l) Set.univ := by
  intro c hc d hd hcode
  funext i
  have hcSum := crowdingRankCode_reassembles c hgl i
  have hdSum := crowdingRankCode_reassembles d hgl i
  change crowdingRankCode c g l = crowdingRankCode d g l at hcode
  rw [hcode] at hcSum
  omega

theorem occupancyPrefix_occupancyRankInterval
    {v : ℕ} (c : Fin v → ℕ) {a b q : ℕ}
    (hab : a ≤ b) (hq : q ≤ v) :
    occupancyPrefix (occupancyRankInterval c a b) q =
      min (occupancyPrefix c q) b - min (occupancyPrefix c q) a := by
  have hpoint := fun i : Fin v ↦ occupancyTake_add_rankInterval c hab i
  have hprefAdd : occupancyPrefix (occupancyTake c a) q +
      occupancyPrefix (occupancyRankInterval c a b) q =
        occupancyPrefix (occupancyTake c b) q := by
    simp only [occupancyPrefix]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
  rw [occupancyPrefix_occupancyTake c a hq,
    occupancyPrefix_occupancyTake c b hq] at hprefAdd
  omega

theorem occupancyPrefix_occupancyDrop
    {v : ℕ} (c : Fin v → ℕ) {n q : ℕ} (hq : q ≤ v) :
    occupancyPrefix (occupancyDrop c n) q =
      occupancyPrefix c q - min (occupancyPrefix c q) n := by
  have hpoint := fun i : Fin v ↦ occupancyTake_add_drop c n i
  have hprefAdd : occupancyPrefix (occupancyTake c n) q +
      occupancyPrefix (occupancyDrop c n) q = occupancyPrefix c q := by
    simp only [occupancyPrefix]
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl (fun i _ ↦ hpoint i)
  rw [occupancyPrefix_occupancyTake c n hq] at hprefAdd
  omega

private theorem crowding_prefix_before_crossing
    {k u v g s l : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordCrowdingOccupanciesAt k u v g s l)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l)
    (hul : u ≤ l) (hhv : l - u < v) :
    occupancyPrefix c (l - u) < l := by
  by_cases hzero : l - u = 0
  · rw [hzero, occupancyPrefix_zero]
    omega
  · have hbar := (mem_smirnovOccupancies.mp
      (mem_fordCrowdingOccupanciesAt.mp hc).1).2
      (l - u) (by omega) (by omega)
    omega

theorem crowding_firstPart_mem
    {k u v g s l : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordCrowdingOccupanciesAt k u v g s l)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    occupancyTake c (l - g - 1) ∈
      (smirnovOccupancies (l - g - 1) u (l - u + 1)).map
        (prefixLiftEmbedding v (l - u + 1) (by omega)) := by
  let A := occupancyTake c (l - g - 1)
  let p := l - u + 1
  have hcData := mem_fordCrowdingOccupanciesAt.mp hc
  have hsumC := (mem_smirnovOccupancies.mp hcData.1).1
  have hA_le : l - g - 1 ≤ k := by omega
  have hsumA : ∑ i, A i = l - g - 1 := by
    simpa [A, hsumC, min_eq_right hA_le] using
      sum_occupancyTake c (l - g - 1)
  have hprefA : occupancyPrefix A p = l - g - 1 := by
    change occupancyPrefix (occupancyTake c (l - g - 1)) p = _
    rw [occupancyPrefix_occupancyTake c (l - g - 1) (by omega)]
    have hprefC : l ≤ occupancyPrefix c p := by
      simpa [p] using hcData.2.1
    rw [min_eq_right]
    omega
  let a := compositionLeftPart v p (by omega) A
  have haSum : ∑ i, a i = l - g - 1 := by
    change (∑ i, compositionLeftPart v p _ A i) = _
    rw [sum_compositionLeftPart, hprefA]
  have haBarrier : ∀ t : ℕ, 1 ≤ t → t ≤ p →
      occupancyPrefix a t < u + t := by
    intro t ht htp
    have hsplit := occupancyPrefix_splitAt_le_crowding v p (by omega)
      a (compositionRightPart v p (by omega) A) htp
    rw [splitAt_leftRight] at hsplit
    have htake := occupancyPrefix_occupancyTake c (l - g - 1)
      (show t ≤ v by omega)
    have hbar := (mem_smirnovOccupancies.mp hcData.1).2 t ht (by omega)
    rw [← hsplit, htake]
    exact (min_le_left _ _).trans_lt hbar
  have haMem : a ∈ smirnovOccupancies (l - g - 1) u p :=
    mem_smirnovOccupancies.mpr ⟨haSum, haBarrier⟩
  apply Finset.mem_map.mpr
  refine ⟨a, ?_, ?_⟩
  · simpa [p] using haMem
  · change prefixLift v p _ a = A
    exact prefixLift_leftPart_eq_of_prefix_total _ (by
      rw [hprefA, hsumA])

theorem crowding_middlePart_mem
    {k u v g s l : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordCrowdingOccupanciesAt k u v g s l)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    occupancyRankInterval c (l - g - 1) (l - 1) ∈
      (compositionsOf ((l - u + 1) - (l - u - s)) g).map
        (intervalLiftEmbedding v (l - u - s)
          ((l - u + 1) - (l - u - s)) (by omega)) := by
  let B := occupancyRankInterval c (l - g - 1) (l - 1)
  let start := l - u - s
  let len := (l - u + 1) - start
  have hsl : start + len ≤ v := by dsimp [start, len]; omega
  have hcData := mem_fordCrowdingOccupanciesAt.mp hc
  have hsumC := (mem_smirnovOccupancies.mp hcData.1).1
  have hab : l - g - 1 ≤ l - 1 := by omega
  have hbTotal : ∑ i, B i = g := by
    have := sum_occupancyRankInterval hsumC hab (show l - 1 ≤ k by omega)
    change (∑ i, occupancyRankInterval c (l - g - 1) (l - 1) i) = g
    rw [this]
    omega
  have hleft : occupancyPrefix B start = 0 := by
    change occupancyPrefix
      (occupancyRankInterval c (l - g - 1) (l - 1)) start = 0
    rw [occupancyPrefix_occupancyRankInterval c hab (by omega)]
    have hpref := hcData.2.2
    have hprefLe : occupancyPrefix c start ≤ l - g - 1 := by
      simpa [start] using (Nat.le_pred_of_lt hpref)
    rw [min_eq_left (hprefLe.trans (by omega)), min_eq_left hprefLe,
      Nat.sub_self]
  have hright : occupancyPrefix B (start + len) = ∑ i, B i := by
    have hstartLen : start + len = l - u + 1 := by
      dsimp [start, len]
      omega
    change occupancyPrefix
      (occupancyRankInterval c (l - g - 1) (l - 1)) (start + len) = _
    rw [hstartLen,
      occupancyPrefix_occupancyRankInterval c hab (by omega), hbTotal]
    have hpref := hcData.2.1
    rw [min_eq_right (by omega : l - 1 ≤ occupancyPrefix c (l - u + 1)),
      min_eq_right (by omega : l - g - 1 ≤ occupancyPrefix c (l - u + 1))]
    omega
  let b := compositionLeftPart (v - start) len (by omega)
    (compositionRightPart v start (by omega) B)
  have hbSum : ∑ i, b i = g := by
    have hlift := intervalLift_middlePart_eq_of_support (c := B)
      hsl hleft hright
    rw [← hbTotal, ← hlift, sum_intervalLift]
  apply Finset.mem_map.mpr
  refine ⟨b, ?_, ?_⟩
  · exact mem_compositionsOf.mpr hbSum
  · change intervalLift v start len hsl b = B
    exact intervalLift_middlePart_eq_of_support
      hsl hleft hright

theorem crowding_crossingPart_mem
    {k u v g s l : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordCrowdingOccupanciesAt k u v g s l)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    occupancyRankInterval c (l - 1) l ∈
      (compositionsOf 1 1).map
        (intervalLiftEmbedding v (l - u) 1 (by omega)) := by
  let C := occupancyRankInterval c (l - 1) l
  let start := l - u
  have hcData := mem_fordCrowdingOccupanciesAt.mp hc
  have hsumC := (mem_smirnovOccupancies.mp hcData.1).1
  have hab : l - 1 ≤ l := by omega
  have hCTotal : ∑ i, C i = 1 := by
    have hsum := sum_occupancyRankInterval hsumC hab hlk
    change (∑ i, occupancyRankInterval c (l - 1) l i) = 1
    rw [hsum]
    omega
  have hleft : occupancyPrefix C start = 0 := by
    change occupancyPrefix (occupancyRankInterval c (l - 1) l) start = 0
    rw [occupancyPrefix_occupancyRankInterval c hab (by omega)]
    have hpref := crowding_prefix_before_crossing hc hg hgl hul hhv
    change occupancyPrefix c (l - u) < l at hpref
    have hpref' : occupancyPrefix c start < l := by simpa [start] using hpref
    have hprefLe : occupancyPrefix c start ≤ l - 1 := by omega
    rw [min_eq_left (hprefLe.trans (by omega)), min_eq_left hprefLe,
      Nat.sub_self]
  have hright : occupancyPrefix C (start + 1) = ∑ i, C i := by
    change occupancyPrefix (occupancyRankInterval c (l - 1) l) (start + 1) = _
    rw [occupancyPrefix_occupancyRankInterval c hab (by omega), hCTotal]
    have hpref : l ≤ occupancyPrefix c (start + 1) := by
      simpa [start] using hcData.2.1
    rw [min_eq_right hpref, min_eq_right (by omega)]
    omega
  let e := compositionLeftPart (v - start) 1 (by omega)
    (compositionRightPart v start (by omega) C)
  have heSum : ∑ i, e i = 1 := by
    have hlift := intervalLift_middlePart_eq_of_support (c := C)
      (show start + 1 ≤ v by omega) hleft hright
    have hsum := congrArg (fun x : Fin v → ℕ ↦ ∑ i, x i) hlift
    rw [sum_intervalLift, hCTotal] at hsum
    exact hsum
  apply Finset.mem_map.mpr
  refine ⟨e, mem_compositionsOf.mpr heSum, ?_⟩
  change intervalLift v start 1 (by omega) e = C
  exact intervalLift_middlePart_eq_of_support (by omega) hleft hright

theorem crowding_suffixPart_mem
    {k u v g s l : ℕ} {c : Fin v → ℕ}
    (hc : c ∈ fordCrowdingOccupanciesAt k u v g s l)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    occupancyDrop c l ∈
      (smirnovOccupancies (k - l) 0 (v - (l - u))).map
        (suffixLiftEmbedding v (l - u) (by omega)) := by
  let D := occupancyDrop c l
  let start := l - u
  have hcData := mem_fordCrowdingOccupanciesAt.mp hc
  have hsumC := (mem_smirnovOccupancies.mp hcData.1).1
  have hsumD : ∑ i, D i = k - l := by
    simpa [D] using sum_occupancyDrop hsumC hlk
  have hleft : occupancyPrefix D start = 0 := by
    change occupancyPrefix (occupancyDrop c l) start = 0
    rw [occupancyPrefix_occupancyDrop c (show start ≤ v by omega)]
    have hpref := crowding_prefix_before_crossing hc hg hgl hul hhv
    change occupancyPrefix c (l - u) < l at hpref
    have hpref' : occupancyPrefix c start < l := by simpa [start] using hpref
    rw [min_eq_left (by omega : occupancyPrefix c start ≤ l), Nat.sub_self]
  let d := compositionRightPart v start (by omega) D
  have hdSum : ∑ i, d i = k - l := by
    change (∑ i, compositionRightPart v start _ D i) = k - l
    rw [sum_compositionRightPart, hleft, Nat.sub_zero, hsumD]
  have hdBarrier : ∀ t : ℕ, 1 ≤ t → t ≤ v - start →
      occupancyPrefix d t < 0 + t := by
    intro t ht htv
    have hsplit := occupancyPrefix_splitAt_add v start (by omega)
      (compositionLeftPart v start (by omega) D) d htv
    rw [splitAt_leftRight] at hsplit
    have hleftSum : ∑ i, compositionLeftPart v start (by omega) D i = 0 := by
      rw [sum_compositionLeftPart, hleft]
    rw [hleftSum, zero_add] at hsplit
    have hdrop := occupancyPrefix_occupancyDrop c
      (n := l) (q := start + t) (show start + t ≤ v by omega)
    have hprefLower : l ≤ occupancyPrefix c (start + t) := by
      have hmono := occupancyPrefix_mono c
        (show start + 1 ≤ start + t by omega)
      exact hcData.2.1.trans hmono
    have hbar := (mem_smirnovOccupancies.mp hcData.1).2
      (start + t) (by omega) (by omega)
    rw [← hsplit, hdrop, min_eq_right hprefLower]
    omega
  have hdMem : d ∈ smirnovOccupancies (k - l) 0 (v - start) :=
    mem_smirnovOccupancies.mpr ⟨hdSum, hdBarrier⟩
  apply Finset.mem_map.mpr
  refine ⟨d, ?_, ?_⟩
  · simpa [start] using hdMem
  · change suffixLift v start _ d = D
    exact suffixLift_rightPart_eq_of_prefix_zero _ hleft

theorem inv_compositionFactorial_le_four_of_pointwise_add
    {v : ℕ} (a b e d c : Fin v → ℕ)
    (hc : ∀ i, a i + b i + e i + d i = c i) :
    1 / compositionFactorial c ≤
      (1 / compositionFactorial a) *
        (1 / compositionFactorial b) *
        (1 / compositionFactorial e) *
        (1 / compositionFactorial d) := by
  let ab : Fin v → ℕ := fun i ↦ a i + b i
  let abe : Fin v → ℕ := fun i ↦ ab i + e i
  have hfacPos : ∀ x : Fin v → ℕ, 0 < compositionFactorial x := by
    intro x
    dsimp [compositionFactorial]
    positivity
  have hab : compositionFactorial a * compositionFactorial b ≤
      compositionFactorial ab :=
    compositionFactorial_mul_le_of_pointwise_add a b ab (by
      intro i; rfl)
  have habe0 : compositionFactorial ab * compositionFactorial e ≤
      compositionFactorial abe :=
    compositionFactorial_mul_le_of_pointwise_add ab e abe (by
      intro i; rfl)
  have habNonneg : 0 ≤ compositionFactorial a * compositionFactorial b := by
    exact mul_nonneg (hfacPos a).le (hfacPos b).le
  have heNonneg : 0 ≤ compositionFactorial e := (hfacPos e).le
  have habe : compositionFactorial a * compositionFactorial b *
      compositionFactorial e ≤ compositionFactorial abe := by
    exact (mul_le_mul_of_nonneg_right hab heNonneg).trans habe0
  have habed0 : compositionFactorial abe * compositionFactorial d ≤
      compositionFactorial c :=
    compositionFactorial_mul_le_of_pointwise_add abe d c (by
      intro i
      dsimp [abe, ab]
      exact hc i)
  have hdNonneg : 0 ≤ compositionFactorial d := (hfacPos d).le
  have habed : compositionFactorial a * compositionFactorial b *
      compositionFactorial e * compositionFactorial d ≤
      compositionFactorial c :=
    (mul_le_mul_of_nonneg_right habe hdNonneg).trans habed0
  have hdenPos : 0 < compositionFactorial a * compositionFactorial b *
      compositionFactorial e * compositionFactorial d := by
    exact mul_pos (mul_pos (mul_pos (hfacPos a) (hfacPos b)) (hfacPos e))
      (hfacPos d)
  have hinv := one_div_le_one_div_of_le hdenPos habed
  calc
    1 / compositionFactorial c ≤
        1 / (compositionFactorial a * compositionFactorial b *
          compositionFactorial e * compositionFactorial d) := hinv
    _ = (1 / compositionFactorial a) *
        (1 / compositionFactorial b) *
        (1 / compositionFactorial e) *
        (1 / compositionFactorial d) := by field_simp

theorem crowdingRankCode_weight_bound
    {v : ℕ} (c : Fin v → ℕ) {g l : ℕ} (hgl : g + 1 ≤ l) :
    1 / compositionFactorial c ≤
      (1 / compositionFactorial (crowdingRankCode c g l).1) *
      (1 / compositionFactorial (crowdingRankCode c g l).2.1) *
      (1 / compositionFactorial (crowdingRankCode c g l).2.2.1) *
      (1 / compositionFactorial (crowdingRankCode c g l).2.2.2) := by
  exact inv_compositionFactorial_le_four_of_pointwise_add _ _ _ _ c
    (crowdingRankCode_reassembles c hgl)

private noncomputable def fourCompositionWeight {v : ℕ}
    (z : (Fin v → ℕ) × (Fin v → ℕ) ×
      (Fin v → ℕ) × (Fin v → ℕ)) : ℝ :=
  (1 / compositionFactorial z.1) *
    (1 / compositionFactorial z.2.1) *
    (1 / compositionFactorial z.2.2.1) *
    (1 / compositionFactorial z.2.2.2)

theorem reciprocalFactorialMassOver_le_fourFamilies
    {v g l : ℕ} (hgl : g + 1 ≤ l)
    (I A B E D : Finset (Fin v → ℕ))
    (hcode : ∀ c ∈ I,
      (crowdingRankCode c g l).1 ∈ A ∧
      (crowdingRankCode c g l).2.1 ∈ B ∧
      (crowdingRankCode c g l).2.2.1 ∈ E ∧
      (crowdingRankCode c g l).2.2.2 ∈ D) :
    reciprocalFactorialMassOver I ≤
      reciprocalFactorialMassOver A * reciprocalFactorialMassOver B *
        reciprocalFactorialMassOver E * reciprocalFactorialMassOver D := by
  classical
  let J := I.image (fun c ↦ crowdingRankCode c g l)
  let Cert := A.product (B.product (E.product D))
  have hJCert : J ⊆ Cert := by
    intro z hz
    change z ∈ I.image (fun c ↦ crowdingRankCode c g l) at hz
    obtain ⟨c, hcI, rfl⟩ := Finset.mem_image.mp hz
    have hm := hcode c hcI
    change crowdingRankCode c g l ∈ A.product (B.product (E.product D))
    apply Finset.mem_product.mpr
    refine ⟨hm.1, ?_⟩
    apply Finset.mem_product.mpr
    refine ⟨hm.2.1, ?_⟩
    exact Finset.mem_product.mpr ⟨hm.2.2.1, hm.2.2.2⟩
  have hnonneg : ∀ z :
      ((Fin v → ℕ) × (Fin v → ℕ) ×
        (Fin v → ℕ) × (Fin v → ℕ)),
      0 ≤ fourCompositionWeight z := by
    intro z
    dsimp [fourCompositionWeight]
    have hinv : ∀ x : Fin v → ℕ, 0 ≤ 1 / compositionFactorial x := by
      intro x
      apply one_div_nonneg.mpr
      dsimp [compositionFactorial]
      positivity
    exact mul_nonneg (mul_nonneg (mul_nonneg (hinv z.1) (hinv z.2.1))
      (hinv z.2.2.1)) (hinv z.2.2.2)
  calc
    reciprocalFactorialMassOver I ≤
        ∑ c ∈ I, fourCompositionWeight (crowdingRankCode c g l) := by
      rw [reciprocalFactorialMassOver]
      apply Finset.sum_le_sum
      intro c hc
      exact crowdingRankCode_weight_bound c hgl
    _ = ∑ z ∈ J, fourCompositionWeight z := by
      change (∑ c ∈ I, fourCompositionWeight (crowdingRankCode c g l)) =
        ∑ z ∈ I.image (fun c ↦ crowdingRankCode c g l),
          fourCompositionWeight z
      symm
      apply Finset.sum_image
      intro c hc d hd hcd
      exact crowdingRankCode_injective_on hgl (Set.mem_univ c)
        (Set.mem_univ d) hcd
    _ ≤ ∑ z ∈ Cert, fourCompositionWeight z :=
      Finset.sum_le_sum_of_subset_of_nonneg hJCert
        (fun z hz hnot ↦ hnonneg z)
    _ = reciprocalFactorialMassOver A * reciprocalFactorialMassOver B *
        reciprocalFactorialMassOver E * reciprocalFactorialMassOver D := by
      change (A.product (B.product (E.product D))).sum
        fourCompositionWeight = _
      have hprod := Finset.sum_product A (B.product (E.product D))
        fourCompositionWeight
      have hprod' : (A.product (B.product (E.product D))).sum
          fourCompositionWeight =
          ∑ x ∈ A, ∑ y ∈ B.product (E.product D),
            fourCompositionWeight (x, y) := by
        exact hprod
      rw [hprod']
      rw [reciprocalFactorialMassOver,
        reciprocalFactorialMassOver, reciprocalFactorialMassOver,
        reciprocalFactorialMassOver]
      have hprodB (a : Fin v → ℕ) :
          (B.product (E.product D)).sum
              (fun y ↦ fourCompositionWeight (a, y)) =
            ∑ b ∈ B, ∑ z ∈ E.product D,
              fourCompositionWeight (a, b, z) := by
        exact Finset.sum_product B (E.product D)
          (fun y ↦ fourCompositionWeight (a, y))
      simp_rw [hprodB]
      have hprodE (a b : Fin v → ℕ) :
          (E.product D).sum
              (fun z ↦ fourCompositionWeight (a, b, z)) =
            ∑ e ∈ E, ∑ d ∈ D,
              fourCompositionWeight (a, b, e, d) := by
        exact Finset.sum_product E D
          (fun z ↦ fourCompositionWeight (a, b, z))
      simp_rw [hprodE]
      simp only [fourCompositionWeight]
      symm
      rw [Finset.sum_mul, Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro a ha
      rw [Finset.mul_sum B
        (fun b ↦ 1 / compositionFactorial b)
        (1 / compositionFactorial a)]
      rw [Finset.sum_mul, Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro b hb
      rw [Finset.mul_sum E
        (fun e ↦ 1 / compositionFactorial e)
        ((1 / compositionFactorial a) * (1 / compositionFactorial b))]
      rw [Finset.sum_mul]
      apply Finset.sum_congr rfl
      intro e he
      rw [Finset.mul_sum D
        (fun d ↦ 1 / compositionFactorial d)
        ((1 / compositionFactorial a) * (1 / compositionFactorial b) *
          (1 / compositionFactorial e))]

/-! ## The fixed-rank four-factor estimate -/

/-- Reciprocal-factorial form of Ford's four-way split at ranks
`l-g-1`, `l-1`, and `l`.  The two Smirnov factors keep their exact
normalizations; the middle factor is the exponential multinomial mass of
`g` objects in the permitted interval of cells, and the crossing object has
mass one. -/
theorem reciprocalFactorialMassOver_fordCrowdingOccupanciesAt_le
    {k u v g s l : ℕ}
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l)
    (hlk : l ≤ k) (hhv : l - u < v) :
    reciprocalFactorialMassOver
        (fordCrowdingOccupanciesAt k u v g s l) ≤
      smirnovOccupancyMass (l - g - 1) u (l - u + 1) *
        (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
            (g.factorial : ℝ)) *
          smirnovOccupancyMass (k - l) 0 (v - (l - u))) := by
  let A := (smirnovOccupancies (l - g - 1) u (l - u + 1)).map
    (prefixLiftEmbedding v (l - u + 1) (by omega))
  let B := (compositionsOf ((l - u + 1) - (l - u - s)) g).map
    (intervalLiftEmbedding v (l - u - s)
      ((l - u + 1) - (l - u - s)) (by omega))
  let E := (compositionsOf 1 1).map
    (intervalLiftEmbedding v (l - u) 1 (by omega))
  let D := (smirnovOccupancies (k - l) 0 (v - (l - u))).map
    (suffixLiftEmbedding v (l - u) (by omega))
  have hfour := reciprocalFactorialMassOver_le_fourFamilies hgl
    (fordCrowdingOccupanciesAt k u v g s l) A B E D (by
      intro c hc
      exact ⟨crowding_firstPart_mem hc hg hgl hul hlk hhv,
        crowding_middlePart_mem hc hg hgl hul hlk hhv,
        crowding_crossingPart_mem hc hg hgl hul hlk hhv,
        crowding_suffixPart_mem hc hg hgl hul hlk hhv⟩)
  apply hfour.trans_eq
  dsimp only [A, B, E, D]
  rw [reciprocalFactorialMassOver_map_prefixLift,
    reciprocalFactorialMassOver_map_intervalLift,
    reciprocalFactorialMassOver_map_intervalLift,
    reciprocalFactorialMassOver_map_suffixLift]
  change smirnovOccupancyMass (l - g - 1) u (l - u + 1) *
      reciprocalFactorialMassOver
        (compositionsOf ((l - u + 1) - (l - u - s)) g) *
      reciprocalFactorialMassOver (compositionsOf 1 1) *
      smirnovOccupancyMass (k - l) 0 (v - (l - u)) = _
  rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
    sum_inv_compositionFactorial_compositionsOf,
    sum_inv_compositionFactorial_compositionsOf]
  norm_num
  ring

end Erdos446
