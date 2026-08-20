/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.SmirnovNumerics
import Mathlib.Data.List.Rotate

/-!
# Erdős Problem 446: Raney's finite cycle lemma

The zero-offset Smirnov occupancy mass is evaluated by Raney's cycle lemma.
We formulate the lemma for an integer walk whose increments are at most one:
if its total rise is the positive integer `w`, exactly `w` indexed cyclic
starts have every nonempty partial sum positive.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- Sum of the first `r` increments of an integer list. -/
def intPrefixSum (x : List ℤ) (r : ℕ) : ℤ :=
  (x.take r).sum

theorem intPrefixSum_zero (x : List ℤ) : intPrefixSum x 0 = 0 := by
  simp [intPrefixSum]

theorem intPrefixSum_length (x : List ℤ) :
    intPrefixSum x x.length = x.sum := by
  simp [intPrefixSum]

theorem intPrefixSum_succ {x : List ℤ} {r : ℕ} (hr : r < x.length) :
    intPrefixSum x (r + 1) = intPrefixSum x r + x[r] := by
  rw [intPrefixSum, intPrefixSum, List.take_succ_eq_append_getElem hr,
    List.sum_append]
  simp

/-- A discrete intermediate-value lemma for walks whose upward increments
are at most one. -/
theorem exists_eq_of_le_of_lt_of_step_le_one
    (f : ℕ → ℤ) {a b : ℕ} {z : ℤ} (hab : a ≤ b)
    (haz : f a ≤ z) (hzb : z < f b)
    (hstep : ∀ i, a ≤ i → i < b → f (i + 1) ≤ f i + 1) :
    ∃ i, a ≤ i ∧ i < b ∧ f i = z := by
  let S := (Finset.Icc a b).filter fun i ↦ z < f i
  have hbS : b ∈ S := by
    simp [S, hab, hzb]
  have hSne : S.Nonempty := ⟨b, hbS⟩
  let j := S.min' hSne
  have hjS : j ∈ S := S.min'_mem hSne
  have hjBounds : a ≤ j ∧ j ≤ b := by
    exact (Finset.mem_Icc.mp (Finset.mem_filter.mp hjS).1)
  have hzj : z < f j := (Finset.mem_filter.mp hjS).2
  have haj : a < j := by
    have hne : a ≠ j := by
      intro h
      rw [← h] at hzj
      omega
    omega
  have hjPos : 0 < j := lt_of_le_of_lt (Nat.zero_le a) haj
  let i := j - 1
  have hij : i + 1 = j := by
    dsimp [i]
    omega
  have hai : a ≤ i := by
    dsimp [i]
    omega
  have hib : i < b := by
    dsimp [i]
    omega
  have hiNotS : i ∉ S := by
    intro hiS
    have hji : j ≤ i := S.min'_le i hiS
    omega
  have hzi : f i ≤ z := by
    have hiIcc : i ∈ Finset.Icc a b := Finset.mem_Icc.mpr ⟨hai, hib.le⟩
    have : ¬ z < f i := by
      intro h
      exact hiNotS (Finset.mem_filter.mpr ⟨hiIcc, h⟩)
    omega
  have hstepI : f j ≤ f i + 1 := by
    rw [← hij]
    exact hstep i hai hib
  refine ⟨i, hai, hib, ?_⟩
  omega

/-- Prefix levels strictly before the terminal endpoint. -/
def raneyPrefixLevels (x : List ℤ) : Finset ℤ :=
  (Finset.range x.length).image (intPrefixSum x)

theorem raneyPrefixLevels_nonempty {x : List ℤ} (hx : x ≠ []) :
    (raneyPrefixLevels x).Nonempty := by
  have hxlen : 0 < x.length := List.length_pos_iff.mpr hx
  exact ⟨0, Finset.mem_image.mpr
    ⟨0, Finset.mem_range.mpr hxlen, intPrefixSum_zero x⟩⟩

/-- Least proper-prefix level of the walk. -/
def raneyMin (x : List ℤ) (hx : x ≠ []) : ℤ :=
  (raneyPrefixLevels x).min' (raneyPrefixLevels_nonempty hx)

theorem raneyMin_mem (x : List ℤ) (hx : x ≠ []) :
    raneyMin x hx ∈ raneyPrefixLevels x := by
  exact (raneyPrefixLevels x).min'_mem (raneyPrefixLevels_nonempty hx)

theorem raneyMin_le_prefix (x : List ℤ) (hx : x ≠ [])
    {r : ℕ} (hr : r < x.length) :
    raneyMin x hx ≤ intPrefixSum x r := by
  apply (raneyPrefixLevels x).min'_le
  exact Finset.mem_image.mpr ⟨r, Finset.mem_range.mpr hr, rfl⟩

theorem raneyMin_le_zero (x : List ℤ) (hx : x ≠ []) :
    raneyMin x hx ≤ 0 := by
  have hxlen : 0 < x.length := List.length_pos_iff.mpr hx
  simpa [intPrefixSum_zero] using raneyMin_le_prefix x hx hxlen

/-- Proper prefix indices at a prescribed level. -/
def raneyLevelIndices (x : List ℤ) (z : ℤ) : Finset ℕ :=
  (Finset.range x.length).filter fun r ↦ intPrefixSum x r = z

/-- The last proper prefix at level `z`. -/
def raneyLastIndex (x : List ℤ) (z : ℤ)
    (hz : (raneyLevelIndices x z).Nonempty) : ℕ :=
  (raneyLevelIndices x z).max' hz

theorem raneyLastIndex_mem (x : List ℤ) (z : ℤ)
    (hz : (raneyLevelIndices x z).Nonempty) :
    raneyLastIndex x z hz ∈ raneyLevelIndices x z := by
  exact (raneyLevelIndices x z).max'_mem hz

theorem raneyLastIndex_lt_length (x : List ℤ) (z : ℤ)
    (hz : (raneyLevelIndices x z).Nonempty) :
    raneyLastIndex x z hz < x.length := by
  exact Finset.mem_range.mp
    (Finset.mem_filter.mp (raneyLastIndex_mem x z hz)).1

theorem intPrefixSum_raneyLastIndex (x : List ℤ) (z : ℤ)
    (hz : (raneyLevelIndices x z).Nonempty) :
    intPrefixSum x (raneyLastIndex x z hz) = z := by
  exact (Finset.mem_filter.mp (raneyLastIndex_mem x z hz)).2

theorem raneyLastIndex_last (x : List ℤ) (z : ℤ)
    (hz : (raneyLevelIndices x z).Nonempty) {t : ℕ}
    (ht : t < x.length)
    (hlt : raneyLastIndex x z hz < t) :
    intPrefixSum x t ≠ z := by
  intro htz
  have htmem : t ∈ raneyLevelIndices x z := by
    exact Finset.mem_filter.mpr ⟨Finset.mem_range.mpr ht, htz⟩
  have hle : t ≤ raneyLastIndex x z hz := by
    simpa [raneyLastIndex] using
      (raneyLevelIndices x z).le_max' t htmem
  omega

/-- Sum of `t` cyclic increments beginning at the proper-prefix index `r`. -/
def cyclicIntPrefixSum (x : List ℤ) (r t : ℕ) : ℤ :=
  if r + t ≤ x.length then
    intPrefixSum x (r + t) - intPrefixSum x r
  else
    x.sum - intPrefixSum x r + intPrefixSum x (r + t - x.length)

/-- An indexed cyclic start is Raney-good when every nonempty cyclic prefix
has positive sum. -/
def IsRaneyGoodStart (x : List ℤ) (r : ℕ) : Prop :=
  r < x.length ∧ ∀ t, 1 ≤ t → t ≤ x.length → 0 < cyclicIntPrefixSum x r t

/-- Finset of all indexed Raney-good starts. -/
noncomputable def raneyGoodStarts (x : List ℤ) : Finset ℕ := by
  classical
  exact (Finset.range x.length).filter (IsRaneyGoodStart x)

theorem mem_raneyGoodStarts {x : List ℤ} {r : ℕ} :
    r ∈ raneyGoodStarts x ↔ IsRaneyGoodStart x r := by
  classical
  simp [raneyGoodStarts, IsRaneyGoodStart]

/-! ## The canonical starts at the `w` consecutive levels above the minimum -/

theorem intPrefixSum_succ_le {x : List ℤ}
    (hentry : ∀ a ∈ x, a ≤ 1) {r : ℕ} (hr : r < x.length) :
    intPrefixSum x (r + 1) ≤ intPrefixSum x r + 1 := by
  rw [intPrefixSum_succ hr]
  have hx : x[r] ∈ x := List.getElem_mem hr
  linarith [hentry x[r] hx]

theorem raneyLevelIndices_min_add_nonempty
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    {q : ℕ} (hq : q < w) :
    (raneyLevelIndices x (raneyMin x hx + (q : ℤ))).Nonempty := by
  obtain ⟨r, hrRange, hrLevel⟩ :=
    Finset.mem_image.mp (raneyMin_mem x hx)
  have hr : r < x.length := Finset.mem_range.mp hrRange
  have hm0 : raneyMin x hx ≤ 0 := raneyMin_le_zero x hx
  have hzlt : raneyMin x hx + (q : ℤ) < intPrefixSum x x.length := by
    rw [intPrefixSum_length, hsum]
    have hqR : (q : ℤ) < (w : ℤ) := by exact_mod_cast hq
    omega
  obtain ⟨i, hri, hiLen, hiLevel⟩ :=
    exists_eq_of_le_of_lt_of_step_le_one (intPrefixSum x)
      (show r ≤ x.length from hr.le)
      (by rw [hrLevel]; omega) hzlt (by
        intro j hrj hj
        exact intPrefixSum_succ_le hentry hj)
  refine ⟨i, Finset.mem_filter.mpr ⟨Finset.mem_range.mpr hiLen, hiLevel⟩⟩

/-- The last occurrence of the `q`th level above the proper-prefix minimum. -/
noncomputable def raneyCanonicalStart
    (x : List ℤ) (w : ℕ) (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (q : Fin w) : ℕ :=
  raneyLastIndex x (raneyMin x hx + (q : ℤ))
    (raneyLevelIndices_min_add_nonempty hx hentry hsum q.isLt)

theorem raneyCanonicalStart_lt_length
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (q : Fin w) :
    raneyCanonicalStart x w hx hentry hsum q < x.length := by
  exact raneyLastIndex_lt_length _ _ _

theorem intPrefixSum_raneyCanonicalStart
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (q : Fin w) :
    intPrefixSum x (raneyCanonicalStart x w hx hentry hsum q) =
      raneyMin x hx + (q : ℤ) := by
  exact intPrefixSum_raneyLastIndex _ _ _

theorem raneyCanonicalStart_last
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (q : Fin w) {t : ℕ} (ht : t < x.length)
    (hlt : raneyCanonicalStart x w hx hentry hsum q < t) :
    intPrefixSum x t ≠ raneyMin x hx + (q : ℤ) := by
  exact raneyLastIndex_last _ _ _ ht hlt

theorem raneyCanonicalStart_injective
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ)) :
    Function.Injective (raneyCanonicalStart x w hx hentry hsum) := by
  intro q q' hqq'
  have hlevels := congrArg (intPrefixSum x) hqq'
  rw [intPrefixSum_raneyCanonicalStart,
    intPrefixSum_raneyCanonicalStart] at hlevels
  apply Fin.ext
  exact_mod_cast (add_left_cancel hlevels)

theorem isRaneyGoodStart_raneyCanonicalStart
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (q : Fin w) :
    IsRaneyGoodStart x (raneyCanonicalStart x w hx hentry hsum q) := by
  let r := raneyCanonicalStart x w hx hentry hsum q
  let m := raneyMin x hx
  let z : ℤ := m + (q : ℤ)
  have hr : r < x.length := raneyCanonicalStart_lt_length hx hentry hsum q
  have hrLevel : intPrefixSum x r = z := by
    simpa [r, m, z] using
      intPrefixSum_raneyCanonicalStart hx hentry hsum q
  have hm0 : m ≤ 0 := by simpa [m] using raneyMin_le_zero x hx
  have hqR : (q : ℤ) < (w : ℤ) := by exact_mod_cast q.isLt
  have hzlt : z < intPrefixSum x x.length := by
    rw [intPrefixSum_length, hsum]
    dsimp [z]
    omega
  refine ⟨hr, ?_⟩
  intro t ht htn
  change 0 < cyclicIntPrefixSum x r t
  by_cases hnowrap : r + t ≤ x.length
  · rw [cyclicIntPrefixSum, if_pos hnowrap]
    have hrs : r < r + t := by omega
    have hsGreater : z < intPrefixSum x (r + t) := by
      by_contra hnot
      have hsle : intPrefixSum x (r + t) ≤ z := le_of_not_gt hnot
      obtain ⟨i, hsi, hiLen, hiLevel⟩ :=
        exists_eq_of_le_of_lt_of_step_le_one (intPrefixSum x)
          hnowrap hsle hzlt (by
            intro j hj _hjLen
            exact intPrefixSum_succ_le hentry _hjLen)
      exact raneyCanonicalStart_last hx hentry hsum q hiLen
        (lt_of_lt_of_le hrs hsi) hiLevel
    rw [hrLevel]
    omega
  · rw [cyclicIntPrefixSum, if_neg hnowrap, hsum, hrLevel]
    have hj : r + t - x.length < x.length := by omega
    have hmj : m ≤ intPrefixSum x (r + t - x.length) := by
      simpa [m] using raneyMin_le_prefix x hx hj
    dsimp [z]
    omega

theorem exists_prefix_eq_raneyMin (x : List ℤ) (hx : x ≠ []) :
    ∃ t, t < x.length ∧ intPrefixSum x t = raneyMin x hx := by
  obtain ⟨t, ht, hlevel⟩ := Finset.mem_image.mp (raneyMin_mem x hx)
  exact ⟨t, Finset.mem_range.mp ht, hlevel⟩

theorem exists_raneyCanonicalStart_eq_of_good
    {x : List ℤ} {w r : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (hw : 0 < w) (hrGood : IsRaneyGoodStart x r) :
    ∃ q : Fin w, raneyCanonicalStart x w hx hentry hsum q = r := by
  let m := raneyMin x hx
  let s := intPrefixSum x r
  have hr : r < x.length := hrGood.1
  have hms : m ≤ s := by
    simpa [m, s] using raneyMin_le_prefix x hx hr
  obtain ⟨t, ht, htLevel⟩ := exists_prefix_eq_raneyMin x hx
  have htr : t ≤ r := by
    by_contra hnot
    have hrt : r < t := lt_of_not_ge hnot
    have hdPos : 1 ≤ t - r := by omega
    have hdLen : t - r ≤ x.length := by omega
    have hgood := hrGood.2 (t - r) hdPos hdLen
    have hsumIndex : r + (t - r) = t := by omega
    have hnowrap : r + (t - r) ≤ x.length := by omega
    rw [cyclicIntPrefixSum, if_pos hnowrap, hsumIndex] at hgood
    dsimp [s, m] at hms
    rw [htLevel] at hgood
    omega
  have hsUpper : s < m + (w : ℤ) := by
    by_cases htrEq : t = r
    · subst t
      dsimp [s, m]
      rw [htLevel]
      have hwZ : (0 : ℤ) < (w : ℤ) := by exact_mod_cast hw
      omega
    · have htrLt : t < r := lt_of_le_of_ne htr htrEq
      let d := x.length - r + t
      have hdPos : 1 ≤ d := by
        dsimp [d]
        omega
      have hdLen : d ≤ x.length := by
        dsimp [d]
        omega
      have hgood := hrGood.2 d hdPos hdLen
      have hindex : r + d = x.length + t := by
        dsimp [d]
        omega
      rw [cyclicIntPrefixSum] at hgood
      by_cases hnowrap : r + d ≤ x.length
      · rw [if_pos hnowrap, hindex, show t = 0 by omega,
          Nat.add_zero, intPrefixSum_length, hsum] at hgood
        have hmzero : m = 0 := by
          rw [show t = 0 by omega, intPrefixSum_zero] at htLevel
          exact htLevel.symm
        dsimp [s]
        rw [hmzero]
        omega
      · rw [if_neg hnowrap, hsum, hindex,
          Nat.add_sub_cancel_left, htLevel] at hgood
        dsimp [s, m]
        omega
  let qNat := Int.toNat (s - m)
  have hqCast : (qNat : ℤ) = s - m := by
    dsimp [qNat]
    exact Int.toNat_of_nonneg (sub_nonneg.mpr hms)
  have hqLt : qNat < w := by
    exact_mod_cast (show (qNat : ℤ) < (w : ℤ) by omega)
  let q : Fin w := ⟨qNat, hqLt⟩
  refine ⟨q, ?_⟩
  let r' := raneyCanonicalStart x w hx hentry hsum q
  have hr' : r' < x.length := raneyCanonicalStart_lt_length hx hentry hsum q
  have hr'Level : intPrefixSum x r' = s := by
    have h := intPrefixSum_raneyCanonicalStart hx hentry hsum q
    change intPrefixSum x r' = _ at h
    dsimp [q] at h
    rw [show ((⟨qNat, hqLt⟩ : Fin w) : ℤ) = (qNat : ℤ) by rfl,
      hqCast] at h
    dsimp [s, m]
    omega
  have hnotBefore : ¬ r' < r := by
    intro hlt
    apply raneyCanonicalStart_last hx hentry hsum q hr hlt
    rw [← intPrefixSum_raneyCanonicalStart hx hentry hsum q, hr'Level]
  have hnotAfter : ¬ r < r' := by
    intro hlt
    have hdPos : 1 ≤ r' - r := by omega
    have hdLen : r' - r ≤ x.length := by omega
    have hgood := hrGood.2 (r' - r) hdPos hdLen
    have hindex : r + (r' - r) = r' := by omega
    have hnowrap : r + (r' - r) ≤ x.length := by omega
    rw [cyclicIntPrefixSum, if_pos hnowrap, hindex, hr'Level] at hgood
    dsimp [s] at hgood
    omega
  dsimp [r'] at hnotBefore hnotAfter ⊢
  omega

theorem mem_raneyGoodStarts_iff_canonical
    {x : List ℤ} {w r : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (hw : 0 < w) :
    r ∈ raneyGoodStarts x ↔
      ∃ q : Fin w, raneyCanonicalStart x w hx hentry hsum q = r := by
  rw [mem_raneyGoodStarts]
  constructor
  · exact exists_raneyCanonicalStart_eq_of_good hx hentry hsum hw
  · rintro ⟨q, rfl⟩
    exact isRaneyGoodStart_raneyCanonicalStart hx hentry hsum q

/-- Raney's cycle lemma: a walk with increments at most one and positive
integer total `w` has exactly `w` indexed cyclic starts whose nonempty
partial sums are all positive. -/
theorem card_raneyGoodStarts
    {x : List ℤ} {w : ℕ} (hx : x ≠ [])
    (hentry : ∀ a ∈ x, a ≤ 1) (hsum : x.sum = (w : ℤ))
    (hw : 0 < w) :
    (raneyGoodStarts x).card = w := by
  classical
  have hset : raneyGoodStarts x =
      (Finset.univ : Finset (Fin w)).image
        (raneyCanonicalStart x w hx hentry hsum) := by
    ext r
    rw [mem_raneyGoodStarts_iff_canonical hx hentry hsum hw]
    simp
  rw [hset, Finset.card_image_of_injective _
    (raneyCanonicalStart_injective hx hentry hsum)]
  simp

end Erdos446
