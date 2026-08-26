import Mathlib

/- Ported from Lean 4.31.0 to 4.33.0; imports and elaboration options adapted. -/
set_option autoImplicit true
set_option relaxedAutoImplicit true
set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

namespace Erdos489

open scoped BigOperators

/-- A gap of exact length `d` starts at `n` for predicate `q`. -/
def gapPattern (q : ℕ → Prop) (d n : ℕ) : Prop :=
  q n ∧ q (n + d) ∧ ∀ k, 0 < k → k < d → ¬q (n + k)

/-- Local squared-gap cost, truncated to lengths below `H`. -/
noncomputable def truncatedGapCost (q : ℕ → Prop) (H n : ℕ) : ℕ := by
  classical
  exact ∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0

/-- There is no predicate member strictly between consecutive terms of an
infinite predicate enumeration. -/
theorem nth_consecutive_no_mem
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (i n : ℕ) (hleft : Nat.nth q i < n)
    (hright : n < Nat.nth q (i + 1)) : ¬q n := by
  intro hn
  have hicount : i < Nat.count q n := (Nat.lt_nth_iff_count_lt hq).2 hleft
  have hidx : i + 1 ≤ Nat.count q n := by omega
  have hmono : Nat.nth q (i + 1) ≤ Nat.nth q (Nat.count q n) :=
    (Nat.nth_strictMono hq).monotone hidx
  have hnth : Nat.nth q (Nat.count q n) = n := Nat.nth_count hn
  rw [hnth] at hmono
  exact (not_lt_of_ge hmono) hright

/-- On an enumerated predicate point, the exact-gap word is equivalent to the
successive enumerated gap having that length. -/
theorem gapPattern_nth_iff_gap_eq
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (i d : ℕ) (hd : 0 < d) :
    gapPattern q d (Nat.nth q i) ↔
      Nat.nth q (i + 1) - Nat.nth q i = d := by
  have hbmono : StrictMono (Nat.nth q) := Nat.nth_strictMono hq
  have hbi : q (Nat.nth q i) := Nat.nth_mem_of_infinite hq i
  have hbi1 : q (Nat.nth q (i + 1)) := Nat.nth_mem_of_infinite hq (i + 1)
  constructor
  · rintro ⟨_, hend, hinterior⟩
    have hilt : Nat.nth q i < Nat.nth q i + d := by omega
    have hicount : i < Nat.count q (Nat.nth q i + d) :=
      (Nat.lt_nth_iff_count_lt hq).2 hilt
    have hidx : i + 1 ≤ Nat.count q (Nat.nth q i + d) := by omega
    have hnextle : Nat.nth q (i + 1) ≤ Nat.nth q i + d := by
      have hm : Nat.nth q (i + 1) ≤
          Nat.nth q (Nat.count q (Nat.nth q i + d)) :=
        hbmono.monotone hidx
      have hnth : Nat.nth q (Nat.count q (Nat.nth q i + d)) =
          Nat.nth q i + d := Nat.nth_count hend
      rwa [hnth] at hm
    have hnextge : Nat.nth q i + d ≤ Nat.nth q (i + 1) := by
      by_contra hnot
      have hstrict : Nat.nth q (i + 1) < Nat.nth q i + d := by omega
      let k := Nat.nth q (i + 1) - Nat.nth q i
      have hstep := hbmono (by omega : i < i + 1)
      have hkpos : 0 < k := Nat.sub_pos_of_lt hstep
      have hklt : k < d := by dsimp [k]; omega
      have hsum : Nat.nth q i + k = Nat.nth q (i + 1) := by
        dsimp [k]
        exact Nat.add_sub_of_le hstep.le
      exact hinterior k hkpos hklt (hsum ▸ hbi1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d :=
      le_antisymm hnextle hnextge
    omega
  · intro hgap
    have hstep := hbmono (by omega : i < i + 1)
    have heq : Nat.nth q (i + 1) = Nat.nth q i + d := by omega
    refine ⟨hbi, ?_, ?_⟩
    · rw [← heq]
      exact hbi1
    · intro k hk0 hkd hkq
      apply nth_consecutive_no_mem q hq i (Nat.nth q i + k)
      · omega
      · rw [heq]
        omega
      · exact hkq

/-- The local truncated cost at the `i`-th predicate member is exactly the
square of its next gap when that gap is below `H`, and zero otherwise. -/
theorem truncatedGapCost_nth
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (H i : ℕ) :
    truncatedGapCost q H (Nat.nth q i) =
      if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0 := by
  classical
  let g := Nat.nth q (i + 1) - Nat.nth q i
  have hg : 0 < g := Nat.sub_pos_of_lt (Nat.nth_strictMono hq (by omega))
  by_cases hgH : g < H
  · rw [if_pos hgH]
    unfold truncatedGapCost
    have hgmem : g ∈ Finset.Ico 1 H := Finset.mem_Ico.mpr ⟨hg, hgH⟩
    rw [Finset.sum_eq_single g]
    · rw [if_pos]
      exact gapPattern_nth_iff_gap_eq q hq i g hg |>.2 rfl
    · intro d hdmem hdne
      rw [if_neg]
      intro hpat
      have heq := (gapPattern_nth_iff_gap_eq q hq i d
        (by exact (Finset.mem_Ico.mp hdmem).1)).1 hpat
      exact hdne heq.symm
    · exact fun h => (h hgmem).elim
  · rw [if_neg hgH]
    unfold truncatedGapCost
    apply Finset.sum_eq_zero
    intro d hdmem
    rw [if_neg]
    intro hpat
    have heq := (gapPattern_nth_iff_gap_eq q hq i d
      (Finset.mem_Ico.mp hdmem).1).1 hpat
    have hdH := (Finset.mem_Ico.mp hdmem).2
    omega

/-- A local cost vanishes away from predicate members. -/
theorem truncatedGapCost_eq_zero_of_not
    (q : ℕ → Prop) (H n : ℕ) (hn : ¬q n) :
    truncatedGapCost q H n = 0 := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_eq_zero
  intro d hd
  rw [if_neg]
  exact fun h => hn h.1

/-- Exact-gap words inherit every period of the underlying predicate. -/
theorem gapPattern_periodic
    (q : ℕ → Prop) (P d : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (gapPattern q d) P := by
  intro n
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · simpa using hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega] at hend
      exact hp ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      have hh := hint k hk0 hkd
      rw [show n + P + k = n + k + P by omega] at hh
      exact hp ▸ hh
  · rintro ⟨hn, hend, hint⟩
    refine ⟨?_, ?_, ?_⟩
    · exact hq n ▸ hn
    · have hp := hq (n + d)
      rw [show n + P + d = n + d + P by omega]
      exact hp.symm ▸ hend
    · intro k hk0 hkd
      have hp := hq (n + k)
      rw [show n + P + k = n + k + P by omega]
      exact hp.symm ▸ hint k hk0 hkd

/-- Truncated local gap cost inherits every period of the predicate. -/
theorem truncatedGapCost_periodic
    (q : ℕ → Prop) (H P : ℕ) (hq : Function.Periodic q P) :
    Function.Periodic (truncatedGapCost q H) P := by
  intro n
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hp := gapPattern_periodic q P d hq n
  rw [hp]

/-- Agreement of two predicates throughout the inspected window forces equal
local truncated costs. -/
theorem truncatedGapCost_eq_of_window_agree
    (q r : ℕ → Prop) (H n : ℕ)
    (hagree : ∀ k, k ≤ H → (q (n + k) ↔ r (n + k))) :
    truncatedGapCost q H n = truncatedGapCost r H n := by
  classical
  unfold truncatedGapCost
  apply Finset.sum_congr rfl
  intro d hd
  have hdH := (Finset.mem_Ico.mp hd).2
  congr 1
  apply propext
  constructor
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mp hn),
      (hagree d hdH.le).mp hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mpr hk)
  · rintro ⟨hn, hend, hint⟩
    refine ⟨(by simpa using (hagree 0 (Nat.zero_le H)).mpr hn),
      (hagree d hdH.le).mpr hend, ?_⟩
    intro k hk0 hkd
    exact fun hk => hint k hk0 hkd ((hagree k (by omega)).mp hk)

/-- A crude uniform bound sufficient for approximation arguments. -/
theorem truncatedGapCost_le_cube (q : ℕ → Prop) (H n : ℕ) :
    truncatedGapCost q H n ≤ H ^ 3 := by
  classical
  unfold truncatedGapCost
  calc
    (∑ d ∈ Finset.Ico 1 H, if gapPattern q d n then d ^ 2 else 0) ≤
        ∑ d ∈ Finset.Ico 1 H, H ^ 2 := by
      apply Finset.sum_le_sum
      intro d hd
      split_ifs
      · exact Nat.pow_le_pow_left (Finset.mem_Ico.mp hd).2.le 2
      · exact Nat.zero_le _
    _ = (Finset.Ico 1 H).card * H ^ 2 := by simp
    _ ≤ H * H ^ 2 := by
      apply Nat.mul_le_mul_right
      simp
    _ = H ^ 3 := by ring

/-- Predicate members below `x` are exactly the image of enumeration indices
below the strict count at `x`. -/
theorem image_nth_range_count
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n}) (x : ℕ) :
    (Finset.range (Nat.count q x)).image (Nat.nth q) =
      (Finset.range x).filter q := by
  ext n
  constructor
  · intro hn
    rcases Finset.mem_image.mp hn with ⟨i, hi, rfl⟩
    apply Finset.mem_filter.mpr
    exact ⟨Finset.mem_range.mpr
      (Nat.nth_lt_of_lt_count (Finset.mem_range.mp hi)),
      Nat.nth_mem_of_infinite hq i⟩
  · intro hn
    have hnr := Finset.mem_range.mp (Finset.mem_filter.mp hn).1
    have hnq := (Finset.mem_filter.mp hn).2
    apply Finset.mem_image.mpr
    refine ⟨Nat.count q n, Finset.mem_range.mpr ?_, Nat.nth_count hnq⟩
    exact Nat.count_strict_mono hnq hnr

/-- Summing local truncated costs over integer starts equals summing squared
short gaps over enumeration indices. -/
theorem sum_truncatedGapCost_eq_gap_sum
    (q : ℕ → Prop) [DecidablePred q] (hq : Set.Infinite {n | q n})
    (H x : ℕ) :
    ∑ n ∈ Finset.range x, truncatedGapCost q H n =
      ∑ i ∈ (Finset.range (Nat.count q x)).filter
        (fun i => Nat.nth q (i + 1) - Nat.nth q i < H),
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 := by
  classical
  let S := Finset.range (Nat.count q x)
  let B := (Finset.range x).filter q
  have hfilter : (∑ n ∈ B, truncatedGapCost q H n) =
      ∑ n ∈ Finset.range x, truncatedGapCost q H n := by
    apply Finset.sum_subset (Finset.filter_subset _ _)
    intro n hnx hnB
    apply truncatedGapCost_eq_zero_of_not q H n
    intro hnq
    exact hnB (Finset.mem_filter.mpr ⟨hnx, hnq⟩)
  have himage : S.image (Nat.nth q) = B := by
    simpa [S, B] using image_nth_range_count q hq x
  rw [← hfilter, ← himage, Finset.sum_image]
  · rw [Finset.sum_filter]
    change (∑ i ∈ S, truncatedGapCost q H (Nat.nth q i)) =
      ∑ i ∈ S, if Nat.nth q (i + 1) - Nat.nth q i < H then
        (Nat.nth q (i + 1) - Nat.nth q i) ^ 2 else 0
    apply Finset.sum_congr rfl
    intro i hi
    rw [truncatedGapCost_nth q hq]
  · exact (Nat.nth_injective hq).injOn

end Erdos489
