/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperDiscreteTCover

/-!
# Erdős Problem 446: the sharp pointwise dyadic-tail deficit

The general dyadic prefix estimate in `UpperPrefixTailBounds` gives a power
of two at the least scale reaching a prescribed prefix.  Strictly before the
cutoff `A - 2^s - 1`, that least power is at most twice the remaining gap.
This is the pointwise estimate needed when summing the no-witness part of
Ford's discrete exceptional cover.
-/

namespace Erdos446

/-- If the gap `x` is strictly larger than the cutoff power `2^s`, then the
least dyadic scale which is both at least `s` and reaches `x` is less than
`2x`. -/
theorem two_pow_max_clog_le_twice_of_pow_lt
    {s x : ℕ} (hsx : 2 ^ s < x) :
    2 ^ max s (Nat.clog 2 x) ≤ 2 * x := by
  have hsclog : s < Nat.clog 2 x :=
    (Nat.lt_clog_iff_pow_lt (by omega : 1 < 2)).2 hsx
  have hclogpos : 0 < Nat.clog 2 x :=
    (Nat.zero_le s).trans_lt hsclog
  have hx : 1 < x := by
    have hpowpos : 0 < 2 ^ s := by positivity
    omega
  have hpred : 2 ^ (Nat.clog 2 x).pred < x :=
    Nat.pow_pred_clog_lt_self (by omega : 1 < 2) hx
  rw [max_eq_right hsclog.le]
  have hclogEq : (Nat.clog 2 x).pred.succ = Nat.clog 2 x :=
    Nat.succ_pred_eq_of_pos hclogpos
  apply Nat.le_of_lt
  calc
    2 ^ Nat.clog 2 x = 2 ^ (Nat.clog 2 x).pred.succ :=
      congrArg (fun n : ℕ ↦ 2 ^ n) hclogEq.symm
    _ = 2 ^ (Nat.clog 2 x).pred * 2 := Nat.pow_succ _ _
    _ < x * 2 := (Nat.mul_lt_mul_right (by omega : 0 < 2)).2 hpred
    _ = 2 * x := Nat.mul_comm _ _

/-- Pointwise form of the dyadic no-crowding argument, isolated here to
keep the sharp deficit lemma independent of the subsequent summation
bounds. -/
private theorem blockPrefixTail_le_pow_max_clog_sharp
    {v : ℕ} (c : Fin v → ℕ) {l A s u : ℕ}
    (huA : u ≤ A)
    (hNoCrowding : ∀ m : ℕ, s ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m)) :
    l - blockPrefixCount c u ≤
      2 ^ max s (Nat.clog 2 (A - u)) := by
  let m := max s (Nat.clog 2 (A - u))
  have hxpow : A - u ≤ 2 ^ m := by
    exact (Nat.le_pow_clog (by omega : 1 < 2) (A - u)).trans
      (Nat.pow_le_pow_right (by omega : 0 < 2) (le_max_right _ _))
  have hindex : A - 2 ^ m ≤ u := by
    omega
  have hprefix : blockPrefixCount c (A - 2 ^ m) ≤
      blockPrefixCount c u :=
    blockPrefixCount_monotone c hindex
  by_cases hml : 2 ^ m < l
  · have hlow : l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m) :=
      hNoCrowding m (le_max_left _ _) hml
    have hlow' := hlow.trans hprefix
    have htail : l - blockPrefixCount c u ≤ 2 ^ m := by omega
    simpa [m] using htail
  · have hlm : l ≤ 2 ^ m := Nat.le_of_not_gt hml
    have htail : l - blockPrefixCount c u ≤ 2 ^ m :=
      (Nat.sub_le l _).trans hlm
    simpa [m] using htail

/-- Sharp pointwise form of the no-dyadic-crowding estimate.  Compared with
`blockPrefixTail_le_pow_add_twice_gap`, the strict cutoff hypothesis removes
the extra additive `2^s` term. -/
theorem blockPrefixTail_le_twice_gap_of_pow_lt
    {v : ℕ} (c : Fin v → ℕ) {l A s u : ℕ}
    (huA : u ≤ A) (hpowGap : 2 ^ s < A - u)
    (hNoCrowding : ∀ m : ℕ, s ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m)) :
    l - blockPrefixCount c u ≤ 2 * (A - u) := by
  exact (blockPrefixTail_le_pow_max_clog_sharp c huA hNoCrowding).trans
    (two_pow_max_clog_le_twice_of_pow_lt hpowGap)

/-- The exact pointwise tail-deficit lemma used under the failure of Ford's
dyadic witness.  Here

* `A = l - γ = q + H - 1` is the unshifted affine rank,
* `d = 2^(H-3)` is the first permitted dyadic scale, and
* `T = A-d-1` is the last summation cutoff.

The affine identity and the harmless numerical condition `6 ≤ H` are kept
in the statement because this is the form used by the surrounding cover;
the pointwise `Nat.clog` argument only needs the displayed equalities and the
strict inequality `t < T`.
-/
theorem fordTailDeficit_le_twice_gap_of_no_witness
    {v : ℕ} (c : Fin v → ℕ)
    {l γ q H A d T t : ℕ}
    (_hH : 6 ≤ H)
    (hA : A = l - γ) (hAq : A = q + H - 1)
    (hd : d = 2 ^ (H - 3)) (hdA : d < A)
    (hT : T = A - d - 1)
    (hNoWitness : ∀ m : ℕ, H - 3 ≤ m → 2 ^ m < l →
      ¬ blockPrefixCount c (l - γ - 2 ^ m) < l - 2 ^ m)
    (ht : t < T) :
    l - blockPrefixCount c (t + 1) ≤ 2 * (A - 1 - t) := by
  have huA : t + 1 ≤ A := by
    omega
  have hpowGap : 2 ^ (H - 3) < A - (t + 1) := by
    omega
  have hNoCrowding : ∀ m : ℕ, H - 3 ≤ m → 2 ^ m < l →
      l - 2 ^ m ≤ blockPrefixCount c (A - 2 ^ m) := by
    intro m hm hml
    have hn := hNoWitness m hm hml
    rw [hA]
    omega
  have htail := blockPrefixTail_le_twice_gap_of_pow_lt c huA hpowGap hNoCrowding
  convert htail using 1
  omega

end Erdos446
