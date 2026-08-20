/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperFiniteLayers

/-!
# Erdős Problem 446: Ford's discrete exceptional cover

This file isolates the completely finite version of the set
`T(k,v,γ)` used in Ford's proof.  If `c : Fin v → ℕ` is a block
occupancy, the first `q` cells contain `blockPrefixCount c q` objects and
have exponential weight `blockPrefixWeight c q`.  Thus the defining
inequality for the ordered-simplex set `T(k,v,γ)` becomes

`2 ^ blockPrefixCount c q ≤ 2 ^ γ * (blockPrefixWeight c q + 1)`.

The added `1` is the discrete endpoint term.  It is also exactly the term
which occurs in the integral prefix envelope, so every integral dyadic
layer lies in this finite `T`-set without approximation.

We also record the two alternatives in Ford's cover.  The first is the
single affine Smirnov barrier (32i).  In the published second alternative
the rank gap is `2^m`, while the cell-coordinate displacement is the
*linear* quantity `2m`: the assertion

`blockPrefixCount c (l - γ - 2*m) < l - 2^m`

says precisely that the `(l-2^m)`-th occupied cell is at least
`l-γ-2m`; this is Ford's displayed crowding condition, with the harmless
half-open-cell convention.
-/

namespace Erdos446

open Finset
open scoped BigOperators

/-- The finite weighted-prefix version of Ford's set `T(k,v,γ)`. -/
def SatisfiesFordWeightedBarrier {v : ℕ} (γ : ℕ) (c : Fin v → ℕ) : Prop :=
  ∀ q ∈ Finset.range (v + 1),
    2 ^ blockPrefixCount c q ≤ 2 ^ γ * (blockPrefixWeight c q + 1)

/-- Occupancies of total mass `k` in the finite `T(k,v,γ)`-set. -/
noncomputable def fordWeightedOccupancies (k v γ : ℕ) : Finset (Fin v → ℕ) :=
  by
    classical
    exact (compositionsOf v k).filter fun c ↦
      ∀ q ∈ Finset.range (v + 1),
        2 ^ blockPrefixCount c q ≤ 2 ^ γ * (blockPrefixWeight c q + 1)

theorem mem_fordWeightedOccupancies {k v γ : ℕ} {c : Fin v → ℕ} :
    c ∈ fordWeightedOccupancies k v γ ↔
      (∑ i, c i = k) ∧ SatisfiesFordWeightedBarrier γ c := by
  simp [fordWeightedOccupancies, SatisfiesFordWeightedBarrier,
    mem_compositionsOf]

/-- The affine alternative (32i), in occupancy-prefix form. -/
def SatisfiesFordAffineBarrier {v : ℕ}
    (γ r : ℕ) (c : Fin v → ℕ) : Prop :=
  ∀ q : ℕ, q ≤ v → blockPrefixCount c q < γ + r + q

/-- Ford's cover radius: an absolute depth five, enlarged by the terminal
deficit when necessary. -/
def fordDiscreteCoverRadius (k v γ : ℕ) : ℕ :=
  max 5 (k - v - γ)

theorem five_le_fordDiscreteCoverRadius (k v γ : ℕ) :
    5 ≤ fordDiscreteCoverRadius k v γ :=
  le_max_left _ _

/-- Ford's published discrete crowding condition.  The first inequality
makes the indicated rank positive; the second says that fewer than `l-2^m`
objects occur before cell `l-γ-2m`. -/
def FordDyadicCrowdingEvent {v : ℕ}
    (γ m l : ℕ) (c : Fin v → ℕ) : Prop :=
  2 ^ m < l ∧
    blockPrefixCount c (l - γ - 2 * m) < l - 2 ^ m

/-- Auxiliary power-displacement event.  This is useful for a separate
coarse dyadic lemma, but is not Ford's published crowding cutoff. -/
def FordPowerCutoffCrowdingEvent {v : ℕ}
    (γ m l : ℕ) (c : Fin v → ℕ) : Prop :=
  2 ^ m < l ∧
    blockPrefixCount c (l - γ - 2 ^ m) < l - 2 ^ m

/-- Full exceptional witness attached to the prefix where the affine
barrier first fails.  Here `h` is the integral depth of the last occupied
cell below its affine position. -/
def FordExceptionalWitness {v : ℕ}
    (γ r : ℕ) (c : Fin v → ℕ) (q h m l : ℕ) : Prop :=
  q ≤ v ∧
    l = blockPrefixCount c q ∧
    h = l - γ - q + 1 ∧
    r + 1 ≤ h ∧
    h - 3 ≤ m ∧
    FordDyadicCrowdingEvent γ m l c

theorem fordWeightedOccupancies_mono_gamma (k v : ℕ) :
    Monotone fun γ ↦ fordWeightedOccupancies k v γ := by
  intro γ γ' hγ c hc
  rw [mem_fordWeightedOccupancies] at hc ⊢
  refine ⟨hc.1, ?_⟩
  intro q hq
  exact (hc.2 q hq).trans <|
    Nat.mul_le_mul_right _ (Nat.pow_le_pow_right (by omega) hγ)

/-- The lower edge of an integral dyadic layer gives all weighted-prefix
inequalities defining the finite `T(k,v,m)`-set. -/
theorem blockIntegerDyadicLayer_subset_fordWeightedOccupancies
    (k v m : ℕ) :
    blockIntegerDyadicLayer k v m ⊆
      fordWeightedOccupancies k v m := by
  intro c hc
  have hcData := mem_blockIntegerDyadicLayer.mp hc
  rw [mem_fordWeightedOccupancies]
  refine ⟨hcData.1, ?_⟩
  intro q hq
  have hqv : q ≤ v := by
    have := Finset.mem_range.mp hq
    omega
  let C := blockPrefixCount c q
  let W := blockPrefixWeight c q
  have hCk : C ≤ k := blockPrefixCount_le_total c hcData.1 hqv
  have hlow : 2 ^ (k - m) ≤ blockIntegerPrefixEnvelope k c q :=
    hcData.2.1.trans (blockIntegerEnvelope_le_prefix k c hqv)
  by_cases hmk : m ≤ k
  · have hsplit : k = (k - m) + m := (Nat.sub_add_cancel hmk).symm
    have hkc : k = (k - C) + C := (Nat.sub_add_cancel hCk).symm
    dsimp [blockIntegerPrefixEnvelope] at hlow
    have hmul := Nat.mul_le_mul_right (2 ^ m) hlow
    have hlhs : 2 ^ (k - m) * 2 ^ m = 2 ^ k := by
      rw [← pow_add, ← hsplit]
    rw [hlhs] at hmul
    have hkcpow : 2 ^ k = 2 ^ (k - C) * 2 ^ C := by
      rw [← pow_add, ← hkc]
    rw [hkcpow] at hmul
    have hscaled : 2 ^ (k - C) * 2 ^ C ≤
        2 ^ (k - C) * (2 ^ m * (W + 1)) := by
      calc
        2 ^ (k - C) * 2 ^ C ≤
            (2 ^ (k - C) * (W + 1)) * 2 ^ m := hmul
        _ = 2 ^ (k - C) * (2 ^ m * (W + 1)) := by ring
    exact Nat.le_of_mul_le_mul_left hscaled (by positivity)
  · have hkm : k < m := lt_of_not_ge hmk
    have htrivial : 2 ^ C ≤ 2 ^ m :=
      Nat.pow_le_pow_right (by omega) (hCk.trans hkm.le)
    exact htrivial.trans <| by
      calc
        2 ^ m = 2 ^ m * 1 := by ring
        _ ≤ 2 ^ m * (W + 1) := Nat.mul_le_mul_left _ (by omega)

/-- The real sharp dyadic layer satisfies the same exact weighted barrier. -/
theorem sharpBlockDyadicLayer_subset_fordWeightedOccupancies
    (M k v m : ℕ) :
    sharpBlockDyadicLayer M k v m ⊆
      fordWeightedOccupancies k v m := by
  intro c hc
  rw [mem_fordWeightedOccupancies]
  refine ⟨(mem_sharpBlockDyadicLayer.mp hc).1, ?_⟩
  intro q hq
  exact sharpBlockDyadicLayer_powerBarrier hc (by
    have := Finset.mem_range.mp hq
    omega)

/-! ## Prefix summation by parts -/

theorem blockPrefixCount_monotone {v : ℕ} (c : Fin v → ℕ) :
    Monotone (blockPrefixCount c) := by
  intro a b hab
  rw [blockPrefixCount, blockPrefixCount]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hab
  · intro i hi _
    exact Nat.zero_le _

theorem blockPrefixWeight_monotone {v : ℕ} (c : Fin v → ℕ) :
    Monotone (blockPrefixWeight c) := by
  intro a b hab
  rw [blockPrefixWeight, blockPrefixWeight]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · exact Finset.range_mono hab
  · intro i hi _
    exact Nat.zero_le _

private theorem sum_two_pow_range (q : ℕ) :
    (∑ t ∈ Finset.range q, 2 ^ t) = 2 ^ q - 1 := by
  induction q with
  | zero => simp
  | succ q ih =>
      rw [Finset.sum_range_succ, ih, pow_succ]
      have hpos : 0 < 2 ^ q := by positivity
      omega

/-- Discrete summation by parts for an occupancy.  The coefficient
`C(q)-C(t+1)` is the number of occupied cells in `[t+1,q)`. -/
theorem blockPrefixWeight_eq_count_add_tailSum
    {v : ℕ} (c : Fin v → ℕ) (q : ℕ) :
    blockPrefixWeight c q =
      blockPrefixCount c q +
        ∑ t ∈ Finset.range q,
          (blockPrefixCount c q - blockPrefixCount c (t + 1)) * 2 ^ t := by
  induction q with
  | zero => simp [blockPrefixWeight, blockPrefixCount]
  | succ q ih =>
      let C := blockPrefixCount c q
      let d := extendComposition c q
      have hcount : blockPrefixCount c (q + 1) = C + d := by
        simp [blockPrefixCount, C, d, Finset.sum_range_succ]
      have hweight : blockPrefixWeight c (q + 1) =
          blockPrefixWeight c q + d * 2 ^ q := by
        simp [blockPrefixWeight, d, Finset.sum_range_succ]
      have hprefix (t : ℕ) (ht : t ∈ Finset.range q) :
          blockPrefixCount c (t + 1) ≤ C := by
        exact blockPrefixCount_monotone c (by
          have := Finset.mem_range.mp ht
          omega)
      have hsub (t : ℕ) (ht : t ∈ Finset.range q) :
          C + d - blockPrefixCount c (t + 1) =
            (C - blockPrefixCount c (t + 1)) + d := by
        have := hprefix t ht
        omega
      have hsum :
          (∑ t ∈ Finset.range q,
              (C + d - blockPrefixCount c (t + 1)) * 2 ^ t) =
            (∑ t ∈ Finset.range q,
              (C - blockPrefixCount c (t + 1)) * 2 ^ t) +
              d * (2 ^ q - 1) := by
        calc
          (∑ t ∈ Finset.range q,
              (C + d - blockPrefixCount c (t + 1)) * 2 ^ t) =
              ∑ t ∈ Finset.range q,
                ((C - blockPrefixCount c (t + 1)) * 2 ^ t +
                  d * 2 ^ t) := by
            apply Finset.sum_congr rfl
            intro t ht
            rw [hsub t ht]
            ring
          _ = (∑ t ∈ Finset.range q,
                (C - blockPrefixCount c (t + 1)) * 2 ^ t) +
                d * (∑ t ∈ Finset.range q, 2 ^ t) := by
            rw [Finset.sum_add_distrib, Finset.mul_sum]
          _ = _ := by rw [sum_two_pow_range]
      have hlast : C + d - blockPrefixCount c (q + 1) = 0 := by
        rw [hcount]
        simp
      rw [hweight, ih, hcount, Finset.sum_range_succ, hsum]
      rw [hlast]
      simp only [zero_mul, add_zero]
      have hpowpos : 0 < 2 ^ q := by positivity
      have hpowdecomp : 1 + (2 ^ q - 1) = 2 ^ q := by omega
      have hd : d + d * (2 ^ q - 1) = d * 2 ^ q := by
        calc
          d + d * (2 ^ q - 1) = d * (1 + (2 ^ q - 1)) := by ring
          _ = d * 2 ^ q := by rw [hpowdecomp]
      dsimp only [C]
      calc
        blockPrefixCount c q +
              (∑ t ∈ Finset.range q,
                (blockPrefixCount c q - blockPrefixCount c (t + 1)) *
                  2 ^ t) + d * 2 ^ q =
            blockPrefixCount c q + d +
              (∑ t ∈ Finset.range q,
                (blockPrefixCount c q - blockPrefixCount c (t + 1)) *
                  2 ^ t) + d * (2 ^ q - 1) := by
          rw [← hd]
          ac_rfl
        _ = blockPrefixCount c q + d +
              ((∑ t ∈ Finset.range q,
                (blockPrefixCount c q - blockPrefixCount c (t + 1)) *
                  2 ^ t) + d * (2 ^ q - 1)) := by ac_rfl

/-- Coarse endpoint bound, with the sharp exponent `q-1` for a nonempty
prefix. -/
theorem blockPrefixWeight_le_count_mul_prevPow
    {v : ℕ} (c : Fin v → ℕ) {q : ℕ} (hq : 0 < q) :
    blockPrefixWeight c q ≤
      blockPrefixCount c q * 2 ^ (q - 1) := by
  rw [blockPrefixWeight, blockPrefixCount]
  calc
    (∑ i ∈ Finset.range q, extendComposition c i * 2 ^ i) ≤
        ∑ i ∈ Finset.range q,
          extendComposition c i * 2 ^ (q - 1) := by
      apply Finset.sum_le_sum
      intro i hi
      apply Nat.mul_le_mul_left
      apply Nat.pow_le_pow_right (by omega)
      have := Finset.mem_range.mp hi
      omega
    _ = (∑ i ∈ Finset.range q, extendComposition c i) *
          2 ^ (q - 1) := by rw [Finset.sum_mul]

/-- A finite weighted geometric identity used to bound the far part of the
dyadic cover. -/
theorem weightedTwoPowRange_le
    {A T : ℕ} (hTA : T ≤ A) :
    (∑ t ∈ Finset.range T, (A - t) * 2 ^ t) ≤
      (A - T + 2) * 2 ^ T := by
  induction T with
  | zero => simp
  | succ T ih =>
      have hT : T ≤ A := T.le_succ.trans hTA
      rw [Finset.sum_range_succ]
      calc
        (∑ t ∈ Finset.range T, (A - t) * 2 ^ t) +
            (A - T) * 2 ^ T ≤
            (A - T + 2) * 2 ^ T + (A - T) * 2 ^ T :=
          Nat.add_le_add_right (ih hT) _
        _ = (A - (T + 1) + 2) * 2 ^ (T + 1) := by
          rw [pow_succ]
          have hsub : A - T = A - (T + 1) + 1 := by omega
          rw [hsub]
          ring

end Erdos446
