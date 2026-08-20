/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.RaneyRotation
import Mathlib.Algebra.BigOperators.Fin

/-!
# Erdős Problem 446: Raney's lemma for occupancy vectors

This file translates the list-valued cycle lemma into the finite occupancy
model.  For an occupancy vector `c`, the increments `1 - cᵢ` have total
rise equal to the terminal slack.  A positive cyclic prefix is exactly a
strict zero-offset Smirnov barrier for the corresponding cyclic rotation.
-/

namespace Erdos446

open Finset
open scoped BigOperators

theorem intPrefixSum_rotate_eq_cyclicIntPrefixSum
    {x : List ℤ} {r t : ℕ} (hr : r ≤ x.length) (ht : t ≤ x.length) :
    intPrefixSum (x.rotate r) t = cyclicIntPrefixSum x r t := by
  have hrotate := List.rotate_eq_drop_append_take (l := x) hr
  by_cases hnowrap : r + t ≤ x.length
  · have htDrop : t ≤ (x.drop r).length := by
      simp only [List.length_drop]
      omega
    have hprefix : intPrefixSum x (r + t) =
        intPrefixSum x r + ((x.drop r).take t).sum := by
      rw [intPrefixSum, intPrefixSum, List.take_add, List.sum_append]
    rw [cyclicIntPrefixSum, if_pos hnowrap, hrotate, intPrefixSum,
      List.take_append_of_le_length htDrop, hprefix]
    omega
  · have hrLen : r ≤ x.length := hr
    have hdropLen : (x.drop r).length = x.length - r := by simp
    have hdropLt : (x.drop r).length < t := by
      rw [hdropLen]
      omega
    have htakeDrop : (x.drop r).take t = x.drop r :=
      List.take_of_length_le hdropLt.le
    have htailIndex : t - (x.drop r).length = r + t - x.length := by
      rw [hdropLen]
      omega
    have htailLe : r + t - x.length ≤ r := by omega
    have htakeTake : (x.take r).take (r + t - x.length) =
        x.take (r + t - x.length) := by
      rw [List.take_take, min_eq_left htailLe]
    have hsplit : (x.take r).sum + (x.drop r).sum = x.sum :=
      List.sum_take_add_sum_drop x r
    have hrPrefix : intPrefixSum x r = (x.take r).sum := rfl
    have htailPrefix : intPrefixSum x (r + t - x.length) =
        (x.take (r + t - x.length)).sum := rfl
    rw [cyclicIntPrefixSum, if_neg hnowrap, hrotate, intPrefixSum,
      List.take_append, htakeDrop, htailIndex, htakeTake, List.sum_append]
    rw [hrPrefix, htailPrefix]
    omega

/-- Integer walk associated with a natural occupancy vector. -/
def occupancyStep (a : ℕ) : ℤ := 1 - (a : ℤ)

/-- The list of occupancy increments `1 - cᵢ`. -/
def occupancyWalk {v : ℕ} (c : Fin v → ℕ) : List ℤ :=
  (List.ofFn c).map occupancyStep

@[simp] theorem length_occupancyWalk {v : ℕ} (c : Fin v → ℕ) :
    (occupancyWalk c).length = v := by
  rw [occupancyWalk, List.length_map, List.length_ofFn]

theorem occupancyWalk_entry_le_one {v : ℕ} (c : Fin v → ℕ) :
    ∀ a ∈ occupancyWalk c, a ≤ 1 := by
  intro a ha
  rw [occupancyWalk, List.mem_map] at ha
  obtain ⟨b, _hb, rfl⟩ := ha
  exact sub_le_self 1 (Int.natCast_nonneg b)

theorem sum_map_occupancyStep (l : List ℕ) :
    (l.map occupancyStep).sum =
      (l.length : ℤ) - (l.sum : ℤ) := by
  induction l with
  | nil => simp
  | cons a l ih =>
      simp [occupancyStep, ih]
      ring

theorem sum_occupancyWalk {v : ℕ} (c : Fin v → ℕ) :
    (occupancyWalk c).sum = (v : ℤ) - ((∑ i, c i : ℕ) : ℤ) := by
  rw [occupancyWalk, sum_map_occupancyStep, List.length_ofFn, List.sum_ofFn]

theorem occupancyPrefix_eq_sum_take_ofFn {v : ℕ}
    (c : Fin v → ℕ) (h : ℕ) :
    occupancyPrefix c h = ((List.ofFn c).take h).sum := by
  rw [occupancyPrefix, List.sum_take_ofFn]

theorem intPrefixSum_occupancyWalk {v : ℕ} (c : Fin v → ℕ)
    {h : ℕ} (hh : h ≤ v) :
    intPrefixSum (occupancyWalk c) h =
      (h : ℤ) - (occupancyPrefix c h : ℤ) := by
  rw [intPrefixSum, occupancyWalk, ← List.map_take, sum_map_occupancyStep,
    List.length_take, List.length_ofFn, min_eq_left hh,
    ← occupancyPrefix_eq_sum_take_ofFn]

theorem occupancyWalk_rotateComposition {v : ℕ} (r : Fin v)
    (c : Fin v → ℕ) :
    occupancyWalk (rotateComposition r c) = (occupancyWalk c).rotate r.val := by
  rw [occupancyWalk, occupancyWalk, ofFn_rotateComposition,
    List.map_rotate]

/-! ## Good cyclic rotations of an occupancy vector -/

/-- The strict zero-offset barriers, without a condition on the total mass. -/
def SatisfiesZeroBarrier {v : ℕ} (c : Fin v → ℕ) : Prop :=
  ∀ h : ℕ, 1 ≤ h → h ≤ v → occupancyPrefix c h < h

/-- Cyclic rotations satisfying all strict zero-offset barriers. -/
noncomputable def zeroBarrierGoodRotations {v : ℕ} (c : Fin v → ℕ) :
    Finset (Fin v) := by
  classical
  exact Finset.univ.filter fun r ↦
    SatisfiesZeroBarrier (rotateComposition r c)

theorem mem_zeroBarrierGoodRotations {v : ℕ} {c : Fin v → ℕ}
    {r : Fin v} :
    r ∈ zeroBarrierGoodRotations c ↔
      SatisfiesZeroBarrier (rotateComposition r c) := by
  simp [zeroBarrierGoodRotations]

theorem isRaneyGoodStart_occupancyWalk_iff
    {v : ℕ} (c : Fin v → ℕ) (r : Fin v) :
    IsRaneyGoodStart (occupancyWalk c) r.val ↔
      SatisfiesZeroBarrier (rotateComposition r c) := by
  constructor
  · intro hgood h hh hhv
    have hhvWalk : h ≤ (occupancyWalk c).length := by simpa using hhv
    have hrWalk : r.val ≤ (occupancyWalk c).length := by
      simpa using r.isLt.le
    have hpos := hgood.2 h hh hhvWalk
    rw [← intPrefixSum_rotate_eq_cyclicIntPrefixSum hrWalk hhvWalk,
      ← occupancyWalk_rotateComposition,
      intPrefixSum_occupancyWalk _ hhv] at hpos
    exact_mod_cast (show (occupancyPrefix (rotateComposition r c) h : ℤ) <
      (h : ℤ) by omega)
  · intro hbarrier
    refine ⟨by simpa using r.isLt, ?_⟩
    intro h hh hhv
    have hhvNat : h ≤ v := by simpa using hhv
    have hrWalk : r.val ≤ (occupancyWalk c).length := by
      simpa using r.isLt.le
    have hlt := hbarrier h hh hhvNat
    rw [← intPrefixSum_rotate_eq_cyclicIntPrefixSum hrWalk hhv,
      ← occupancyWalk_rotateComposition,
      intPrefixSum_occupancyWalk _ hhvNat]
    have hltZ : (occupancyPrefix (rotateComposition r c) h : ℤ) <
        (h : ℤ) := by exact_mod_cast hlt
    omega

/-- Occupancy form of Raney's cycle lemma. -/
theorem card_zeroBarrierGoodRotations
    {k v w : ℕ} (hw : 0 < w) (hrel : w + k = v)
    {c : Fin v → ℕ} (hc : ∑ i, c i = k) :
    (zeroBarrierGoodRotations c).card = w := by
  have hv : 0 < v := by omega
  have hx : occupancyWalk c ≠ [] := by
    exact List.ne_nil_of_length_pos (by simpa using hv)
  have hsum : (occupancyWalk c).sum = (w : ℤ) := by
    rw [sum_occupancyWalk, hc]
    have hrelZ : (w : ℤ) + (k : ℤ) = (v : ℤ) := by
      exact_mod_cast hrel
    omega
  have hcard := card_raneyGoodStarts hx
    (occupancyWalk_entry_le_one c) hsum hw
  have himage :
      (zeroBarrierGoodRotations c).image Fin.val =
        raneyGoodStarts (occupancyWalk c) := by
    ext s
    constructor
    · intro hs
      obtain ⟨r, hr, rfl⟩ := Finset.mem_image.mp hs
      rw [mem_raneyGoodStarts,
        isRaneyGoodStart_occupancyWalk_iff]
      exact mem_zeroBarrierGoodRotations.mp hr
    · intro hs
      have hgood := mem_raneyGoodStarts.mp hs
      have hslt : s < v := by simpa using hgood.1
      let r : Fin v := ⟨s, hslt⟩
      apply Finset.mem_image.mpr
      refine ⟨r, ?_, rfl⟩
      rw [mem_zeroBarrierGoodRotations,
        ← isRaneyGoodStart_occupancyWalk_iff]
      exact hgood
  rw [← hcard, ← himage,
    Finset.card_image_of_injective _ Fin.val_injective]

theorem mem_smirnovOccupancies_zero_iff
    {k v : ℕ} {c : Fin v → ℕ} :
    c ∈ smirnovOccupancies k 0 v ↔
      c ∈ compositionsOf v k ∧ SatisfiesZeroBarrier c := by
  simp [mem_smirnovOccupancies, mem_compositionsOf,
    SatisfiesZeroBarrier]

/-! ## Reciprocal-factorial double count -/

/-- Weighted form of Raney's lemma.  The left side counts a zero-barrier
occupancy once for every possible choice of cyclic origin; the right side
counts the `w` good origins of every unrestricted occupancy. -/
theorem length_mul_smirnovOccupancyMass_zero
    {k v w : ℕ} (hw : 0 < w) (hrel : w + k = v) :
    (v : ℝ) * smirnovOccupancyMass k 0 v =
      (w : ℝ) * ((v : ℝ) ^ k / (k.factorial : ℝ)) := by
  classical
  let W : (Fin v → ℕ) → ℝ := fun c ↦ 1 / compositionFactorial c
  have hmass : smirnovOccupancyMass k 0 v =
      ∑ c ∈ compositionsOf v k,
        if SatisfiesZeroBarrier c then W c else 0 := by
    rw [smirnovOccupancyMass, smirnovOccupancies, Finset.sum_filter]
    simp only [SatisfiesZeroBarrier, Nat.zero_add, W]
    apply Finset.sum_congr rfl
    intro c _hc
    split_ifs with h <;> simp_all
  calc
    (v : ℝ) * smirnovOccupancyMass k 0 v =
        ∑ r : Fin v, ∑ c ∈ compositionsOf v k,
          if SatisfiesZeroBarrier c then W c else 0 := by
      rw [hmass]
      simp
    _ = ∑ r : Fin v, ∑ c ∈ compositionsOf v k,
          if SatisfiesZeroBarrier (rotateComposition r c) then W c else 0 := by
      apply Finset.sum_congr rfl
      intro r _hr
      have hperm := Finset.sum_equiv (rotateComposition r)
        (s := compositionsOf v k) (t := compositionsOf v k)
        (f := fun c ↦
          if SatisfiesZeroBarrier (rotateComposition r c) then
            W (rotateComposition r c) else 0)
        (g := fun c ↦ if SatisfiesZeroBarrier c then W c else 0)
        (fun c ↦ by simp only [mem_compositionsOf, sum_rotateComposition])
        (fun _c _hc ↦ rfl)
      simpa only [W, compositionFactorial_rotate] using hperm.symm
    _ = ∑ c ∈ compositionsOf v k, ∑ r : Fin v,
          if SatisfiesZeroBarrier (rotateComposition r c) then W c else 0 := by
      rw [Finset.sum_comm]
    _ = ∑ c ∈ compositionsOf v k,
          ∑ r ∈ zeroBarrierGoodRotations c, W c := by
      apply Finset.sum_congr rfl
      intro c _hc
      rw [zeroBarrierGoodRotations, Finset.sum_filter]
    _ = ∑ c ∈ compositionsOf v k, (w : ℝ) * W c := by
      apply Finset.sum_congr rfl
      intro c hc
      have hcard := card_zeroBarrierGoodRotations hw hrel
        (mem_compositionsOf.mp hc)
      rw [Finset.sum_const, hcard]
      simp
    _ = (w : ℝ) *
          (∑ c ∈ compositionsOf v k, 1 / compositionFactorial c) := by
      simp only [W, Finset.mul_sum]
    _ = (w : ℝ) * ((v : ℝ) ^ k / (k.factorial : ℝ)) := by
      rw [sum_inv_compositionFactorial_compositionsOf]

theorem add_mul_abelKernel_eq_pow {w : ℕ} (hw : 0 < w) (k : ℕ) :
    ((w + k : ℕ) : ℝ) * abelKernel (w : ℝ) k =
      ((w + k : ℕ) : ℝ) ^ k := by
  cases k with
  | zero =>
      simp [abelKernel, ne_of_gt hw]
  | succ k =>
      rw [abelKernel_eq_pow (Nat.succ_ne_zero k)]
      simp only [Nat.cast_add, Nat.cast_one, Nat.succ_sub_one,
        Nat.cast_succ]
      rw [pow_succ]
      ring_nf

/-- Exact zero-offset Smirnov mass.  The inverse convention in
`abelKernel` makes the formula valid at `k = 0` as well. -/
theorem smirnovOccupancyMass_zero_eq_abelKernel
    {w : ℕ} (hw : 0 < w) (k : ℕ) :
    smirnovOccupancyMass k 0 (w + k) =
      (w : ℝ) * abelKernel (w : ℝ) k / (k.factorial : ℝ) := by
  have hdouble := length_mul_smirnovOccupancyMass_zero
    (k := k) (v := w + k) (w := w) hw rfl
  have hV : (0 : ℝ) < (w + k : ℕ) := by positivity
  have hfac : (0 : ℝ) < k.factorial := by positivity
  have hkernel := add_mul_abelKernel_eq_pow hw k
  apply mul_left_cancel₀ hV.ne'
  rw [hdouble]
  field_simp [hfac.ne']
  nlinarith

end Erdos446
