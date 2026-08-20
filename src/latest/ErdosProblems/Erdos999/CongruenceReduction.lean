/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/

import ErdosProblems.Erdos999.PairGeometry
import ErdosProblems.Erdos999.CRTCount

/-!
# Reduction of nearby rational pairs to congruence fibres

Writing two positive denominators as `q = g * a` and `r = g * b`, where
`g = gcd q r`, scales their rational-centre difference by the common ambient
modulus `g * a * b = lcm q r`.  After subtracting the corresponding integral
multiple of that modulus, every nearby pair therefore belongs to a congruence
fibre with a small signed fibre parameter.
-/

open scoped BigOperators

namespace Erdos999

/-- The finite set of integers of absolute value at most `C`. -/
noncomputable def signedIntegerRange (C : ℕ) : Finset ℤ :=
  Finset.Icc (-(C : ℤ)) (C : ℤ)

@[simp] theorem mem_signedIntegerRange_iff {C : ℕ} {c : ℤ} :
    c ∈ signedIntegerRange C ↔ c.natAbs ≤ C := by
  rw [signedIntegerRange, Finset.mem_Icc]
  constructor
  · intro hc
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs]
    exact (abs_le.mpr hc)
  · intro hc
    rw [← Nat.cast_le (α := ℤ), Int.natCast_natAbs] at hc
    exact abs_le.mp hc

/-- Factored-denominator form of the congruence-fibre reduction.  The real
cutoff hypothesis says that `C` dominates the proximity radius after scaling
by the common ambient modulus `g * a * b`. -/
theorem nearbyReducedPairCount_mul_le_sum_congruenceFiberCount
    {g a b C : ℕ} (hg : 0 < g) (ha : 0 < a) (hb : 0 < b)
    {L M : ℝ}
    (hcut : (g * a * b : ℝ) *
      (L / (g * a : ℕ) + M / (g * b : ℕ)) ≤ C) :
    nearbyReducedPairCount (g * a) (g * b) L M ≤
      ∑ c ∈ signedIntegerRange C, congruenceFiberCount g a b c := by
  classical
  let nearby : Finset (Fin (g * a) × Fin (g * b)) :=
    Finset.univ.filter (isNearbyReducedPair (g * a) (g * b) L M)
  let fibres : Finset (Fin (g * a) × Fin (g * b)) :=
    (signedIntegerRange C).biUnion (congruenceFiber g a b)
  have hga : (0 : ℝ) < (g * a : ℕ) := by positivity
  have hgb : (0 : ℝ) < (g * b : ℕ) := by positivity
  have hgab : (0 : ℝ) < (g * a * b : ℕ) := by positivity
  have hsubset : nearby ⊆ fibres := by
    intro z hz
    have hnear : isNearbyReducedPair (g * a) (g * b) L M z :=
      (Finset.mem_filter.mp hz).2
    rcases hnear.2.2 with ⟨k, hk⟩
    let c : ℤ :=
      (b : ℤ) * (z.1 : ℕ) - (a : ℤ) * (z.2 : ℕ) -
        k * (g * a * b : ℕ)
    have hcscale :
        |(c : ℝ)| < (g * a * b : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) := by
      have halg :
          (c : ℝ) = (g * a * b : ℝ) *
            ((z.1 : ℝ) / (g * a : ℕ) -
              (z.2 : ℝ) / (g * b : ℕ) - k) := by
        dsimp [c]
        push_cast
        field_simp
      have hprod : (0 : ℝ) < (g : ℝ) * a * b := by positivity
      rw [halg, abs_mul, abs_of_pos hprod]
      exact mul_lt_mul_of_pos_left hk hprod
    have hcCReal : |(c : ℝ)| < (C : ℝ) := hcscale.trans_le hcut
    have hcNatLt : c.natAbs < C := by
      rw [← Nat.cast_lt (α := ℝ), ← Int.cast_natCast,
        Int.natCast_natAbs, Int.cast_abs]
      exact hcCReal
    have hcRange : c ∈ signedIntegerRange C :=
      mem_signedIntegerRange_iff.mpr hcNatLt.le
    have hcfibre : z ∈ congruenceFiber g a b c := by
      rw [mem_congruenceFiber_iff]
      refine ⟨hnear.1, hnear.2.1, ?_⟩
      dsimp [c]
      push_cast
      have hmod :
          (g : ZMod (g * a * b)) * a * b = 0 := by
        rw [← Nat.cast_mul, ← Nat.cast_mul, ZMod.natCast_self]
      rw [hmod, mul_zero, sub_zero]
    exact Finset.mem_biUnion.mpr ⟨c, hcRange, hcfibre⟩
  change nearby.card ≤ _
  calc
    nearby.card ≤ fibres.card := Finset.card_le_card hsubset
    _ ≤ ∑ c ∈ signedIntegerRange C, (congruenceFiber g a b c).card := by
      exact Finset.card_biUnion_le
    _ = ∑ c ∈ signedIntegerRange C, congruenceFiberCount g a b c := by
      simp only [congruenceFiberCount]

/-- For positive `q,r`, the product of the gcd and the quotient-product
modulus is the usual least common multiple. -/
theorem gcd_mul_quotients_eq_lcm {q r : ℕ} (hq : 0 < q) :
    q.gcd r * (q / q.gcd r) * (r / q.gcd r) = q.lcm r := by
  let g := q.gcd r
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hqfac : g * (q / g) = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hrfac : g * (r / g) = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  apply Nat.mul_left_cancel hg
  calc
    g * (g * (q / g) * (r / g)) =
        (g * (q / g)) * (g * (r / g)) := by ring
    _ = q * r := by rw [hqfac, hrfac]
    _ = g * q.lcm r := (Nat.gcd_mul_lcm q r).symm

/-- Nearby reduced pairs for arbitrary positive denominators are covered by
the small congruence fibres after factoring out their gcd. -/
theorem nearbyReducedPairCount_le_sum_congruenceFiberCount
    {q r C : ℕ} (hq : 0 < q) (hr : 0 < r) {L M : ℝ}
    (hcut : (q.lcm r : ℝ) * (L / q + M / r) ≤ C) :
    nearbyReducedPairCount q r L M ≤
      ∑ c ∈ signedIntegerRange C,
        congruenceFiberCount (q.gcd r) (q / q.gcd r)
          (r / q.gcd r) c := by
  let g := q.gcd r
  let a := q / g
  let b := r / g
  have hg : 0 < g := Nat.gcd_pos_of_pos_left r hq
  have hgleq : g ≤ q := Nat.le_of_dvd hq (Nat.gcd_dvd_left q r)
  have hgler : g ≤ r := Nat.le_of_dvd hr (Nat.gcd_dvd_right q r)
  have ha : 0 < a := Nat.div_pos hgleq hg
  have hb : 0 < b := Nat.div_pos hgler hg
  have hqfac : g * a = q := Nat.mul_div_cancel' (Nat.gcd_dvd_left q r)
  have hrfac : g * b = r := Nat.mul_div_cancel' (Nat.gcd_dvd_right q r)
  have hlcm : g * a * b = q.lcm r := by
    simpa [g, a, b] using gcd_mul_quotients_eq_lcm hq
  have hlcmR : (g : ℝ) * a * b = (q.lcm r : ℝ) := by
    exact_mod_cast hlcm
  have hqfacR : ((g * a : ℕ) : ℝ) = q := by exact_mod_cast hqfac
  have hrfacR : ((g * b : ℕ) : ℝ) = r := by exact_mod_cast hrfac
  have hcut' : (g * a * b : ℝ) *
      (L / (g * a : ℕ) + M / (g * b : ℕ)) ≤ C := by
    calc
      (g * a * b : ℝ) *
          (L / (g * a : ℕ) + M / (g * b : ℕ)) =
          (q.lcm r : ℝ) * (L / q + M / r) := by
            rw [hlcmR, hqfacR, hrfacR]
      _ ≤ C := hcut
  simpa only [g, a, b, hqfac, hrfac] using
    (nearbyReducedPairCount_mul_le_sum_congruenceFiberCount
      hg ha hb hcut')

/-- The geometric overlap-pair count obeys the same congruence-fibre bound. -/
theorem overlapPairCount_le_sum_congruenceFiberCount
    {q r C : ℕ} (hq : 0 < q) (hr : 0 < r) {L M : ℝ}
    (hcut : (q.lcm r : ℝ) * (L / q + M / r) ≤ C) :
    overlapPairCount q r L M ≤
      ∑ c ∈ signedIntegerRange C,
        congruenceFiberCount (q.gcd r) (q / q.gcd r)
          (r / q.gcd r) c :=
  (overlapPairCount_le_nearbyReducedPairCount q r L M).trans
    (nearbyReducedPairCount_le_sum_congruenceFiberCount hq hr hcut)

end Erdos999
