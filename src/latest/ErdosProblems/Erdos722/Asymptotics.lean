/-
Copyright 2026 The Lean-Proofs Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    http://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/
import ErdosProblems.Erdos722.Reserve
import Mathlib

/-!
# Reusable rational-power thresholds

The design proof records all sparse exponents with one fixed natural
denominator.  Taking the natural floor of `n^(E/d)` lets the finite
combinatorial lemmas remain entirely natural-valued, while the lemmas below
translate their power-cleared hypotheses to the real asymptotic estimates.
-/

namespace Erdos722.Asymptotics

open Filter
open scoped Topology Real

noncomputable section

/-- Natural threshold `⌊n^(E/d)⌋`. -/
def rationalPowerThreshold (E d n : ℕ) : ℕ :=
  ⌊(n : ℝ) ^ ((E : ℝ) / (d : ℝ))⌋₊

lemma rationalPowerThreshold_cast_le (E d n : ℕ) :
    (rationalPowerThreshold E d n : ℝ) ≤
      (n : ℝ) ^ ((E : ℝ) / (d : ℝ)) := by
  exact Nat.floor_le (Real.rpow_nonneg (Nat.cast_nonneg n) _)

lemma rationalPowerThreshold_pow_le
    (E d n : ℕ) (hd : 0 < d) :
    (rationalPowerThreshold E d n) ^ d ≤ n ^ E := by
  have hbase := rationalPowerThreshold_cast_le E d n
  have hpowReal := pow_le_pow_left₀
    (Nat.cast_nonneg (rationalPowerThreshold E d n)) hbase d
  have hexp : ((E : ℝ) / (d : ℝ)) * (d : ℝ) = E := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  have hid :
      (((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ d) = (n : ℝ) ^ E := by
    calc
      (((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ d) =
          ((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ (d : ℝ) := by
        rw [Real.rpow_natCast]
      _ = (n : ℝ) ^ (((E : ℝ) / (d : ℝ)) * (d : ℝ)) := by
        rw [Real.rpow_mul (Nat.cast_nonneg n)]
      _ = (n : ℝ) ^ (E : ℝ) := by rw [hexp]
      _ = ((n : ℝ) ^ E : ℝ) := Real.rpow_natCast _ E
  rw [hid] at hpowReal
  exact_mod_cast hpowReal

lemma pow_rationalExponent_eq
    (E d n : ℕ) (hd : 0 < d) :
    (((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ d) = (n : ℝ) ^ E := by
  have hexp : ((E : ℝ) / (d : ℝ)) * (d : ℝ) = E := by
    have hdR : (d : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hd)
    field_simp
  calc
    (((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ d) =
        ((n : ℝ) ^ ((E : ℝ) / (d : ℝ))) ^ (d : ℝ) := by
      rw [Real.rpow_natCast]
    _ = (n : ℝ) ^ (((E : ℝ) / (d : ℝ)) * (d : ℝ)) := by
      rw [Real.rpow_mul (Nat.cast_nonneg n)]
    _ = (n : ℝ) ^ (E : ℝ) := by rw [hexp]
    _ = ((n : ℝ) ^ E : ℝ) := Real.rpow_natCast _ E

lemma le_rationalPowerThreshold_of_pow_le
    (E d n x : ℕ) (hd : 0 < d) (h : x ^ d ≤ n ^ E) :
    x ≤ rationalPowerThreshold E d n := by
  apply Nat.le_floor
  have hreal : (x : ℝ) ^ d ≤ (n : ℝ) ^ E := by exact_mod_cast h
  rw [← pow_rationalExponent_eq E d n hd] at hreal
  exact (pow_le_pow_iff_left₀ (Nat.cast_nonneg x)
    (Real.rpow_nonneg (Nat.cast_nonneg n) _) (Nat.ne_of_gt hd)).mp hreal

lemma rationalPowerThreshold_le_of_power_lower
    (E d n x : ℕ) (hd : 0 < d) (h : n ^ E ≤ x ^ d) :
    rationalPowerThreshold E d n ≤ x := by
  apply (Nat.pow_le_pow_iff_left (Nat.ne_of_gt hd)).mp
  exact (rationalPowerThreshold_pow_le E d n hd).trans h

lemma rationalPowerExponent_pos {E d : ℕ} (hE : 0 < E) (hd : 0 < d) :
    (0 : ℝ) < (E : ℝ) / (d : ℝ) := by positivity

lemma rationalPowerThreshold_tendsto_atTop
    {E d : ℕ} (hE : 0 < E) (hd : 0 < d) :
    Tendsto (rationalPowerThreshold E d) atTop atTop := by
  exact tendsto_nat_floor_atTop.comp
    ((tendsto_rpow_atTop (rationalPowerExponent_pos hE hd)).comp
      tendsto_natCast_atTop_atTop)

lemma eventually_half_rpow_le_rationalPowerThreshold
    {E d : ℕ} (hE : 0 < E) (hd : 0 < d) :
    ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((E : ℝ) / (d : ℝ)) / 2 ≤
        (rationalPowerThreshold E d n : ℝ) := by
  have htop : Tendsto
      (fun n : ℕ ↦ (n : ℝ) ^ ((E : ℝ) / (d : ℝ))) atTop atTop :=
    (tendsto_rpow_atTop (rationalPowerExponent_pos hE hd)).comp
      tendsto_natCast_atTop_atTop
  have htwo : ∀ᶠ n : ℕ in atTop,
      (2 : ℝ) ≤ (n : ℝ) ^ ((E : ℝ) / (d : ℝ)) :=
    htop.eventually (eventually_ge_atTop 2)
  filter_upwards [htwo] with n hn
  have hfloor := Nat.lt_floor_add_one
    ((n : ℝ) ^ ((E : ℝ) / (d : ℝ)))
  change (n : ℝ) ^ ((E : ℝ) / (d : ℝ)) <
    (rationalPowerThreshold E d n : ℝ) + 1 at hfloor
  nlinarith

/-- A fixed nonnegative multiple of a smaller real power is eventually
bounded by a larger power. -/
theorem eventually_const_mul_rpow_le_rpow
    {a b C : ℝ} (hab : a < b) (hC : 0 ≤ C) :
    ∀ᶠ n : ℕ in atTop, C * (n : ℝ) ^ a ≤ (n : ℝ) ^ b := by
  have hdelta : 0 < b - a := sub_pos.mpr hab
  have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ (b - a)) atTop atTop :=
    (tendsto_rpow_atTop hdelta).comp tendsto_natCast_atTop_atTop
  have hlarge : ∀ᶠ n : ℕ in atTop, C ≤ (n : ℝ) ^ (b - a) :=
    tendsto_atTop.mp ht C
  filter_upwards [hlarge, eventually_ge_atTop (1 : ℕ)] with n hn hn1
  have hnpos : (0 : ℝ) < n := by positivity
  calc
    C * (n : ℝ) ^ a ≤ (n : ℝ) ^ (b - a) * (n : ℝ) ^ a := by gcongr
    _ = (n : ℝ) ^ b := by
      rw [← Real.rpow_add hnpos]
      congr 2
      ring

end

end Erdos722.Asymptotics
