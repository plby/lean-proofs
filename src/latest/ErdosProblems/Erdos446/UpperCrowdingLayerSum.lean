/-
Copyright (c) 2026 The Formal Conjectures Authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Formal Conjectures Authors
-/

import ErdosProblems.Erdos446.UpperCrowdingMass
import ErdosProblems.Erdos446.UpperCrowdingNumerics

/-!
# Erdős Problem 446: summing the fixed-rank crowding layers

This file performs the union bound in the crossing rank and the (possibly
shifted) Abel convolution in Ford's exceptional-layer estimate.  All bounds
retain the reciprocal-factorial normalization `1 / (k+1)!`.
-/

namespace Erdos446

open Finset Real
open scoped BigOperators

/-- Endpoint-safe conversion of the unconditional Smirnov probability bound
to reciprocal-factorial mass. -/
theorem smirnovOccupancyMass_le_uniformFactorial
    {k u v w : ℕ} (hw : 0 < w) (hrel : u + v = k + w) :
    smirnovOccupancyMass k u v ≤
      2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
  by_cases hk0 : k = 0
  · subst k
    have hleOne := smirnovOccupancyMass_le_total 0 u v
    have huOne : (1 : ℝ) ≤ (u + 1 : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 u)
    have hwBase : (1 : ℝ) ≤ (w + 1 : ℝ) := by
      exact_mod_cast (Nat.le_add_left 1 w)
    have hwOne : (1 : ℝ) ≤ (w + 1 : ℝ) ^ 2 := by
      exact one_le_pow₀ hwBase
    have hR : (1 : ℝ) ≤
        2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 := by
      nlinarith [mul_le_mul huOne hwOne (by norm_num : (0 : ℝ) ≤ 1)
        (by positivity : (0 : ℝ) ≤ (u + 1 : ℝ))]
    exact hleOne.trans (by simpa using hR)
  by_cases hv0 : v = 0
  · subst v
    have hzero : smirnovOccupancyMass k u 0 ≤ 0 := by
      simpa [hk0] using smirnovOccupancyMass_le_total k u 0
    exact hzero.trans_eq (by simp [hk0])
  have hk : 0 < k := Nat.pos_of_ne_zero hk0
  have hv : 0 < v := Nat.pos_of_ne_zero hv0
  have hprob := smirnovProbability_le_uniform hk hw hrel
  rw [smirnovOccupancyMass_eq_probability_mul hv]
  calc
    smirnovProbability k u v * (v : ℝ) ^ k / (k.factorial : ℝ) ≤
        (2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 /
          (k + 1 : ℕ)) * (v : ℝ) ^ k / (k.factorial : ℝ) := by
      gcongr
    _ = 2400 * (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 * (v : ℝ) ^ k /
        ((k + 1).factorial : ℝ) := by
      rw [Nat.factorial_succ]
      push_cast
      field_simp

/-- Abel index `j=l-g` for the admissible crossing ranks. -/
def fordCrowdingRankIndices (k u g : ℕ) : Finset ℕ :=
  (Finset.Ico 1 (k + 1 - g)).filter fun j ↦ u ≤ j + g

/-- The crossing-rank union for fixed Smirnov offset, gap, and cell width. -/
noncomputable def fordCrowdingOccupancies
    (k u v g s : ℕ) : Finset (Fin v → ℕ) :=
  (fordCrowdingRankIndices k u g).biUnion fun j ↦
    fordCrowdingOccupanciesAt k u v g s (j + g)

theorem fordCrowdingOccupanciesAt_subset_fordCrowdingOccupancies
    {k u v g s l : ℕ} (hl : l ∈ Finset.Icc (max (g + 1) u) k) :
    fordCrowdingOccupanciesAt k u v g s l ⊆
      fordCrowdingOccupancies k u v g s := by
  have hdata := Finset.mem_Icc.mp hl
  have hj : l - g ∈ fordCrowdingRankIndices k u g := by
    rw [fordCrowdingRankIndices, Finset.mem_filter, Finset.mem_Ico]
    omega
  have hsub := Finset.subset_biUnion_of_mem
    (fun j ↦ fordCrowdingOccupanciesAt k u v g s (j + g)) hj
  change fordCrowdingOccupanciesAt k u v g s l ⊆
    (fordCrowdingRankIndices k u g).biUnion
      (fun j ↦ fordCrowdingOccupanciesAt k u v g s (j + g))
  simpa [show l - g + g = l by omega] using hsub

/-- A nonnegative finite union has mass at most the sum of the masses of
its members; no disjointness is needed. -/
theorem reciprocalFactorialMassOver_biUnion_le
    {v : ℕ} {α : Type*} (S : Finset α)
    (F : α → Finset (Fin v → ℕ)) :
    reciprocalFactorialMassOver (S.biUnion F) ≤
      ∑ a ∈ S, reciprocalFactorialMassOver (F a) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp [reciprocalFactorialMassOver]
  | @insert a S ha ih =>
      rw [Finset.biUnion_insert, Finset.sum_insert ha]
      calc
        reciprocalFactorialMassOver (F a ∪ S.biUnion F) ≤
            reciprocalFactorialMassOver (F a) +
              reciprocalFactorialMassOver (S.biUnion F) := by
          rw [reciprocalFactorialMassOver, reciprocalFactorialMassOver,
            reciprocalFactorialMassOver]
          have hinter := Finset.sum_union_inter
            (s₁ := F a) (s₂ := S.biUnion F)
            (f := fun b ↦ 1 / compositionFactorial b)
          have hinterNonneg : 0 ≤
              ∑ b ∈ F a ∩ S.biUnion F, 1 / compositionFactorial b := by
            apply Finset.sum_nonneg
            intro b hb
            apply one_div_nonneg.mpr
            dsimp [compositionFactorial]
            positivity
          linarith
        _ ≤ reciprocalFactorialMassOver (F a) +
              ∑ x ∈ S, reciprocalFactorialMassOver (F x) :=
          add_le_add_right ih _

/-- One fixed crossing rank, after both endpoint Smirnov estimates. -/
theorem reciprocalFactorialMassOver_fordCrowdingOccupanciesAt_le_uniform
    {k u v g s l w : ℕ}
    (hw : 0 < w) (hrel : u + v = k + w)
    (hg : 1 ≤ g) (hgl : g + 1 ≤ l) (hul : u ≤ l) (hlk : l ≤ k) :
    reciprocalFactorialMassOver
        (fordCrowdingOccupanciesAt k u v g s l) ≤
      (2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
          (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
            ((l - g).factorial : ℝ))) *
        ((((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
        (2400 * (w + 1 : ℝ) ^ 2 *
          (((v - (l - u) : ℕ) : ℝ) ^ (k - l) /
            ((k - l + 1).factorial : ℝ))) := by
  have hhv : l - u < v := by omega
  have hfirst := reciprocalFactorialMassOver_fordCrowdingOccupanciesAt_le
    (s := s) hg hgl hul hlk hhv
  have hpRel : u + (l - u + 1) = (l - g - 1) + (g + 2) := by omega
  have hp := smirnovOccupancyMass_le_uniformFactorial
    (show 0 < g + 2 by omega) hpRel
  have hsRel : 0 + (v - (l - u)) = (k - l) + w := by omega
  have hsuf := smirnovOccupancyMass_le_uniformFactorial hw hsRel
  have hlen : (l - u + 1) - (l - u - s) ≤ s + 1 := by omega
  have hlenR :
      ((((l - u + 1) - (l - u - s) : ℕ) : ℝ)) ^ g ≤
        (((s + 1 : ℕ) : ℝ)) ^ g := by
    gcongr
  apply hfirst.trans
  calc
    smirnovOccupancyMass (l - g - 1) u (l - u + 1) *
          (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
            (g.factorial : ℝ)) *
          smirnovOccupancyMass (k - l) 0 (v - (l - u))) ≤
        (2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
          (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
            ((l - g).factorial : ℝ))) *
        ((((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
        (2400 * (w + 1 : ℝ) ^ 2 *
          (((v - (l - u) : ℕ) : ℝ) ^ (k - l) /
            ((k - l + 1).factorial : ℝ))) := by
      have hfacg : (0 : ℝ) ≤ (g.factorial : ℝ) := by positivity
      have hmid :
          (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
              (g.factorial : ℝ))) ≤
            (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ)) :=
        div_le_div_of_nonneg_right hlenR hfacg
      have hp' : smirnovOccupancyMass (l - g - 1) u (l - u + 1) ≤
          2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
            (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
              ((l - g).factorial : ℝ)) := by
        rw [show l - g = l - g - 1 + 1 by omega]
        convert hp using 1 <;> push_cast <;> ring
      have hsuf' : smirnovOccupancyMass (k - l) 0 (v - (l - u)) ≤
          2400 * (w + 1 : ℝ) ^ 2 *
            (((v - (l - u) : ℕ) : ℝ) ^ (k - l) /
              ((k - l + 1).factorial : ℝ)) := by
        convert hsuf using 1 <;> push_cast <;> ring
      have hPnon : 0 ≤ 2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
          (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
            ((l - g).factorial : ℝ)) := by positivity
      have hMnon : 0 ≤
          (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
            (g.factorial : ℝ))) := by positivity
      have hM'non : 0 ≤
          (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ)) := by
        positivity
      have hSnon : 0 ≤
          smirnovOccupancyMass (k - l) 0 (v - (l - u)) :=
        smirnovOccupancyMass_nonneg _ _ _
      calc
        smirnovOccupancyMass (l - g - 1) u (l - u + 1) *
              (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
                (g.factorial : ℝ)) *
                smirnovOccupancyMass (k - l) 0 (v - (l - u))) ≤
            (2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
              (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
                ((l - g).factorial : ℝ))) *
              (((((l - u + 1) - (l - u - s) : ℕ) : ℝ) ^ g /
                (g.factorial : ℝ)) *
                smirnovOccupancyMass (k - l) 0 (v - (l - u))) :=
          mul_le_mul_of_nonneg_right hp' (mul_nonneg hMnon hSnon)
        _ ≤ (2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
              (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
                ((l - g).factorial : ℝ))) *
              ((((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ)) *
                smirnovOccupancyMass (k - l) 0 (v - (l - u))) := by
          gcongr
        _ ≤ (2400 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
              (((l - u + 1 : ℕ) : ℝ) ^ (l - g - 1) /
                ((l - g).factorial : ℝ))) *
              ((((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ)) *
                (2400 * (w + 1 : ℝ) ^ 2 *
                  (((v - (l - u) : ℕ) : ℝ) ^ (k - l) /
                    ((k - l + 1).factorial : ℝ)))) := by
          gcongr
        _ = _ := by ring

/-- The factorial-normalized Abel summand after the change of variables
`j=l-g`. -/
noncomputable def fordCrowdingAbelSummand
    (k u v g j : ℕ) : ℝ :=
  ((((j + g - u + 1 : ℕ) : ℝ) ^ (j - 1)) /
      (j.factorial : ℝ)) *
    ((((v - (j + g - u) : ℕ) : ℝ) ^ (k - (j + g))) /
      ((k - (j + g) + 1).factorial : ℝ))

noncomputable def fordCrowdingAbelSum
    (k u v g : ℕ) : ℝ :=
  ∑ j ∈ fordCrowdingRankIndices k u g,
    fordCrowdingAbelSummand k u v g j

/-- Union-bound reduction of all crossing ranks to one Abel sum. -/
theorem reciprocalFactorialMassOver_fordCrowdingOccupancies_le_abelSum
    {k u v g s w : ℕ}
    (hw : 0 < w) (hrel : u + v = k + w) (hg : 1 ≤ g) :
    reciprocalFactorialMassOver (fordCrowdingOccupancies k u v g s) ≤
      (2400 ^ 2 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
        (w + 1 : ℝ) ^ 2 *
        (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
      fordCrowdingAbelSum k u v g := by
  have hunion := reciprocalFactorialMassOver_biUnion_le
    (fordCrowdingRankIndices k u g)
    (fun j ↦ fordCrowdingOccupanciesAt k u v g s (j + g))
  apply hunion.trans
  rw [fordCrowdingAbelSum, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j hj
  have hjData := Finset.mem_filter.mp hj
  have hjRange := Finset.mem_Ico.mp hjData.1
  have hgl : g + 1 ≤ j + g := by omega
  have hul : u ≤ j + g := hjData.2
  have hlk : j + g ≤ k := by omega
  have hfix :=
    reciprocalFactorialMassOver_fordCrowdingOccupanciesAt_le_uniform
      hw hrel hg hgl hul hlk (s := s)
  apply hfix.trans_eq
  rw [fordCrowdingAbelSummand]
  have hjg : j + g - g = j := by omega
  have hjgPred : j + g - g - 1 = j - 1 := by omega
  have hkg : k - (j + g) = k - (j + g) := rfl
  simp only [hjg, hjgPred, hkg]
  norm_num [pow_two]
  ring

theorem crowding_inv_factorial_pair_eq_choose_div
    {t j : ℕ} (hjt : j ≤ t) :
    (1 / (j.factorial : ℝ)) *
        (1 / (((t - j).factorial : ℕ) : ℝ)) =
      (t.choose j : ℝ) / (t.factorial : ℝ) := by
  have hjFac : (j.factorial : ℝ) ≠ 0 := by positivity
  have htjFac : (((t - j).factorial : ℕ) : ℝ) ≠ 0 := by positivity
  have htFac : (t.factorial : ℝ) ≠ 0 := by positivity
  have hchooseNat := Nat.choose_mul_factorial_mul_factorial hjt
  have hchoose :
      (t.choose j : ℝ) * (j.factorial : ℝ) *
          (((t - j).factorial : ℕ) : ℝ) =
        (t.factorial : ℝ) := by exact_mod_cast hchooseNat
  field_simp
  nlinarith

/-- In the range where the first Abel parameter is at least `-1`, the
rank convolution is an ordinary Abel interior sum.  The second affine base
is enlarged from `w-1` to `w`, producing the uniform final base `v+2`. -/
theorem fordCrowdingAbelSum_le_ordinary
    {k u v g w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (hgk : g < k) (hu : u ≤ g + 2) :
    fordCrowdingAbelSum k u v g ≤
      Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
        (((k + 1 - g).factorial : ℕ) : ℝ) := by
  let t := k + 1 - g
  let a : ℝ := (g + 1 : ℕ) - (u : ℝ)
  let B : ℝ := w
  have ht : t = k - g + 1 := by dsimp [t]; omega
  have ht1 : 1 < t := by omega
  have ha : -1 ≤ a := by
    dsimp [a]
    have huR : (u : ℝ) ≤ (g : ℝ) + 2 := by exact_mod_cast hu
    push_cast
    linarith
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hpoint : ∀ j ∈ fordCrowdingRankIndices k u g,
      fordCrowdingAbelSummand k u v g j ≤
        (1 / (t.factorial : ℝ)) *
          ((t.choose j : ℝ) * (a + j) ^ (j - 1) *
            (B + (t - j : ℕ)) ^ (t - j - 1)) := by
    intro j hj
    have hjData := Finset.mem_filter.mp hj
    have hjRange := Finset.mem_Ico.mp hjData.1
    have hju : u ≤ j + g := hjData.2
    have hjgk : j + g ≤ k := by omega
    have hjt : j ≤ t := by omega
    have hden : k - (j + g) + 1 = t - j := by omega
    have hexp : k - (j + g) = t - j - 1 := by omega
    have hleft : (((j + g - u + 1 : ℕ) : ℝ)) = a + j := by
      dsimp [a]
      rw [Nat.cast_add, Nat.cast_one, Nat.cast_sub hju]
      push_cast
      ring
    have hsuf : v - (j + g - u) ≤ w + (t - j) := by omega
    have hsufR : (((v - (j + g - u) : ℕ) : ℝ)) ≤
        B + (t - j : ℕ) := by
      dsimp [B]
      exact_mod_cast hsuf
    have hpow : (((v - (j + g - u) : ℕ) : ℝ) ^
          (k - (j + g))) ≤
        (B + (t - j : ℕ)) ^ (t - j - 1) := by
      rw [hexp]
      gcongr
    have hfac := crowding_inv_factorial_pair_eq_choose_div hjt
    rw [fordCrowdingAbelSummand, hleft, hden]
    calc
      (a + (j : ℝ)) ^ (j - 1) / (j.factorial : ℝ) *
            (((v - (j + g - u) : ℕ) : ℝ) ^ (k - (j + g)) /
              (((t - j).factorial : ℕ) : ℝ)) ≤
          (a + (j : ℝ)) ^ (j - 1) / (j.factorial : ℝ) *
            ((B + (t - j : ℕ)) ^ (t - j - 1) /
              (((t - j).factorial : ℕ) : ℝ)) := by
        gcongr
        have hbase : 0 ≤ a + (j : ℝ) := by
          rw [← hleft]
          positivity
        positivity
      _ = (1 / (t.factorial : ℝ)) *
          ((t.choose j : ℝ) * (a + j) ^ (j - 1) *
            (B + (t - j : ℕ)) ^ (t - j - 1)) := by
        calc
          (a + (j : ℝ)) ^ (j - 1) / (j.factorial : ℝ) *
                ((B + (t - j : ℕ)) ^ (t - j - 1) /
                  (((t - j).factorial : ℕ) : ℝ)) =
              ((a + (j : ℝ)) ^ (j - 1) *
                (B + (t - j : ℕ)) ^ (t - j - 1)) *
                ((1 / (j.factorial : ℝ)) *
                  (1 / (((t - j).factorial : ℕ) : ℝ))) := by ring
          _ = _ := by rw [hfac]; ring
  have hsubset : fordCrowdingRankIndices k u g ⊆ Finset.Ico 1 t := by
    intro j hj
    exact (Finset.mem_filter.mp hj).1
  have hnonneg : ∀ j ∈ Finset.Ico 1 t,
      0 ≤ (1 / (t.factorial : ℝ)) *
        ((t.choose j : ℝ) * (a + j) ^ (j - 1) *
          (B + (t - j : ℕ)) ^ (t - j - 1)) := by
    intro j hj
    have hj1 := (Finset.mem_Ico.mp hj).1
    have hbase : 0 ≤ a + (j : ℝ) := by
      have hjR : (1 : ℝ) ≤ j := by exact_mod_cast hj1
      linarith
    positivity
  calc
    fordCrowdingAbelSum k u v g ≤
        ∑ j ∈ fordCrowdingRankIndices k u g,
          (1 / (t.factorial : ℝ)) *
            ((t.choose j : ℝ) * (a + j) ^ (j - 1) *
              (B + (t - j : ℕ)) ^ (t - j - 1)) := by
      rw [fordCrowdingAbelSum]
      exact Finset.sum_le_sum hpoint
    _ ≤ ∑ j ∈ Finset.Ico 1 t,
          (1 / (t.factorial : ℝ)) *
            ((t.choose j : ℝ) * (a + j) ^ (j - 1) *
              (B + (t - j : ℕ)) ^ (t - j - 1)) :=
      Finset.sum_le_sum_of_subset_of_nonneg hsubset
        (fun j hj hnot ↦ hnonneg j hj)
    _ = (1 / (t.factorial : ℝ)) *
          fordAbelInteriorSum (t - 1) a B := by
      rw [fordAbelInteriorSum, show t - 1 + 1 = t by omega,
        Finset.mul_sum]
    _ ≤ (1 / (t.factorial : ℝ)) *
          (Real.exp 4 * (t + a + B) ^ (t - 1)) := by
      gcongr
      have habel := fordAbelInteriorSum_le_exp_four
        (t - 1) (by omega) ha hB
      have htCast : (((t - 1 : ℕ) : ℝ) + 1) = (t : ℝ) := by
        exact_mod_cast (show t - 1 + 1 = t by omega)
      apply habel.trans_eq
      rw [htCast]
    _ = Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
          (((k + 1 - g).factorial : ℕ) : ℝ) := by
      have hbase : t + a + B = ((v + 2 : ℕ) : ℝ) := by
        have hrelR : (u : ℝ) + (v : ℝ) = (k : ℝ) + (w : ℝ) := by
          exact_mod_cast hrel
        dsimp [t, a, B]
        push_cast [Nat.cast_sub (show g ≤ k + 1 by omega)]
        linarith
      rw [hbase]
      have hexp : t - 1 = k - g := by omega
      rw [hexp]
      dsimp [t]
      ring

/-- If the first Abel parameter is a more negative integer, shift the
interior sum.  Again the harmless enlargement `w-1 ≤ w` gives the same
uniform base `v+2`. -/
theorem fordCrowdingAbelSum_le_shifted
    {k u v g w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (hgk : g < k) (hu : g + 2 < u) :
    fordCrowdingAbelSum k u v g ≤
      Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
        (((k + 1 - g).factorial : ℕ) : ℝ) := by
  by_cases huk : u ≤ k
  · let t := k + 1 - g
    let d := u - g - 1
    let B : ℝ := w
    have ht : t = k - g + 1 := by dsimp [t]; omega
    have hd : 1 ≤ d := by dsimp [d]; omega
    have hdt : d < t := by dsimp [d, t]; omega
    have hB : 1 ≤ B := by dsimp [B]; exact_mod_cast hw
    have hindex : fordCrowdingRankIndices k u g = Finset.Ico (d + 1) t := by
      ext j
      rw [fordCrowdingRankIndices, Finset.mem_filter,
        Finset.mem_Ico, Finset.mem_Ico]
      dsimp [d, t]
      constructor
      · intro hj
        omega
      · intro hj
        omega
    have hpoint : ∀ j ∈ Finset.Ico (d + 1) t,
        fordCrowdingAbelSummand k u v g j ≤
          (1 / (t.factorial : ℝ)) *
            ((t.choose j : ℝ) * (((j : ℝ) - (d : ℝ)) ^ (j - 1)) *
              (B + (t - j : ℕ)) ^ (t - j - 1)) := by
      intro j hj
      have hjRange := Finset.mem_Ico.mp hj
      have hdu : d + 1 = u - g := by dsimp [d]; omega
      have hju : u ≤ j + g := by omega
      have hjgk : j + g ≤ k := by omega
      have hjt : j ≤ t := hjRange.2.le
      have hdj : d ≤ j := by omega
      have hden : k - (j + g) + 1 = t - j := by omega
      have hexp : k - (j + g) = t - j - 1 := by omega
      have hleft : j + g - u + 1 = j - d := by dsimp [d]; omega
      have hsuf : v - (j + g - u) ≤ w + (t - j) := by omega
      have hsufR : (((v - (j + g - u) : ℕ) : ℝ)) ≤
          B + (t - j : ℕ) := by
        dsimp [B]
        exact_mod_cast hsuf
      have hpow : (((v - (j + g - u) : ℕ) : ℝ) ^
            (k - (j + g))) ≤
          (B + (t - j : ℕ)) ^ (t - j - 1) := by
        rw [hexp]
        gcongr
      have hfac := crowding_inv_factorial_pair_eq_choose_div hjt
      rw [fordCrowdingAbelSummand, hleft, hden]
      calc
        (((j - d : ℕ) : ℝ) ^ (j - 1)) / (j.factorial : ℝ) *
              (((v - (j + g - u) : ℕ) : ℝ) ^ (k - (j + g)) /
                (((t - j).factorial : ℕ) : ℝ)) ≤
            (((j - d : ℕ) : ℝ) ^ (j - 1)) / (j.factorial : ℝ) *
              ((B + (t - j : ℕ)) ^ (t - j - 1) /
                (((t - j).factorial : ℕ) : ℝ)) := by
          gcongr <;> positivity
        _ = (1 / (t.factorial : ℝ)) *
            ((t.choose j : ℝ) * (((j : ℝ) - (d : ℝ)) ^ (j - 1)) *
              (B + (t - j : ℕ)) ^ (t - j - 1)) := by
          rw [← Nat.cast_sub hdj]
          calc
            (((j - d : ℕ) : ℝ) ^ (j - 1)) / (j.factorial : ℝ) *
                  ((B + (t - j : ℕ)) ^ (t - j - 1) /
                    (((t - j).factorial : ℕ) : ℝ)) =
                ((((j - d : ℕ) : ℝ) ^ (j - 1)) *
                  (B + (t - j : ℕ)) ^ (t - j - 1)) *
                  ((1 / (j.factorial : ℝ)) *
                    (1 / (((t - j).factorial : ℕ) : ℝ))) := by ring
            _ = _ := by rw [hfac]; ring
    calc
      fordCrowdingAbelSum k u v g ≤
          (1 / (t.factorial : ℝ)) *
            fordAbelIntegerNegativePositiveSum t d B := by
        rw [fordCrowdingAbelSum, hindex,
          fordAbelIntegerNegativePositiveSum, Finset.mul_sum]
        exact Finset.sum_le_sum hpoint
      _ ≤ (1 / (t.factorial : ℝ)) *
          (Real.exp 4 * (t - d + B) ^ (t - 1)) := by
        gcongr
        exact fordAbelIntegerNegativePositiveSum_le hd hdt hB
      _ = Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
          (((k + 1 - g).factorial : ℕ) : ℝ) := by
        have hrelR : (u : ℝ) + (v : ℝ) = (k : ℝ) + (w : ℝ) := by
          exact_mod_cast hrel
        have hdR : (d : ℝ) = (u : ℝ) - (g : ℝ) - 1 := by
          dsimp [d]
          rw [Nat.cast_sub (show 1 ≤ u - g by omega),
            Nat.cast_sub (show g ≤ u by omega)]
          ring
        have hbase : (t : ℝ) - (d : ℝ) + B =
            ((v + 2 : ℕ) : ℝ) := by
          rw [hdR]
          dsimp [t, B]
          push_cast [Nat.cast_sub (show g ≤ k + 1 by omega)]
          linarith
        rw [hbase]
        have hexp : t - 1 = k - g := by omega
        rw [hexp]
        dsimp [t]
        ring
  · have hindices : fordCrowdingRankIndices k u g = ∅ := by
      ext j
      constructor
      · intro hj
        rw [fordCrowdingRankIndices, Finset.mem_filter,
          Finset.mem_Ico] at hj
        exfalso
        omega
      · intro hj
        simp at hj
    rw [fordCrowdingAbelSum, hindices]
    simp only [sum_empty, Nat.cast_add, Nat.cast_ofNat, ge_iff_le]
    positivity

/-- Uniform ordinary/shifted Abel bound for the crossing-rank sum. -/
theorem fordCrowdingAbelSum_le
    {k u v g w : ℕ} (hw : 0 < w) (hrel : u + v = k + w)
    (hgk : g < k) :
    fordCrowdingAbelSum k u v g ≤
      Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
        (((k + 1 - g).factorial : ℕ) : ℝ) := by
  by_cases hu : u ≤ g + 2
  · exact fordCrowdingAbelSum_le_ordinary hw hrel hgk hu
  · exact fordCrowdingAbelSum_le_shifted hw hrel hgk (by omega)

/-- Ford's fixed-`(u,g,s)` crowding mass after summing every crossing rank
and applying the ordinary or shifted Abel convolution. -/
theorem reciprocalFactorialMassOver_fordCrowdingOccupancies_le_abel
    {k u v g s w : ℕ}
    (hw : 0 < w) (hrel : u + v = k + w)
    (hg : 1 ≤ g) (hgk : g < k) :
    reciprocalFactorialMassOver (fordCrowdingOccupancies k u v g s) ≤
      (2400 ^ 2 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
        (w + 1 : ℝ) ^ 2 *
        (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
      (Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
        (((k + 1 - g).factorial : ℕ) : ℝ)) := by
  have hmass :=
    reciprocalFactorialMassOver_fordCrowdingOccupancies_le_abelSum
      hw hrel hg (s := s)
  have habel := fordCrowdingAbelSum_le hw hrel hgk
  apply hmass.trans
  exact mul_le_mul_of_nonneg_left habel (by positivity)

/-- Fully normalized fixed crowding layer.  This is equation (32h): the
crucial denominator is `(k+1)!`, not `k!`. -/
theorem reciprocalFactorialMassOver_fordCrowdingOccupancies_le_normalized
    {k u v g s w : ℕ}
    (hv : 0 < v) (hw : 0 < w) (hrel : u + v = k + w)
    (hg : 1 ≤ g) (hgk : g < k) (hkv : k ≤ 10 * v) :
    reciprocalFactorialMassOver (fordCrowdingOccupancies k u v g s) ≤
      2400 ^ 2 * Real.exp 27 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
        (w + 1 : ℝ) ^ 2 *
        ((((10 * (s + 1 : ℕ) : ℕ) : ℝ) ^ g /
          (g.factorial : ℝ))) *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hraw := reciprocalFactorialMassOver_fordCrowdingOccupancies_le_abel
    hw hrel hg hgk (s := s)
  have hnum := crowdingAbelExpFactor_le_normalized_ten_add_two
    hv hgk.le hkv
  have hnum' :
      Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
          (((k + 1 - g).factorial : ℕ) : ℝ) ≤
        Real.exp 27 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
          ((k + 1).factorial : ℝ) := by
    calc
      Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
            (((k + 1 - g).factorial : ℕ) : ℝ) =
          Real.exp 4 *
            ((((v + 2 : ℕ) : ℝ) ^ (k - g)) /
              (((k + 1 - g).factorial : ℕ) : ℝ)) := by ring
      _ ≤ _ := hnum
  apply hraw.trans
  calc
    (2400 ^ 2 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
          (w + 1 : ℝ) ^ 2 *
          (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
        (Real.exp 4 * (((v + 2 : ℕ) : ℝ) ^ (k - g)) /
          (((k + 1 - g).factorial : ℕ) : ℝ)) ≤
      (2400 ^ 2 * (u + 1 : ℝ) * (g + 3 : ℝ) ^ 2 *
          (w + 1 : ℝ) ^ 2 *
          (((s + 1 : ℕ) : ℝ) ^ g / (g.factorial : ℝ))) *
        (Real.exp 27 * (10 : ℝ) ^ g * (v : ℝ) ^ k /
          ((k + 1).factorial : ℝ)) :=
      mul_le_mul_of_nonneg_left hnum' (by positivity)
    _ = _ := by
      push_cast
      rw [mul_pow]
      ring

theorem crowding_gap_factorial_absorption
    {g : ℕ} (hg : 8 ≤ g) (X : ℝ) (hX : 0 ≤ X) :
    ((g + 3 : ℕ) : ℝ) ^ 2 * X / (g.factorial : ℝ) ≤
      4 * (X / ((g - 2).factorial : ℝ)) := by
  have hfacNat : g.factorial = g * (g - 1) * (g - 2).factorial := by
    have hrepr : g = (g - 2) + 2 := by omega
    nth_rw 1 [hrepr]
    rw [Nat.factorial_succ, Nat.factorial_succ]
    rw [show g - 2 + 2 = g by omega,
      show g - 2 + 1 = g - 1 by omega]
    ring
  have hcoeff : (((g + 3 : ℕ) : ℝ) ^ 2) ≤
      4 * ((g : ℝ) * (g - 1 : ℕ)) := by
    have hgR : (8 : ℝ) ≤ g := by exact_mod_cast hg
    have hgm1 : (((g - 1 : ℕ) : ℝ)) = (g : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ g by omega)]
      norm_num
    rw [hgm1]
    push_cast
    have hprod : 0 ≤ ((g : ℝ) - 8) * (3 * (g : ℝ) + 14) := by
      positivity
    nlinarith
  have hfac : (0 : ℝ) < (g.factorial : ℝ) := by positivity
  have hfac2 : (0 : ℝ) < ((g - 2).factorial : ℝ) := by positivity
  rw [show 4 * (X / ((g - 2).factorial : ℝ)) =
    (4 * X) / ((g - 2).factorial : ℝ) by ring]
  apply (div_le_div_iff₀ hfac hfac2).2
  rw [hfacNat]
  push_cast [Nat.cast_sub (show 1 ≤ g by omega)]
  have hcoeff' : ((g : ℝ) + 3) ^ 2 ≤
      4 * ((g : ℝ) * ((g : ℝ) - 1)) := by
    have hg1cast : (((g - 1 : ℕ) : ℝ)) = (g : ℝ) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ g by omega)]
      norm_num
    rw [hg1cast] at hcoeff
    norm_num at hcoeff ⊢
    exact hcoeff
  calc
    (((g : ℝ) + 3) ^ 2 * X) * ((g - 2).factorial : ℝ) ≤
        (4 * ((g : ℝ) * ((g : ℝ) - 1)) * X) *
          ((g - 2).factorial : ℝ) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right hcoeff' hX) (by positivity)
    _ = (4 * X) *
        ((g : ℝ) * ((g : ℝ) - 1) * ((g - 2).factorial : ℝ)) := by
      ring

/-- Dyadic specialization with Ford's exponent-shifted factorial
suppression.  The decay is `2^(-2^(m+3))`, the form needed when
`m ≥ h-3` is summed over the failed depth. -/
theorem reciprocalFactorialMassOver_fordDyadicCrowding_le_suppressed
    {k u v m w : ℕ}
    (hv : 0 < v) (hw : 0 < w) (hrel : u + v = k + w)
    (hm : 3 ≤ m) (hgk : 2 ^ m < k) (hkv : k ≤ 10 * v) :
    reciprocalFactorialMassOver
        (fordCrowdingOccupancies k u v (2 ^ m) (2 * m)) ≤
      (4 * 2400 ^ 2 * Real.exp 27 *
          fordCrowdingStrongSuppressionConstant) *
        (u + 1 : ℝ) * (w + 1 : ℝ) ^ 2 /
          (2 : ℝ) ^ (2 ^ (m + 3)) *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
  have hg : 1 ≤ 2 ^ m := one_le_pow₀ (by omega)
  have hnorm :=
    reciprocalFactorialMassOver_fordCrowdingOccupancies_le_normalized
      hv hw hrel hg hgk hkv (s := 2 * m)
  have hgap : 8 ≤ 2 ^ m := by
    calc
      8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by omega) hm
  have hbase : 10 * (2 * m + 1) = 20 * m + 10 := by omega
  have habsorb := crowding_gap_factorial_absorption hgap
    ((((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m))) (by positivity)
  have hsuppress := fordCrowdingFactorialSuppression_shifted m
  have hfactor :
      (((2 ^ m + 3 : ℕ) : ℝ) ^ 2 *
          (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
            (((2 ^ m).factorial : ℕ) : ℝ)) ≤
        4 * fordCrowdingStrongSuppressionConstant /
          (2 : ℝ) ^ (2 ^ (m + 3)) := by
    calc
      (((2 ^ m + 3 : ℕ) : ℝ) ^ 2 *
            (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
              (((2 ^ m).factorial : ℕ) : ℝ)) ≤
          4 * ((((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
            (((2 ^ m - 2).factorial : ℕ) : ℝ)) := habsorb
      _ ≤ 4 * (fordCrowdingStrongSuppressionConstant /
          (2 : ℝ) ^ (2 ^ (m + 3))) :=
        mul_le_mul_of_nonneg_left hsuppress (by norm_num)
      _ = _ := by ring
  have hfactor' :
      (((2 ^ m : ℕ) : ℝ) + 3) ^ 2 *
          (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
            (((2 ^ m).factorial : ℕ) : ℝ) ≤
        4 * fordCrowdingStrongSuppressionConstant /
          (2 : ℝ) ^ (2 ^ (m + 3)) := by
    simpa only [Nat.cast_add, Nat.cast_ofNat] using hfactor
  apply hnorm.trans
  rw [hbase]
  calc
    2400 ^ 2 * Real.exp 27 * (u + 1 : ℝ) *
          (((2 ^ m : ℕ) : ℝ) + 3) ^ 2 * (w + 1 : ℝ) ^ 2 *
          ((((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m) /
            (((2 ^ m).factorial : ℕ) : ℝ))) *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) =
        (2400 ^ 2 * Real.exp 27 * (u + 1 : ℝ) *
          (w + 1 : ℝ) ^ 2) *
          (((((2 ^ m : ℕ) : ℝ) + 3) ^ 2 *
            (((20 * m + 10 : ℕ) : ℝ) ^ (2 ^ m)) /
              (((2 ^ m).factorial : ℕ) : ℝ))) *
          ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by ring
    _ ≤ (2400 ^ 2 * Real.exp 27 * (u + 1 : ℝ) *
          (w + 1 : ℝ) ^ 2) *
        (4 * fordCrowdingStrongSuppressionConstant /
          (2 : ℝ) ^ (2 ^ (m + 3))) *
        ((v : ℝ) ^ k / ((k + 1).factorial : ℝ)) := by
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hfactor' (by positivity)) (by positivity)
    _ = _ := by ring

end Erdos446
