/- leanprover/lean4:v4.33.0 mathlib v4.33.0 -/
/-
Copyright 2026 The Formal Conjectures Authors.

Licensed under the Apache License, Version 2.0 (the "License");
you may not use this file except in compliance with the License.
You may obtain a copy of the License at

    https://www.apache.org/licenses/LICENSE-2.0

Unless required by applicable law or agreed to in writing, software
distributed under the License is distributed on an "AS IS" BASIS,
WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
See the License for the specific language governing permissions and
limitations under the License.
-/

import ErdosProblems.Erdos1165.PotentialRadialMass
import ErdosProblems.Erdos1165.PotentialRadialSums
import ErdosProblems.Erdos1165.PotentialGradient

/-!
# Uniform comparison on radial shells

This file sums the pointwise estimates from `PotentialRadialMass`.  Two
diagonal-coordinate points whose squared radii differ by `O(ρ)` and whose
radii are comparable to `ρ` have potential-kernel values differing by
`O(ρ⁻¹)`.  This is the angular estimate needed to pass from an exact
coordinate-axis expansion to a genuinely radial expansion.
-/

open Real
open scoped BigOperators Topology

namespace Erdos1165
namespace PotentialRadialShell

open PotentialFourierIntegral
open PotentialGradient
open PotentialRadialMass
open PotentialRadialSums

/-- The late local-CLT error, with time written as `k+1`. -/
noncomputable def localEnvelope (Q ρ k : ℕ) : ℝ :=
  Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (Real.pi * (k + 1)) *
    (16 * (ρ : ℝ) * (Q : ℝ) / (k + 1 : ℝ) ^ 2 +
      (Q : ℝ) / (k + 1 : ℝ) ^ 2 + 2 / (3 * (k + 1 : ℝ)))

/-- The Gaussian main-term error caused by changing the squared radius. -/
noncomputable def radiusGapEnvelope (Q Q' k : ℕ) : ℝ :=
  |(Q : ℝ) - (Q' : ℝ)| / (k + 1 : ℝ) *
    (Real.exp (-(min Q Q' : ℕ) / (k + 1 : ℝ)) /
      (Real.pi * (k + 1 : ℝ)))

lemma localEnvelope_nonneg (Q ρ k : ℕ) : 0 ≤ localEnvelope Q ρ k := by
  unfold localEnvelope
  positivity

lemma radiusGapEnvelope_nonneg (Q Q' k : ℕ) :
    0 ≤ radiusGapEnvelope Q Q' k := by
  unfold radiusGapEnvelope
  positivity

private lemma one_div_pi_le_one : (1 : ℝ) / Real.pi ≤ 1 := by
  have hpi : (1 : ℝ) ≤ Real.pi := by linarith [Real.two_le_pi]
  simpa using one_div_le_one_div_of_le (by norm_num : (0 : ℝ) < 1) hpi

lemma localEnvelope_le_weights (Q ρ k : ℕ) :
    localEnvelope Q ρ k ≤
      (16 * (ρ : ℝ) * Q + Q) * cubeGaussianWeight Q k +
        squareGaussianWeight Q k := by
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hexp : 0 ≤ Real.exp (-(Q : ℝ) / (2 * (k + 1))) :=
    (Real.exp_pos _).le
  have hpi : 0 < Real.pi := Real.pi_pos
  unfold localEnvelope cubeGaussianWeight squareGaussianWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hfirst :
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) *
        (16 * (ρ : ℝ) * Q / (k + 1) ^ 2 + Q / (k + 1) ^ 2) ≤
      (16 * (ρ : ℝ) * Q + Q) *
        (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 3) := by
    have hcoef : (1 : ℝ) / Real.pi ≤ 1 := one_div_pi_le_one
    calc
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
            (Real.pi * (k + 1)) *
          (16 * (ρ : ℝ) * Q / (k + 1) ^ 2 + Q / (k + 1) ^ 2) =
        ((1 : ℝ) / Real.pi) *
          ((16 * (ρ : ℝ) * Q + Q) *
            (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 3)) := by
              field_simp
      _ ≤ 1 * ((16 * (ρ : ℝ) * Q + Q) *
            (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 3)) := by
          gcongr
      _ = _ := by ring
  have hsecond :
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) * (2 / (3 * (k + 1))) ≤
        Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 2 := by
    have hc : (2 : ℝ) / (3 * Real.pi) ≤ 1 := by
      have : (2 : ℝ) ≤ 3 * Real.pi := by nlinarith [Real.two_le_pi]
      rw [div_le_one (by positivity : (0 : ℝ) < 3 * Real.pi)]
      exact this
    calc
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) * (2 / (3 * (k + 1))) =
        (2 / (3 * Real.pi)) *
          (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 2) := by
            field_simp
      _ ≤ 1 * (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 2) := by
        gcongr
      _ = _ := by ring
  calc
    Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) *
        (16 * (ρ : ℝ) * Q / (k + 1) ^ 2 + Q / (k + 1) ^ 2 +
          2 / (3 * (k + 1))) =
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) *
        (16 * (ρ : ℝ) * Q / (k + 1) ^ 2 + Q / (k + 1) ^ 2) +
      Real.exp (-(Q : ℝ) / (2 * (k + 1))) /
          (Real.pi * (k + 1)) * (2 / (3 * (k + 1))) := by ring
    _ ≤ (16 * (ρ : ℝ) * Q + Q) *
          (Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 3) +
        Real.exp (-(Q : ℝ) / (2 * (k + 1))) / (k + 1) ^ 2 :=
      add_le_add hfirst hsecond

theorem summable_localEnvelope (Q ρ : ℕ) : Summable (localEnvelope Q ρ) := by
  apply Summable.of_nonneg_of_le (localEnvelope_nonneg Q ρ)
    (localEnvelope_le_weights Q ρ)
  exact ((summable_cubeGaussianWeight Q).mul_left
      (16 * (ρ : ℝ) * Q + Q)).add (summable_squareGaussianWeight Q)

/-- The total local-CLT error has the required inverse-radius scale. -/
theorem tsum_localEnvelope_le {Q ρ : ℕ} (hρ : 2 ≤ ρ)
    (hQlo : ρ ^ 2 ≤ Q) :
    ∑' k : ℕ, localEnvelope Q ρ k ≤ 10000 / (ρ : ℝ) := by
  have hQ : 0 < Q := lt_of_lt_of_le (by positivity : 0 < ρ ^ 2) hQlo
  have hcube := tsum_cubeGaussianWeight_le hQ
  have hsquare := tsum_squareGaussianWeight_le hQ
  have hsum := Summable.tsum_le_tsum (localEnvelope_le_weights Q ρ)
    (summable_localEnvelope Q ρ)
    (((summable_cubeGaussianWeight Q).mul_left
      (16 * (ρ : ℝ) * Q + Q)).add (summable_squareGaussianWeight Q))
  rw [Summable.tsum_add
    ((summable_cubeGaussianWeight Q).mul_left
      (16 * (ρ : ℝ) * Q + Q))
    (summable_squareGaussianWeight Q), tsum_mul_left] at hsum
  calc
      ∑' k : ℕ, localEnvelope Q ρ k ≤
          (16 * (ρ : ℝ) * Q + Q) *
              (∑' k : ℕ, cubeGaussianWeight Q k) +
            ∑' k : ℕ, squareGaussianWeight Q k := hsum
      _ ≤ (16 * (ρ : ℝ) * Q + Q) * (400 / (Q : ℝ) ^ 2) +
            400 / (Q : ℝ) := by gcongr
      _ ≤ 10000 / (ρ : ℝ) := by
        have hρR : (0 : ℝ) < ρ := by positivity
        have hρtwo : (2 : ℝ) ≤ ρ := by exact_mod_cast hρ
        have hQR : (ρ : ℝ) ^ 2 ≤ Q := by exact_mod_cast hQlo
        have hQpos : (0 : ℝ) < Q := by exact_mod_cast hQ
        apply (le_div_iff₀ hρR).2
        field_simp [ne_of_gt hQpos]
        nlinarith

lemma radiusGapEnvelope_le_weight (Q Q' k : ℕ) :
    radiusGapEnvelope Q Q' k ≤
      |(Q : ℝ) - (Q' : ℝ)| * squareGaussianWeight (min Q Q') k := by
  unfold radiusGapEnvelope squareGaussianWeight
  norm_num only [Nat.cast_add, Nat.cast_one]
  have hk : (0 : ℝ) < k + 1 := by positivity
  have hmin : (0 : ℝ) ≤ (min Q Q' : ℕ) := by positivity
  have hexp : Real.exp (-(min Q Q' : ℕ) / (k + 1 : ℝ)) ≤
      Real.exp (-(min Q Q' : ℕ) / (2 * (k + 1 : ℝ))) := by
    apply Real.exp_le_exp.mpr
    have hhalf : ((min Q Q' : ℕ) : ℝ) / (2 * (k + 1)) ≤
        ((min Q Q' : ℕ) : ℝ) / (k + 1) := by
      apply div_le_div_of_nonneg_left hmin hk
      linarith
    simpa only [neg_div] using neg_le_neg hhalf
  have hpi := one_div_pi_le_one
  calc
    |(Q : ℝ) - (Q' : ℝ)| / (k + 1) *
        (Real.exp (-(min Q Q' : ℕ) / (k + 1)) /
          (Real.pi * (k + 1))) =
      |(Q : ℝ) - (Q' : ℝ)| * ((1 / Real.pi) *
        (Real.exp (-(min Q Q' : ℕ) / (k + 1)) / (k + 1) ^ 2)) := by
          field_simp
    _ ≤ |(Q : ℝ) - (Q' : ℝ)| * (1 *
        (Real.exp (-(min Q Q' : ℕ) / (2 * (k + 1))) / (k + 1) ^ 2)) := by
      gcongr
    _ = _ := by ring

theorem summable_radiusGapEnvelope (Q Q' : ℕ) :
    Summable (radiusGapEnvelope Q Q') := by
  apply Summable.of_nonneg_of_le (radiusGapEnvelope_nonneg Q Q')
    (radiusGapEnvelope_le_weight Q Q')
  exact (summable_squareGaussianWeight (min Q Q')).mul_left _

private lemma abs_natCast_sub_eq_natGap (a b : ℕ) :
    |(a : ℝ) - (b : ℝ)| = (natGap a b : ℕ) := by
  rcases le_total a b with h | h
  · have hR : (a : ℝ) ≤ b := by exact_mod_cast h
    rw [abs_of_nonpos (sub_nonpos.mpr hR), natGap_eq_sub_of_le h]
    rw [Nat.cast_sub h]
    ring
  · have hR : (b : ℝ) ≤ a := by exact_mod_cast h
    rw [abs_of_nonneg (sub_nonneg.mpr hR), natGap_comm,
      natGap_eq_sub_of_le h]
    rw [Nat.cast_sub h]

/-- The summed Gaussian-radius mismatch is `O(ρ⁻¹)` when the squared-radius
gap is `O(ρ)`. -/
theorem tsum_radiusGapEnvelope_le {Q Q' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hQlo : ρ ^ 2 ≤ Q) (hQlo' : ρ ^ 2 ≤ Q')
    (hgap : natGap Q Q' ≤ 8 * ρ) :
    ∑' k : ℕ, radiusGapEnvelope Q Q' k ≤ 4000 / (ρ : ℝ) := by
  have hminNat : ρ ^ 2 ≤ min Q Q' := le_min hQlo hQlo'
  have hminPos : 0 < min Q Q' :=
    lt_of_lt_of_le (by positivity : 0 < ρ ^ 2) hminNat
  have hsquare := tsum_squareGaussianWeight_le hminPos
  have hsum := Summable.tsum_le_tsum (radiusGapEnvelope_le_weight Q Q')
    (summable_radiusGapEnvelope Q Q')
    ((summable_squareGaussianWeight (min Q Q')).mul_left _)
  rw [tsum_mul_left] at hsum
  calc
    ∑' k : ℕ, radiusGapEnvelope Q Q' k ≤
        |(Q : ℝ) - (Q' : ℝ)| *
          ∑' k : ℕ, squareGaussianWeight (min Q Q') k := hsum
    _ ≤ (natGap Q Q' : ℝ) * (400 / (min Q Q' : ℝ)) := by
      rw [abs_natCast_sub_eq_natGap]
      gcongr
      simpa using hsquare
    _ ≤ 4000 / (ρ : ℝ) := by
      have hρR : (0 : ℝ) < ρ := by positivity
      have hminR : (ρ : ℝ) ^ 2 ≤ (min Q Q' : ℕ) := by exact_mod_cast hminNat
      have hgapR : (natGap Q Q' : ℝ) ≤ 8 * ρ := by exact_mod_cast hgap
      have hminRpos : (0 : ℝ) < (min Q Q' : ℕ) := by positivity
      have hminR' : (ρ : ℝ) ^ 2 ≤ min (Q : ℝ) (Q' : ℝ) := by
        simpa using hminR
      have hminRpos' : (0 : ℝ) < min (Q : ℝ) (Q' : ℝ) := by
        have hm : (0 : ℝ) < ((min Q Q' : ℕ) : ℝ) := by exact_mod_cast hminPos
        simpa using hm
      apply (le_div_iff₀ hρR).2
      rw [div_eq_mul_inv]
      calc
        (natGap Q Q' : ℝ) * (400 * (min (Q : ℝ) (Q' : ℝ))⁻¹) * ρ ≤
            (8 * ρ) * (400 * (min (Q : ℝ) (Q' : ℝ))⁻¹) * ρ := by gcongr
        _ ≤ 4000 := by
          calc
            (8 * ρ) * (400 * (min (Q : ℝ) (Q' : ℝ))⁻¹) * ρ =
                (3200 * (ρ : ℝ) ^ 2) / min (Q : ℝ) (Q' : ℝ) := by
                  rw [div_eq_mul_inv]
                  ring
            _ ≤ 4000 := by
              rw [div_le_iff₀ hminRpos']
              nlinarith [hminR']

private lemma shifted_tsum_le_tsum {f : ℕ → ℝ} (hf : Summable f)
    (hnonneg : ∀ n, 0 ≤ f n) (K : ℕ) :
    ∑' n : ℕ, f (n + K) ≤ ∑' n : ℕ, f n := by
  rw [← hf.sum_add_tsum_nat_add K]
  exact le_add_of_nonneg_left (Finset.sum_nonneg fun n hn ↦ hnonneg n)

private theorem summable_massDifference (d e d' e' : ℕ) :
    Summable (fun n : ℕ ↦ fourierProductMass n d' e' -
      fourierProductMass n d e) := by
  have h := (summable_fourierProductLoss d e).sub
    (summable_fourierProductLoss d' e')
  apply h.congr
  intro n
  unfold fourierProductLoss
  ring

private theorem fourierPotential_sub_eq_tsum_massDifference
    (d e d' e' : ℕ) :
    fourierPotential d e - fourierPotential d' e' =
      ∑' n : ℕ, (fourierProductMass n d' e' -
        fourierProductMass n d e) := by
  unfold fourierPotential
  rw [← Summable.tsum_sub (summable_fourierProductLoss d e)
    (summable_fourierProductLoss d' e')]
  apply tsum_congr
  intro n
  unfold fourierProductLoss
  ring

/-- **Uniform shell comparison in diagonal coordinates.**  The constant is
deliberately generous; the scale `ρ⁻¹` and the absence of angular dependence
are the important conclusions. -/
theorem abs_fourierPotential_sub_le_of_radiusSq_gap
    {d e d' e' ρ : ℕ} (hρ : 2 ≤ ρ)
    (hdρ : d ≤ 2 * ρ) (heρ : e ≤ 2 * ρ)
    (hdρ' : d' ≤ 2 * ρ) (heρ' : e' ≤ 2 * ρ)
    (hradius : ρ ≤ max d e) (hradius' : ρ ≤ max d' e')
    (hgap : natGap (radiusSq d e) (radiusSq d' e') ≤ 8 * ρ) :
    |fourierPotential d e - fourierPotential d' e'| ≤
      2100000000 / (ρ : ℝ) := by
  let N : ℕ := 64 * ρ
  let K : ℕ := N - 1
  let Q := radiusSq d e
  let Q' := radiusSq d' e'
  have hN : 0 < N := by dsimp [N]; positivity
  have hK : K + 1 = N := by dsimp [K]; omega
  have hQlo : ρ ^ 2 ≤ Q := by
    dsimp [Q]
    unfold radiusSq
    rcases max_cases d e with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_right _ _)
    · rw [h] at hradius
      exact (Nat.pow_le_pow_left hradius 2).trans (Nat.le_add_left _ _)
  have hQlo' : ρ ^ 2 ≤ Q' := by
    dsimp [Q']
    unfold radiusSq
    rcases max_cases d' e' with ⟨h, _⟩ | ⟨h, _⟩
    · rw [h] at hradius'
      exact (Nat.pow_le_pow_left hradius' 2).trans (Nat.le_add_right _ _)
    · rw [h] at hradius'
      exact (Nat.pow_le_pow_left hradius' 2).trans (Nat.le_add_left _ _)
  have hdiff := summable_massDifference d e d' e'
  have habs := hdiff.abs
  rw [fourierPotential_sub_eq_tsum_massDifference]
  have hnorm :
      |∑' n : ℕ, (fourierProductMass n d' e' - fourierProductMass n d e)| ≤
        ∑' n : ℕ, |fourierProductMass n d' e' - fourierProductMass n d e| := by
    simpa only [Real.norm_eq_abs] using norm_tsum_le_tsum_norm hdiff.norm
  refine hnorm.trans ?_
  rw [← habs.sum_add_tsum_nat_add N]
  have hearly :
      ∑ n ∈ Finset.range N,
          |fourierProductMass n d' e' - fourierProductMass n d e| ≤
        2000000000 / (ρ : ℝ) := by
    calc
      _ ≤ ∑ _n ∈ Finset.range N, 25165824 / (ρ : ℝ) ^ 3 := by
        apply Finset.sum_le_sum
        intro n hn
        rw [abs_sub_comm]
        exact abs_fourierProductMass_sub_le_of_radiusSq_eq_early hρ
          hradius hradius' (Finset.mem_range.mp hn)
      _ = (N : ℝ) * (25165824 / (ρ : ℝ) ^ 3) := by simp
      _ ≤ 2000000000 / (ρ : ℝ) := by
        dsimp [N]
        norm_num only [Nat.cast_mul, Nat.cast_ofNat]
        have hρR : (0 : ℝ) < ρ := by positivity
        have hρone : (1 : ℝ) ≤ ρ := by exact_mod_cast (show 1 ≤ ρ by omega)
        field_simp
        nlinarith
  have hlatePoint (n : ℕ) :
      |fourierProductMass (n + N) d' e' - fourierProductMass (n + N) d e| ≤
        localEnvelope Q ρ (n + K) + radiusGapEnvelope Q Q' (n + K) +
          localEnvelope Q' ρ (n + K) := by
    have hm : n + N = (n + K) + 1 := by omega
    rw [abs_sub_comm]
    have h := abs_fourierProductMass_sub_le_late hρ hdρ heρ hdρ' heρ'
      hradius hradius' (show 64 * ρ ≤ n + N by dsimp [N]; omega)
    simpa only [Q, Q', hm, localEnvelope, radiusGapEnvelope,
      Nat.cast_add, Nat.cast_one] using h
  have hlateSummable : Summable (fun n : ℕ ↦
      localEnvelope Q ρ (n + K) + radiusGapEnvelope Q Q' (n + K) +
        localEnvelope Q' ρ (n + K)) :=
    ((((summable_nat_add_iff K).mpr (summable_localEnvelope Q ρ)).add
      ((summable_nat_add_iff K).mpr (summable_radiusGapEnvelope Q Q'))).add
      ((summable_nat_add_iff K).mpr (summable_localEnvelope Q' ρ)))
  have hlate :
      ∑' n : ℕ,
          |fourierProductMass (n + N) d' e' - fourierProductMass (n + N) d e| ≤
        30000 / (ρ : ℝ) := by
    calc
      _ ≤ ∑' n : ℕ,
          (localEnvelope Q ρ (n + K) + radiusGapEnvelope Q Q' (n + K) +
            localEnvelope Q' ρ (n + K)) := by
        exact Summable.tsum_le_tsum hlatePoint
          ((summable_nat_add_iff N).mpr habs) hlateSummable
      _ = (∑' n : ℕ, localEnvelope Q ρ (n + K)) +
          (∑' n : ℕ, radiusGapEnvelope Q Q' (n + K)) +
            ∑' n : ℕ, localEnvelope Q' ρ (n + K) := by
        rw [Summable.tsum_add
          (((summable_nat_add_iff K).mpr (summable_localEnvelope Q ρ)).add
            ((summable_nat_add_iff K).mpr (summable_radiusGapEnvelope Q Q')))
          ((summable_nat_add_iff K).mpr (summable_localEnvelope Q' ρ)),
          Summable.tsum_add
            ((summable_nat_add_iff K).mpr (summable_localEnvelope Q ρ))
            ((summable_nat_add_iff K).mpr (summable_radiusGapEnvelope Q Q'))]
      _ ≤ (∑' n : ℕ, localEnvelope Q ρ n) +
          (∑' n : ℕ, radiusGapEnvelope Q Q' n) +
            ∑' n : ℕ, localEnvelope Q' ρ n := by
        exact add_le_add
          (add_le_add
            (shifted_tsum_le_tsum (summable_localEnvelope Q ρ)
              (localEnvelope_nonneg Q ρ) K)
            (shifted_tsum_le_tsum (summable_radiusGapEnvelope Q Q')
              (radiusGapEnvelope_nonneg Q Q') K))
          (shifted_tsum_le_tsum (summable_localEnvelope Q' ρ)
            (localEnvelope_nonneg Q' ρ) K)
      _ ≤ 10000 / (ρ : ℝ) + 4000 / (ρ : ℝ) + 10000 / (ρ : ℝ) := by
        exact add_le_add (add_le_add (tsum_localEnvelope_le hρ hQlo)
          (tsum_radiusGapEnvelope_le hρ hQlo hQlo' hgap))
          (tsum_localEnvelope_le hρ hQlo')
      _ ≤ 30000 / (ρ : ℝ) := by
        have hρR : (0 : ℝ) < ρ := by positivity
        field_simp
        norm_num
  calc
    (∑ n ∈ Finset.range N,
        |fourierProductMass n d' e' - fourierProductMass n d e|) +
      ∑' n : ℕ,
        |fourierProductMass (n + N) d' e' - fourierProductMass (n + N) d e| ≤
      2000000000 / (ρ : ℝ) + 30000 / (ρ : ℝ) := add_le_add hearly hlate
    _ ≤ 2100000000 / (ρ : ℝ) := by
      have hρR : (0 : ℝ) < ρ := by positivity
      field_simp
      norm_num

end PotentialRadialShell
end Erdos1165
