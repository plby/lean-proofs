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
import ErdosProblems.Erdos722.NibbleConcrete
import Mathlib

/-!
# Asymptotic estimates for the concrete nibble

This file keeps all fractional exponents in the one integer scale `T` from
`NibbleConcrete`.  Its first estimates show that the initial reciprocal
profile error dominates both the boost rounding error and every fixed
multiple of the design-hypergraph codegree.
-/

namespace Erdos722.NibbleAsymptotic

open Filter Finset
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.BinomialBounds
open Erdos722.Boost
open Erdos722.BoostAsymptotic
open Erdos722.NibbleConcrete

noncomputable section

lemma K_ge_three (hr : 1 < r) (hrq : r < q) : 3 ≤ K q r := by
  calc
    3 ≤ r + 1 := by omega
    _ = Nat.choose (r + 1) r := (Nat.choose_succ_self_right r).symm
    _ ≤ Nat.choose q r := Nat.choose_le_choose r (by omega)

lemma K_pos (hrq : r ≤ q) : 0 < K q r := Nat.choose_pos hrq

lemma den_pos (hrq : r ≤ q) : 0 < den q r := by
  unfold den K
  exact pow_pos (mul_pos (by norm_num) (Nat.choose_pos hrq)) _

lemma scale_tendsto (hrq : r ≤ q) :
    Tendsto (fun n ↦ scale n q r) atTop atTop := by
  have hbase : Tendsto
      (rationalPowerThreshold (3 * K q r) (den q r)) atTop atTop :=
    rationalPowerThreshold_tendsto_atTop
      (mul_pos (by norm_num) (K_pos hrq)) (den_pos hrq)
  refine tendsto_atTop_mono' atTop (Eventually.of_forall ?_) hbase
  intro n
  exact Nat.le_mul_of_pos_left _ (by norm_num [scaleMultiplier])

lemma scale_cast_le_rpow (n q r : ℕ) :
    (scale n q r : ℝ) ≤
      scaleMultiplier *
        (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r) := by
  unfold scale
  push_cast
  exact mul_le_mul_of_nonneg_left
    (by simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      rationalPowerThreshold_cast_le (3 * K q r) (den q r) n) (by positivity)

lemma profile_scale_exponent_lt
    (hrq : r ≤ q) :
    (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1) < 4 / 9 := by
  have hK : 0 < K q r := K_pos hrq
  have hden : (den q r : ℝ) = 36 * (K q r : ℝ) ^ 2 := by
    unfold den
    push_cast
    ring
  rw [hden]
  have hKR : (0 : ℝ) < K q r := by exact_mod_cast hK
  have heq : ((3 * K q r : ℕ) : ℝ) /
        (36 * (K q r : ℝ) ^ 2) * (5 * K q r - 1) =
      5 / 12 - 1 / (12 * (K q r : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [heq]
  have : (0 : ℝ) < 1 / (12 * (K q r : ℝ)) := by positivity
  nlinarith

lemma boost_profile_exponent_lt
    (hrq : r < q) :
    boostErrorExponent q r +
        (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1) <
      (q - r : ℕ) := by
  have hK : 0 < K q r := K_pos hrq.le
  have hscale := profile_scale_exponent_lt hrq.le
  have hb : boostErrorExponent q r = (q - r : ℕ) - 4 / 9 := by
    unfold boostErrorExponent boostErrorNumerator
    rw [Nat.cast_sub (by omega : 4 ≤ 9 * (q - r))]
    push_cast
    ring
  rw [hb]
  linarith

/-- The boost's absolute rounding error is at most one quarter of the
initial edge-profile error. -/
theorem eventually_boostError_le_initial_error (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (boostError n q r : ℝ) ≤
        centerDegree n q r /
          (scale n q r : ℝ) ^ (5 * K q r - 1) / 4 := by
  let a := boostErrorExponent q r +
    (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)
  let M : ℝ := (scaleMultiplier : ℝ) ^ (5 * K q r - 1)
  have ha : a < (q - r : ℕ) := boost_profile_exponent_lt hrq
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := a) (b := (q - r : ℕ))
    (C := 8 * M * 2 ^ (q - r) * (q - r).factorial) ha (by positivity)
  have hnlarge := eventually_ge_atTop (2 * q)
  have hscalePos := (scale_tendsto hrq.le).eventually (eventually_ge_atTop 1)
  filter_upwards [hdom, hnlarge, hscalePos] with n hdom hn hT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTnonneg : (0 : ℝ) ≤ scale n q r := by positivity
  have hTpow := pow_le_pow_left₀ hTnonneg (scale_cast_le_rpow n q r)
    (5 * K q r - 1)
  have hTpow' : ((scale n q r : ℝ) ^ (5 * K q r - 1)) ≤
      M * (n : ℝ) ^
        ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) := by
    calc
      _ ≤ ((scaleMultiplier : ℝ) *
          (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
          (5 * K q r - 1) := hTpow
      _ = (scaleMultiplier : ℝ) ^ (5 * K q r - 1) *
          ((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
            (5 * K q r - 1) := by rw [mul_pow]
      _ = _ := by
        dsimp [M]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_mul (Nat.cast_nonneg n)]
        congr 1
        rw [Nat.cast_sub (by
          have := K_pos hrq.le
          omega : 1 ≤ 5 * K q r)]
        push_cast
        rfl
  have hboost : (boostError n q r : ℝ) ≤
      (n : ℝ) ^ boostErrorExponent q r :=
    rationalPowerThreshold_cast_le _ _ _
  have hprod : 8 * (scale n q r : ℝ) ^ (5 * K q r - 1) *
      boostError n q r ≤
        8 * M * (n : ℝ) ^ a := by
    calc
      _ = 8 * ((scale n q r : ℝ) ^ (5 * K q r - 1) *
          boostError n q r) := by ring
      _ ≤ 8 * ((M * (n : ℝ) ^
            ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1))) *
          (n : ℝ) ^ boostErrorExponent q r) := by gcongr
      _ = 8 * M * ((n : ℝ) ^
          ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) *
            (n : ℝ) ^ boostErrorExponent q r) := by ring
      _ = 8 * M * (n : ℝ) ^
          (((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) +
            boostErrorExponent q r) := by rw [Real.rpow_add hnpos]
      _ = 8 * M * (n : ℝ) ^ a := by
        congr 2
        dsimp [a]
        ring
  have hchooseLower := half_pow_div_factorial_le_choose_sub n r (q - r)
    (by omega)
  have htoChoose : 8 * M * (n : ℝ) ^ a ≤
      Nat.choose (n - r) (q - r) := by
    apply hchooseLower.trans'
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (q - r).factorial)).2
    calc
      8 * M * (n : ℝ) ^ a * (q - r).factorial ≤
          (n : ℝ) ^ (q - r) / 2 ^ (q - r) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (q - r))).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hdom
      _ = ((n : ℝ) / 2) ^ (q - r) := by rw [div_pow]
  have hmain : 8 * (scale n q r : ℝ) ^ (5 * K q r - 1) *
      boostError n q r ≤ Nat.choose (n - r) (q - r) :=
    hprod.trans htoChoose
  have hTreal : (0 : ℝ) < scale n q r := by exact_mod_cast hT
  unfold centerDegree extensionScale
  rw [div_div]
  apply (le_div_iff₀ (by positivity : (0 : ℝ) <
    (scale n q r : ℝ) ^ (5 * K q r - 1) * 4)).2
  calc
    (boostError n q r : ℝ) *
        ((scale n q r : ℝ) ^ (5 * K q r - 1) * 4) ≤
      (Nat.choose (n - r) (q - r) : ℝ) / 2 := by
        nlinarith
    _ = _ := by ring

lemma codegree_profile_exponent_lt (hrq : r < q) :
    ((q - r - 1 : ℕ) : ℝ) +
        (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1) <
      (q - r : ℕ) := by
  have hs : 1 ≤ q - r := by omega
  have hscale := profile_scale_exponent_lt (r := r) (q := q) hrq.le
  have hscaleOne :
      (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1) < 1 :=
    hscale.trans (by norm_num)
  calc
    ((q - r - 1 : ℕ) : ℝ) +
        (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1) <
      ((q - r - 1 : ℕ) : ℝ) + 1 :=
        by simpa [add_comm] using
          add_lt_add_left hscaleOne ((q - r - 1 : ℕ) : ℝ)
    _ = (q - r : ℕ) := by
      rw [Nat.cast_sub hs]
      push_cast
      ring

/-- Every fixed multiple of the auxiliary-hypergraph codegree is eventually
absorbed by the initial edge-profile error. -/
theorem eventually_const_codegree_le_initial_error
    (hrq : r < q) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop,
      C₀ * (n : ℝ) ^ (q - r - 1) ≤
        centerDegree n q r /
          (scale n q r : ℝ) ^ (5 * K q r - 1) := by
  let a := ((q - r - 1 : ℕ) : ℝ) +
    (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)
  let M : ℝ := (scaleMultiplier : ℝ) ^ (5 * K q r - 1)
  have ha : a < (q - r : ℕ) := codegree_profile_exponent_lt hrq
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := a) (b := (q - r : ℕ))
    (C := 2 * C₀ * M * 2 ^ (q - r) * (q - r).factorial) ha (by positivity)
  have hnlarge := eventually_ge_atTop (2 * q)
  have hscalePos := (scale_tendsto hrq.le).eventually (eventually_ge_atTop 1)
  filter_upwards [hdom, hnlarge, hscalePos] with n hdom hn hT
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTpow := pow_le_pow_left₀ (Nat.cast_nonneg (scale n q r))
    (scale_cast_le_rpow n q r) (5 * K q r - 1)
  have hPcast : ((5 * K q r - 1 : ℕ) : ℝ) =
      5 * (K q r : ℝ) - 1 := by
    rw [Nat.cast_sub (by
      have := K_pos hrq.le
      omega : 1 ≤ 5 * K q r)]
    push_cast
    rfl
  have hTpow' : ((scale n q r : ℝ) ^ (5 * K q r - 1)) ≤
      M * (n : ℝ) ^
        ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) := by
    calc
      _ ≤ ((scaleMultiplier : ℝ) *
          (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
          (5 * K q r - 1) := hTpow
      _ = (scaleMultiplier : ℝ) ^ (5 * K q r - 1) *
          ((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
            (5 * K q r - 1) := by rw [mul_pow]
      _ = _ := by
        dsimp [M]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_mul (Nat.cast_nonneg n), hPcast]
  have hprod : 2 * C₀ * (scale n q r : ℝ) ^ (5 * K q r - 1) *
      (n : ℝ) ^ (q - r - 1) ≤ 2 * C₀ * M * (n : ℝ) ^ a := by
    calc
      _ = (2 * C₀) * ((scale n q r : ℝ) ^ (5 * K q r - 1) *
          (n : ℝ) ^ (q - r - 1)) := by ring
      _ ≤ (2 * C₀) *
          (M * (n : ℝ) ^
              ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) *
            (n : ℝ) ^ (q - r - 1)) := by
        apply mul_le_mul_of_nonneg_left _ (by positivity)
        exact mul_le_mul_of_nonneg_right hTpow' (by positivity)
      _ = 2 * C₀ * M * (n : ℝ) ^ a := by
        rw [← Real.rpow_natCast]
        calc
          2 * C₀ * (M * (n : ℝ) ^
                ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) *
              (n : ℝ) ^ ((q - r - 1 : ℕ) : ℝ)) =
              2 * C₀ * M * ((n : ℝ) ^
                ((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) *
              (n : ℝ) ^ ((q - r - 1 : ℕ) : ℝ)) := by ring
          _ = 2 * C₀ * M * (n : ℝ) ^
              (((((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)) +
                ((q - r - 1 : ℕ) : ℝ)) := by rw [Real.rpow_add hnpos]
          _ = _ := by
            dsimp [a]
            congr 2
            ring
  have hchooseLower := half_pow_div_factorial_le_choose_sub n r (q - r)
    (by omega)
  have htoChoose : 2 * C₀ * M * (n : ℝ) ^ a ≤
      Nat.choose (n - r) (q - r) := by
    apply hchooseLower.trans'
    apply (le_div_iff₀ (by positivity : (0 : ℝ) < (q - r).factorial)).2
    calc
      2 * C₀ * M * (n : ℝ) ^ a * (q - r).factorial ≤
          (n : ℝ) ^ (q - r) / 2 ^ (q - r) := by
        apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ (q - r))).2
        simpa [mul_assoc, mul_left_comm, mul_comm] using hdom
      _ = ((n : ℝ) / 2) ^ (q - r) := by rw [div_pow]
  have hmain := hprod.trans htoChoose
  have hTreal : (0 : ℝ) < scale n q r := by exact_mod_cast hT
  unfold centerDegree extensionScale
  rw [div_div]
  apply (le_div_iff₀ (mul_pos (by norm_num) (pow_pos hTreal _))).2
  convert hmain using 1 <;> ring

/-- The profile-scale power is negligible compared with the number of
`r`-edges in every host containing more than half of the complete graph. -/
theorem eventually_const_scaleProfile_le_host
    (hr : 0 < r) (hrq : r ≤ q) (C₀ : ℝ) (hC₀ : 0 ≤ C₀) :
    ∀ᶠ n : ℕ in atTop, ∀ g : ℕ,
      Nat.choose n r / 2 < g →
      C₀ * (scale n q r : ℝ) ^ (5 * K q r - 1) ≤ g := by
  let a := (((3 * K q r : ℕ) : ℝ) / den q r) * (5 * K q r - 1)
  let M : ℝ := (scaleMultiplier : ℝ) ^ (5 * K q r - 1)
  have ha49 : a < 4 / 9 := profile_scale_exponent_lt hrq
  have har : a < (r : ℝ) := by
    have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hr
    have : (4 / 9 : ℝ) < r := by linarith
    linarith
  have hdom := eventually_const_mul_rpow_le_rpow
    (a := a) (b := (r : ℝ))
    (C := 2 * C₀ * M * 2 ^ r * r.factorial) har (by positivity)
  have hnlarge := eventually_ge_atTop (2 * r)
  filter_upwards [hdom, hnlarge] with n hdom hn
  intro g hg
  have hnpos : (0 : ℝ) < n := by exact_mod_cast (by omega : 0 < n)
  have hTpow := pow_le_pow_left₀ (Nat.cast_nonneg (scale n q r))
    (scale_cast_le_rpow n q r) (5 * K q r - 1)
  have hPcast : ((5 * K q r - 1 : ℕ) : ℝ) =
      5 * (K q r : ℝ) - 1 := by
    rw [Nat.cast_sub (by
      have := K_pos hrq
      omega : 1 ≤ 5 * K q r)]
    push_cast
    rfl
  have hTpow' : ((scale n q r : ℝ) ^ (5 * K q r - 1)) ≤
      M * (n : ℝ) ^ a := by
    calc
      _ ≤ ((scaleMultiplier : ℝ) *
          (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
          (5 * K q r - 1) := hTpow
      _ = (scaleMultiplier : ℝ) ^ (5 * K q r - 1) *
          ((n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r)) ^
            (5 * K q r - 1) := by rw [mul_pow]
      _ = _ := by
        dsimp [M]
        congr 1
        rw [← Real.rpow_natCast, Real.rpow_mul (Nat.cast_nonneg n), hPcast]
  have hprod : 2 * C₀ * (scale n q r : ℝ) ^ (5 * K q r - 1) ≤
      2 * C₀ * M * (n : ℝ) ^ a := by
    calc
      _ ≤ 2 * C₀ * (M * (n : ℝ) ^ a) := by gcongr
      _ = _ := by ring
  have hchooseLower := half_pow_div_factorial_le_choose_sub n 0 r (by omega)
  have htoChoose : 2 * C₀ * M * (n : ℝ) ^ a ≤ Nat.choose n r := by
    have hbase : 2 * C₀ * M * (n : ℝ) ^ a ≤
        ((n : ℝ) / 2) ^ r / r.factorial := by
      apply (le_div_iff₀ (by positivity : (0 : ℝ) < r.factorial)).2
      calc
        2 * C₀ * M * (n : ℝ) ^ a * r.factorial ≤
            (n : ℝ) ^ r / 2 ^ r := by
          apply (le_div_iff₀ (by positivity : (0 : ℝ) < 2 ^ r)).2
          simpa [mul_assoc, mul_left_comm, mul_comm] using hdom
        _ = ((n : ℝ) / 2) ^ r := by rw [div_pow]
    exact hbase.trans (by simpa using hchooseLower)
  have hgNat : Nat.choose n r ≤ 2 * g := by omega
  have hgReal : (Nat.choose n r : ℝ) / 2 ≤ g := by
    have : (Nat.choose n r : ℝ) ≤ 2 * g := by exact_mod_cast hgNat
    linarith
  calc
    C₀ * (scale n q r : ℝ) ^ (5 * K q r - 1) ≤
        (Nat.choose n r : ℝ) / 2 := by linarith [hprod.trans htoChoose]
    _ ≤ (g : ℝ) := hgReal

/-- The ambient edge-extension scale eventually dominates the `K`-th
power of the integer profile scale.  This is the uniform source of all
floor/ceiling margins in the finite nibble. -/
theorem eventually_scale_pow_K_le_centerDegree (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop,
      (scale n q r : ℝ) ^ K q r ≤ centerDegree n q r := by
  have herr := eventually_const_codegree_le_initial_error hrq 1 (by norm_num)
  have hT := (scale_tendsto hrq.le).eventually (eventually_ge_atTop 1)
  filter_upwards [herr, hT, eventually_ge_atTop 1] with n herr hT hn
  have hnPow : (1 : ℝ) ≤ (n : ℝ) ^ (q - r - 1) := by
    exact one_le_pow₀ (by exact_mod_cast hn)
  have hdiv : (1 : ℝ) ≤ centerDegree n q r /
      (scale n q r : ℝ) ^ (5 * K q r - 1) := by
    have herr' : (n : ℝ) ^ (q - r - 1) ≤ centerDegree n q r /
        (scale n q r : ℝ) ^ (5 * K q r - 1) := by simpa using herr
    exact hnPow.trans herr'
  have hTreal : (1 : ℝ) ≤ scale n q r := by exact_mod_cast hT
  have hpowPos : 0 < (scale n q r : ℝ) ^ (5 * K q r - 1) := by positivity
  have hlarge : (scale n q r : ℝ) ^ (5 * K q r - 1) ≤
      centerDegree n q r := by
    simpa using (le_div_iff₀ hpowPos).mp hdiv
  have hexp : K q r ≤ 5 * K q r - 1 := by
    have hK := K_pos hrq.le
    omega
  exact (pow_le_pow_right₀ hTreal hexp).trans hlarge

end

end Erdos722.NibbleAsymptotic
