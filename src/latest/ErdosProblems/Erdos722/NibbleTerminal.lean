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
import ErdosProblems.Erdos722.NibbleAsymptotic
import ErdosProblems.Erdos722.CoverAsymptotic
import Mathlib

/-!
# Terminal estimate for the clique-removal process

The fixed multiplier in the integer nibble scale makes the coefficient in
the terminal lower-face estimate strictly smaller than the coefficient-one
power threshold required by the sparse cover.
-/

namespace Erdos722.NibbleTerminal

open Filter Finset
open scoped Topology Real
open Erdos722.Asymptotics
open Erdos722.NibbleProfiles
open Erdos722.NibbleConcrete
open Erdos722.NibbleAsymptotic
open Erdos722.CoverAsymptotic

noncomputable section

/-- At the prescribed stopping time, the weighted face cap is bounded by
the exact natural power threshold consumed by `HasBoundedNibble`. -/
theorem eventually_faceCap_terminal_le_coverLeaveCap
    (hr : 1 < r) (hrq : r < q) :
    ∀ᶠ n : ℕ in atTop, ∀ g : ℕ,
      Nat.choose n r / 2 < g →
      stopTarget g n q r ≤ g →
      faceCap n (faceSlack n q r) (faceEps n q r)
          g (K q r) (depth g n q r) ≤
        faceWeight g (K q r) (depth g n q r) *
          coverLeaveCap q r n := by
  let a : ℝ := ((3 * K q r : ℕ) : ℝ) / den q r
  let δ : ℝ := coverLeaveExponent q r
  let C : ℝ := 2 * K q r + 1
  have ha : 0 < a := by
    dsimp [a]
    exact div_pos (by exact_mod_cast
      (mul_pos (by norm_num : 0 < 3) (K_pos hrq.le)))
      (by exact_mod_cast den_pos hrq.le)
  have hδ : δ = 1 - a := by
    have hids := cover_exponent_identities (by omega : 0 < r) hrq
    have h := hids.2.1
    dsimp [δ, a, coverLeaveExponent] at h ⊢
    simpa [coverDen, coverK, den, K] using h
  have hscaleLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ (((3 * K q r : ℕ) : ℝ) / den q r) / 2 ≤
        (rationalPowerThreshold (3 * K q r) (den q r) n : ℝ) :=
    eventually_half_rpow_le_rationalPowerThreshold
      (mul_pos (by norm_num) (K_pos hrq.le)) (den_pos hrq.le)
  have hcapLower : ∀ᶠ n : ℕ in atTop,
      (n : ℝ) ^ ((coverLeaveNumerator q r : ℝ) / coverDen q r) / 2 ≤
        (coverLeaveCap q r n : ℝ) := by
    simpa [coverLeaveCap] using
      (eventually_half_rpow_le_rationalPowerThreshold
        (coverLeaveNumerator_pos (by omega : 0 < r) hrq)
        (coverDen_pos hrq.le))
  have hhostLarge := eventually_const_scaleProfile_le_host
    (by omega : 0 < r) hrq.le (2 * C) (by positivity)
  have hTlarge := (scale_tendsto hrq.le).eventually (eventually_ge_atTop 4)
  filter_upwards [hscaleLower, hcapLower, hhostLarge, hTlarge,
      eventually_ge_atTop 1] with n hscaleLower hcapLower hhostLarge hT hn
  intro g hg htarget
  let T : ℝ := scale n q r
  let x : ℝ := (n : ℝ) ^ a
  let y : ℝ := (n : ℝ) ^ δ
  let d : ℝ := density g (K q r) (depth g n q r)
  have hnR : (0 : ℝ) < n := by exact_mod_cast hn
  have hTR : 0 < T := by
    dsimp [T]
    exact_mod_cast (show 0 < scale n q r by omega)
  have hx : 0 < x := by dsimp [x]; positivity
  have hy : 0 < y := by dsimp [y]; positivity
  have hgpos : 0 < g := by omega
  have hKpos : 0 < K q r := K_pos hrq.le
  have hmulDepth : K q r * depth g n q r ≤ g := by
    dsimp [depth]
    exact (Nat.mul_div_le _ _).trans (Nat.sub_le _ _)
  have htargetPos : 0 < stopTarget g n q r := by
    dsimp [stopTarget]
    omega
  have hmulDepthLt : K q r * depth g n q r < g := by
    calc
      K q r * depth g n q r ≤ g - stopTarget g n q r := by
        dsimp [depth]
        exact Nat.mul_div_le _ _
      _ < g := Nat.sub_lt hgpos htargetPos
  have hdpos : 0 < d := by
    dsimp [d]
    exact density_pos hgpos hmulDepthLt
  have hdle : d ≤ 1 := by
    dsimp [d]
    exact density_le_one_of_mul_le hgpos hmulDepth
  have hscaleBase : x / 2 ≤
      (rationalPowerThreshold (3 * K q r) (den q r) n : ℝ) := by
    simpa [x, a] using hscaleLower
  have hTx : 32 * x ≤ T := by
    dsimp [T, scale, scaleMultiplier]
    push_cast
    nlinarith
  have hprofileHost : 2 * C * T ≤ g := by
    have hraw := hhostLarge g hg
    have hTP : T ≤ T ^ (5 * K q r - 1) := by
      calc
        T = T ^ 1 := by simp
        _ ≤ T ^ (5 * K q r - 1) := by
          apply pow_le_pow_right₀
          · dsimp [T]
            exact_mod_cast (show 1 ≤ scale n q r by omega)
          · have hK := K_pos hrq.le
            omega
    have hscaled : 2 * C * T ≤
        2 * C * T ^ (5 * K q r - 1) := by gcongr
    exact hscaled.trans (by simpa [T, C] using hraw)
  have hCg : C / g ≤ 1 / (2 * T) := by
    have hgR : (0 : ℝ) < g := by exact_mod_cast hgpos
    have htwoT : 0 < 2 * T := by positivity
    calc
      C / (g : ℝ) ≤ C / (2 * C * T) := by
        apply div_le_div_of_nonneg_left (by dsimp [C]; positivity)
          (by positivity)
        simpa using hprofileHost
      _ = 1 / (2 * T) := by
        have hCpos : 0 < C := by dsimp [C]; positivity
        field_simp
  have hdUpperRaw := density_depth_lt hgpos hKpos
    (show 0 < scale n q r by omega) htarget
  have hdUpper : d ≤ 3 / (2 * T) := by
    have hCcast : (((2 * K q r + 1 : ℕ) : ℝ)) = C := by
      dsimp [C]
      push_cast
      ring
    have hone : 1 / T + C / g ≤ 3 / (2 * T) := by
      calc
        1 / T + C / (g : ℝ) ≤ 1 / T + 1 / (2 * T) := by gcongr
        _ = 3 / (2 * T) := by field_simp; norm_num
    exact (le_of_lt (by simpa [d, T, hCcast] using hdUpperRaw)).trans hone
  have hslack : faceSlack n q r ≤ n := by
    dsimp [faceSlack, T]
    have hTone : (1 : ℝ) ≤ T ^ 2 := by
      have : (1 : ℝ) ≤ T := by
        dsimp [T]
        exact_mod_cast (show 1 ≤ scale n q r by omega)
      nlinarith [sq_nonneg (T - 1)]
    exact div_le_self (Nat.cast_nonneg n) hTone
  have honeMinus : 0 ≤ 1 - d := sub_nonneg.mpr hdle
  have hratio :
      faceCap n (faceSlack n q r) (faceEps n q r)
          g (K q r) (depth g n q r) /
          faceWeight g (K q r) (depth g n q r) ≤
        11 * (n : ℝ) / T := by
    rw [faceCap_div_weight hgpos
      hmulDepthLt]
    calc
      ((n : ℝ) + faceSlack n q r) * d +
          (n : ℝ) * faceEps n q r * (1 - d) ≤
        (2 * n) * (3 / (2 * T)) +
          (n : ℝ) * (8 / T) := by
            apply add_le_add
            · gcongr
              linarith
            · dsimp [faceEps]
              change (n : ℝ) * (8 / T) * (1 - d) ≤
                (n : ℝ) * (8 / T)
              have hfac : (8 / T) * (1 - d) ≤ 8 / T := by
                have hOneMinus : 1 - d ≤ 1 := by linarith [hdpos]
                simpa using mul_le_mul_of_nonneg_left hOneMinus
                  (div_nonneg (by norm_num : (0 : ℝ) ≤ 8) hTR.le)
              simpa [mul_assoc] using
                mul_le_mul_of_nonneg_left hfac (Nat.cast_nonneg n)
      _ = 11 * (n : ℝ) / T := by field_simp; ring
  have hxy : x * y = n := by
    dsimp [x, y]
    rw [hδ, ← Real.rpow_add hnR]
    norm_num
  have hterminalReal : 11 * (n : ℝ) / T ≤ y / 2 := by
    apply (div_le_iff₀ hTR).2
    calc
      11 * (n : ℝ) ≤ 16 * (n : ℝ) := by nlinarith
      _ = 16 * (x * y) := by rw [hxy]
      _ = (y / 2) * (32 * x) := by ring
      _ ≤ (y / 2) * T := by gcongr
  have hB : y / 2 ≤ (coverLeaveCap q r n : ℝ) := by
    simpa [y, δ, coverLeaveCap, coverLeaveExponent] using hcapLower
  have hweightPos : 0 < faceWeight g (K q r) (depth g n q r) :=
    faceWeight_pos hgpos hmulDepthLt
  have hfinal := (div_le_iff₀ hweightPos).mp
    (hratio.trans (hterminalReal.trans hB))
  simpa [mul_comm] using hfinal

end

end Erdos722.NibbleTerminal
