/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.DyadicDetectorShell

/-!
# Optimizing the additive blocks in a dyadic detector shell

For a shell of length `A`, and a height `T`, we take blocks of integral
length `A / (T + 1)`.  The elementary estimates in this file make the two
terms in the hybrid large sieve simultaneously bounded and remove the
otherwise fatal exponential Taylor loss.
-/

namespace Erdos48

open Complex
open scoped BigOperators

noncomputable section

/-- The integral block length used at height `T` on a shell of length `A`. -/
def optimizedDetectorBlockLength (A T : ℕ) : ℕ := A / (T + 1)

theorem optimizedDetectorBlockLength_pos {A T : ℕ} (hAT : T + 1 ≤ A) :
    0 < optimizedDetectorBlockLength A T := by
  rw [optimizedDetectorBlockLength]
  exact Nat.div_pos hAT (by omega)

theorem optimizedDetectorBlockLength_le {A T : ℕ} :
    optimizedDetectorBlockLength A T ≤ A := by
  rw [optimizedDetectorBlockLength]
  exact Nat.div_le_self A (T + 1)

theorem optimizedDetectorBlockLength_mul_le {A T : ℕ} :
    optimizedDetectorBlockLength A T * (T + 1) ≤ A := by
  rw [optimizedDetectorBlockLength]
  exact Nat.div_mul_le_self A (T + 1)

theorem optimizedDetectorBlockLength_half_lower {A T : ℕ}
    (hAT : T + 1 ≤ A) :
    (A : ℝ) < 2 * (optimizedDetectorBlockLength A T : ℝ) * (T + 1 : ℕ) := by
  let H := optimizedDetectorBlockLength A T
  let D := T + 1
  have hD : 0 < D := by dsimp [D]; omega
  have hH : 0 < H := optimizedDetectorBlockLength_pos hAT
  have hquot : A / D < H + 1 := by
    dsimp [H, D, optimizedDetectorBlockLength]
    omega
  have hA : A < (H + 1) * D :=
    (Nat.div_lt_iff_lt_mul hD).mp hquot
  have hHtwo : H + 1 ≤ 2 * H := by omega
  have hnat : A < 2 * H * D := by
    exact hA.trans_le (Nat.mul_le_mul_right D hHtwo)
  exact_mod_cast hnat

/-- On a shell long enough for the height and conductor, the optimized
hybrid estimate has only a polynomial loss and a factor `A ^ (-2*eta)`. -/
theorem intervalIntegral_optimizedDetectorShell_le
    (Q Y N a T k : ℕ) (hY : 1 ≤ Y)
    (hheight : T + 1 ≤ 2 ^ a) (hconductor : Q ^ 2 ≤ 2 ^ a)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q
          (detectorDyadicShell Y N a)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      (2 * Real.exp 2 * (1 + 8 * Real.pi)) * (T + 1 : ℕ) *
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
          (2 ^ a : ℕ) ^ (-(2 * eta)) := by
  let A : ℕ := 2 ^ a
  let D : ℕ := T + 1
  let H : ℕ := optimizedDetectorBlockLength A T
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; omega
  have hH : 0 < H := by
    dsimp [H, A]
    exact optimizedDetectorBlockLength_pos hheight
  have hHA : H ≤ A := optimizedDetectorBlockLength_le
  have hHD : H * D ≤ A := by
    simpa only [H, D] using
      (optimizedDetectorBlockLength_mul_le (A := A) (T := T))
  have hAhalf : (A : ℝ) < 2 * (H : ℝ) * D := by
    simpa only [H, D] using
      (optimizedDetectorBlockLength_half_lower (A := A) (T := T)
        (by simpa only [A] using hheight))
  have hTaylor :
      ((T : ℝ) * ((H : ℝ) / (A : ℝ))) ^ 2 ≤ 1 := by
    have hTD : T ≤ D := by dsimp [D]; omega
    have hnum : (T : ℝ) * H ≤ A := by
      calc
        (T : ℝ) * H ≤ (D : ℝ) * H := by exact_mod_cast Nat.mul_le_mul_right H hTD
        _ = (H * D : ℕ) := by push_cast; ring
        _ ≤ A := by exact_mod_cast hHD
    have hratio : (T : ℝ) * ((H : ℝ) / A) ≤ 1 := by
      calc
        (T : ℝ) * ((H : ℝ) / A) = ((T : ℝ) * H) / A := by ring
        _ ≤ 1 := (div_le_one (by exact_mod_cast hA)).2 hnum
    have hratio0 : 0 ≤ (T : ℝ) * ((H : ℝ) / A) := by positivity
    nlinarith
  have hExp :
      Real.exp (((T : ℝ) * ((H : ℝ) / (A : ℝ))) ^ 2) ≤ Real.exp 1 :=
    Real.exp_le_exp.mpr hTaylor
  have hInverse : (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤ 4 * D := by
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
    rw [inv_div]
    apply (div_le_iff₀ hHreal).2
    norm_cast at hAhalf ⊢
    nlinarith
  have hFrequency :
      (T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤
        (1 + 8 * Real.pi) * D := by
    have hTleD : (T : ℝ) ≤ D := by exact_mod_cast (show T ≤ D by dsimp [D]; omega)
    have hpi : 0 ≤ Real.pi := Real.pi_pos.le
    calc
      (T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤
          (D : ℝ) + 2 * Real.pi * (4 * D) := by gcongr
      _ = (1 + 8 * Real.pi) * D := by ring
  have hSize : (H : ℝ) + (Q : ℝ) ^ 2 ≤ 2 * A := by
    have hHcast : (H : ℝ) ≤ A := by exact_mod_cast hHA
    have hQcast : (Q : ℝ) ^ 2 ≤ A := by exact_mod_cast hconductor
    linarith
  have hEnergy := sum_detectorDyadicShell_weighted_energy_le
    Y N a k hY eta heta
  have hRaw := intervalIntegral_primitiveNegativeDirichletMass_shell_le
    Q Y N a H hY hH
      (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ))
      (T := (T : ℝ)) (by positivity)
  have hlog0 :
      0 ≤ (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) := by positivity
  have hrpow0 : 0 ≤ (A : ℝ) ^ (-(1 + 2 * eta)) := by positivity
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q
          (detectorDyadicShell Y N a)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
        Real.exp 1 *
          Real.exp (((T : ℝ) * ((H : ℝ) / A)) ^ 2) *
          ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by
      simpa only [A] using hRaw
    _ ≤ Real.exp 1 * Real.exp 1 *
          ((1 + 8 * Real.pi) * D) * (2 * A) *
          (((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
            (A : ℝ) ^ (-(1 + 2 * eta))) := by
      gcongr
    _ = (2 * Real.exp 2 * (1 + 8 * Real.pi)) * (T + 1 : ℕ) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (A : ℝ) ^ (-(2 * eta)) := by
      have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
      rw [← Real.exp_add]
      have hrpow : (A : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) =
          (A : ℝ) ^ (-(2 * eta)) := by
        calc
          (A : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) =
              (A : ℝ) ^ (1 : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) := by
                rw [Real.rpow_one]
          _ = (A : ℝ) ^ ((1 : ℝ) + -(1 + 2 * eta)) := by
                rw [Real.rpow_add hAreal]
          _ = (A : ℝ) ^ (-(2 * eta)) := by congr 1 <;> ring
      rw [show (1 : ℝ) + 1 = 2 by norm_num]
      rw [← hrpow]
      dsimp [D]
      push_cast
      ring
    _ = _ := by rfl

/-- The sharp hybrid form of the optimized shell estimate.  If the shell
length dominates `2 * (T+1) * Q^2`, the frequency factor and the character
large-sieve factor cancel the `A⁻¹` in the coefficient energy.  In
particular there is no residual linear factor in the height. -/
theorem intervalIntegral_optimizedDetectorShell_hybrid_le
    (Q Y N a T k : ℕ) (hY : 1 ≤ Y) (hQ : 1 ≤ Q)
    (hhybrid : (T + 1) * Q ^ 2 ≤ 2 ^ a)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q
          (detectorDyadicShell Y N a)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
        (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
          (2 ^ a : ℕ) ^ (-(2 * eta)) := by
  let A : ℕ := 2 ^ a
  let D : ℕ := T + 1
  let H : ℕ := optimizedDetectorBlockLength A T
  have hA : 0 < A := by dsimp [A]; positivity
  have hD : 0 < D := by dsimp [D]; omega
  have hheight : D ≤ A := by
    have hQsq : 1 ≤ Q ^ 2 := by
      simpa only [pow_two, one_mul] using Nat.mul_le_mul hQ hQ
    have htwoD : D ≤ D * Q ^ 2 := by
      calc
        D = D * 1 := by omega
        _ ≤ D * Q ^ 2 := Nat.mul_le_mul_left D hQsq
    simpa only [A, D] using htwoD.trans hhybrid
  have hH : 0 < H := by
    dsimp [H, A, D]
    exact optimizedDetectorBlockLength_pos hheight
  have hHD : H * D ≤ A := by
    simpa only [H, D] using
      (optimizedDetectorBlockLength_mul_le (A := A) (T := T))
  have hAhalf : (A : ℝ) < 2 * (H : ℝ) * D := by
    simpa only [H, D] using
      (optimizedDetectorBlockLength_half_lower (A := A) (T := T) hheight)
  have hTaylor :
      ((T : ℝ) * ((H : ℝ) / (A : ℝ))) ^ 2 ≤ 1 := by
    have hTD : T ≤ D := by dsimp [D]; omega
    have hnum : (T : ℝ) * H ≤ A := by
      calc
        (T : ℝ) * H ≤ (D : ℝ) * H := by
          exact_mod_cast Nat.mul_le_mul_right H hTD
        _ = (H * D : ℕ) := by push_cast; ring
        _ ≤ A := by exact_mod_cast hHD
    have hratio : (T : ℝ) * ((H : ℝ) / A) ≤ 1 := by
      calc
        (T : ℝ) * ((H : ℝ) / A) = ((T : ℝ) * H) / A := by ring
        _ ≤ 1 := (div_le_one (by exact_mod_cast hA)).2 hnum
    have hratio0 : 0 ≤ (T : ℝ) * ((H : ℝ) / A) := by positivity
    nlinarith
  have hExp :
      Real.exp (((T : ℝ) * ((H : ℝ) / (A : ℝ))) ^ 2) ≤
        Real.exp 1 := Real.exp_le_exp.mpr hTaylor
  have hInverse : (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤ 4 * D := by
    have hHreal : (0 : ℝ) < H := by exact_mod_cast hH
    rw [inv_div]
    apply (div_le_iff₀ hHreal).2
    norm_cast at hAhalf ⊢
    nlinarith
  have hFrequency :
      (T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤
        (1 + 8 * Real.pi) * D := by
    have hTleD : (T : ℝ) ≤ D := by
      exact_mod_cast (show T ≤ D by dsimp [D]; omega)
    calc
      (T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹) ≤
          (D : ℝ) + 2 * Real.pi * (4 * D) := by gcongr
      _ = (1 + 8 * Real.pi) * D := by ring
  have hDQ : D * Q ^ 2 ≤ A := by
    simpa only [A, D] using hhybrid
  have hHybridSize :
      ((1 + 8 * Real.pi) * (D : ℝ)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) ≤
        (1 + 8 * Real.pi) * (2 * (A : ℝ)) := by
    have hHDreal : (D : ℝ) * H ≤ A := by
      exact_mod_cast (by simpa [Nat.mul_comm] using hHD)
    have hDQreal : (D : ℝ) * (Q : ℝ) ^ 2 ≤ A := by
      exact_mod_cast hDQ
    calc
      ((1 + 8 * Real.pi) * (D : ℝ)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) =
          (1 + 8 * Real.pi) *
            ((D : ℝ) * H + (D : ℝ) * (Q : ℝ) ^ 2) := by ring
      _ ≤ (1 + 8 * Real.pi) * ((A : ℝ) + A) := by gcongr
      _ = (1 + 8 * Real.pi) * (2 * (A : ℝ)) := by ring
  have hEnergy := sum_detectorDyadicShell_weighted_energy_le
    Y N a k hY eta heta
  have hRaw := intervalIntegral_primitiveNegativeDirichletMass_shell_le
    Q Y N a H hY hH
      (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ))
      (T := (T : ℝ)) (by positivity)
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q
          (detectorDyadicShell Y N a)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
        Real.exp 1 *
          Real.exp (((T : ℝ) * ((H : ℝ) / A)) ^ 2) *
          ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by
      simpa only [A] using hRaw
    _ ≤ Real.exp 1 * Real.exp 1 *
          ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by
      have hrest : 0 ≤
          ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
          ((H : ℝ) + (Q : ℝ) ^ 2) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by
        positivity
      calc
        Real.exp 1 *
            Real.exp (((T : ℝ) * ((H : ℝ) / A)) ^ 2) *
            ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
            ((H : ℝ) + (Q : ℝ) ^ 2) *
            ∑ n ∈ detectorDyadicShell Y N a,
              ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 =
            Real.exp 1 *
              (Real.exp (((T : ℝ) * ((H : ℝ) / A)) ^ 2) *
                (((T : ℝ) + 2 * Real.pi *
                    (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
                  ((H : ℝ) + (Q : ℝ) ^ 2) *
                  ∑ n ∈ detectorDyadicShell Y N a,
                    ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2)) := by ring
        _ ≤ Real.exp 1 *
              (Real.exp 1 *
                (((T : ℝ) + 2 * Real.pi *
                    (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
                  ((H : ℝ) + (Q : ℝ) ^ 2) *
                  ∑ n ∈ detectorDyadicShell Y N a,
                    ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2)) := by
            gcongr
        _ = _ := by ring
    _ ≤ Real.exp 1 * Real.exp 1 *
          ((1 + 8 * Real.pi) * (2 * (A : ℝ))) *
          ∑ n ∈ detectorDyadicShell Y N a,
            ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by
      have hsum : 0 ≤ ∑ n ∈ detectorDyadicShell Y N a,
          ‖(weightedVonMangoldtMajorant eta k n : ℂ)‖ ^ 2 := by positivity
      have hpair :
          ((T : ℝ) + 2 * Real.pi * (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
              ((H : ℝ) + (Q : ℝ) ^ 2) ≤
            (1 + 8 * Real.pi) * (2 * (A : ℝ)) := by
        calc
          ((T : ℝ) + 2 * Real.pi *
              (((H : ℝ) / (2 * A : ℕ))⁻¹)) *
                ((H : ℝ) + (Q : ℝ) ^ 2) ≤
              ((1 + 8 * Real.pi) * (D : ℝ)) *
                ((H : ℝ) + (Q : ℝ) ^ 2) := by gcongr
          _ ≤ _ := hHybridSize
      simpa only [mul_assoc] using
        (mul_le_mul_of_nonneg_left
          (mul_le_mul_of_nonneg_right hpair hsum)
          (mul_nonneg (Real.exp_pos 1).le (Real.exp_pos 1).le))
    _ ≤ Real.exp 1 * Real.exp 1 *
          ((1 + 8 * Real.pi) * (2 * (A : ℝ))) *
          (((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1))) *
            (A : ℝ) ^ (-(1 + 2 * eta))) := by
      gcongr
    _ = (2 * Real.exp 2 * (1 + 8 * Real.pi)) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * (k + 1)) *
            (A : ℝ) ^ (-(2 * eta)) := by
      have hAreal : (0 : ℝ) < A := by exact_mod_cast hA
      rw [← Real.exp_add]
      have hrpow : (A : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) =
          (A : ℝ) ^ (-(2 * eta)) := by
        calc
          (A : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) =
              (A : ℝ) ^ (1 : ℝ) * (A : ℝ) ^ (-(1 + 2 * eta)) := by
                rw [Real.rpow_one]
          _ = (A : ℝ) ^ ((1 : ℝ) + -(1 + 2 * eta)) := by
                rw [Real.rpow_add hAreal]
          _ = (A : ℝ) ^ (-(2 * eta)) := by congr 1 <;> ring
      rw [show (1 : ℝ) + 1 = 2 by norm_num, ← hrpow]
      ring
    _ = _ := by rfl

end

end Erdos48
