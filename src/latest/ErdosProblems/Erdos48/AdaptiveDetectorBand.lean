/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.AdaptiveBlockPartition
import ErdosProblems.Erdos48.SharpDetectorEnergy

/-!
# A single adaptive hybrid estimate for the complete detector band

The blocks in `AdaptiveBlockPartition` are fed simultaneously to the
variable-length hybrid large sieve.  Thus no Cauchy--Schwarz factor is lost
when the dyadic shells are reassembled.
-/

namespace Erdos48

open Complex
open scoped BigOperators
open BoundedGaps.Maynard

noncomputable section

private theorem primitiveNegativeDirichletBlockMass_adaptive_eq
    (Q Y N T : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    primitiveNegativeDirichletBlockMass Q
        (adaptiveDetectorBlock Y N T) c t =
      primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t := by
  classical
  have hp :
      ((Finset.univ : Finset (adaptiveDetectorBlocks Y N T)) : Set _).PairwiseDisjoint
        (adaptiveDetectorBlock Y N T) := by
    intro z hz w hw hzw
    exact adaptiveDetectorBlock_pairwise_disjoint Y N T z w hzw
  unfold primitiveNegativeDirichletBlockMass primitiveNegativeDirichletMass
  apply Finset.sum_congr rfl
  intro q hq
  apply congrArg (fun z : ℝ ↦ (q : ℝ) / (q.totient : ℝ) * z)
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  rw [← Finset.sum_biUnion hp, biUnion_adaptiveDetectorBlock]

/-- The raw variable-length hybrid estimate for the whole band `(Y,N]`.
The only geometric assumption is that every active shell is at least as
long as the adaptive denominator. -/
theorem intervalIntegral_primitiveNegativeDirichletMass_adaptive_le
    (Q Y N T : ℕ) (hY : 1 ≤ Y)
    (hden : ∀ a ∈ detectorActiveShells Y N,
      adaptiveBlockDenominator T ≤ 2 ^ a)
    (c : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
      Real.exp 1 *
        Real.exp ((((T : ℝ) *
          (adaptiveBlockDenominator T : ℝ)⁻¹) ^ 2)) *
        ((T : ℝ) + 2 * Real.pi *
          ((8 * (T + 1 : ℕ) : ℝ)⁻¹)⁻¹) *
          ∑ z : adaptiveDetectorBlocks Y N T,
            (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                (Q : ℝ) ^ 2) *
              ∑ n ∈ adaptiveDetectorBlock Y N T z, ‖c n‖ ^ 2 := by
  let P : ℕ := adaptiveBlockDenominator T
  have hmain :=
    intervalIntegral_primitiveNegativeDirichletBlockMass_variable_le
      Q (adaptiveDetectorBlockLength Y N T)
      (adaptiveDetectorBlock Y N T) (adaptiveDetectorBlockStart Y N T)
      (adaptiveDetectorBlock_subset_Ioc hY)
      (adaptiveDetectorBlockCenter Y N T)
      (show 0 < (8 * (T + 1 : ℕ) : ℝ)⁻¹ by positivity)
      (show 0 ≤ (T : ℝ) by positivity)
      (adaptiveDetectorBlockCenter_separated hY hden) c
      (adaptiveDetectorBlock_pairwise_disjoint Y N T)
      (show 0 ≤ (P : ℝ)⁻¹ by positivity)
      (fun z n hn ↦ by
        simpa only [P] using
          adaptiveDetectorBlockCenter_offset_le hY hden z n hn)
  have hmass : primitiveNegativeDirichletBlockMass Q
      (adaptiveDetectorBlock Y N T) c =
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c := by
    funext t
    exact primitiveNegativeDirichletBlockMass_adaptive_eq Q Y N T c t
  rw [hmass] at hmain
  simpa only [P] using hmain

/-- Regrouping the adaptive blocks by their dyadic shell preserves an
arbitrary nonnegative coefficient energy. -/
theorem sum_adaptiveDetectorBlock_shellEnergy_eq
    (Y N T : ℕ) (c : ℕ → ℂ) :
    (∑ z : adaptiveDetectorBlocks Y N T,
        ((2 ^ z.1.1 : ℕ) : ℝ) *
          ∑ n ∈ adaptiveDetectorBlock Y N T z, ‖c n‖ ^ 2) =
      ∑ a ∈ detectorActiveShells Y N,
        ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 := by
  classical
  rw [Fintype.sum_sigma]
  rw [Finset.sum_subtype (s := detectorActiveShells Y N)
    (fun _ ↦ Iff.rfl)]
  apply Finset.sum_congr rfl
  intro a ha
  change (∑ i : {i // i ∈ shortBlockIndices
      (detectorDyadicShell Y N a.1) (2 ^ a.1)
        (adaptiveShellBlockLength T a.1)},
      ((2 ^ a.1 : ℕ) : ℝ) *
        ∑ n ∈ shortBlock (detectorDyadicShell Y N a.1) (2 ^ a.1)
          (adaptiveShellBlockLength T a.1) i, ‖c n‖ ^ 2) =
    ((2 ^ a.1 : ℕ) : ℝ) *
      ∑ n ∈ detectorDyadicShell Y N a.1, ‖c n‖ ^ 2
  rw [← Finset.mul_sum]
  congr 1
  rw [← Finset.sum_biUnion
    (pairwiseDisjoint_shortBlock (detectorDyadicShell Y N a.1) (2 ^ a.1)
      (adaptiveShellBlockLength T a.1)), biUnion_shortBlock]

private theorem adaptive_denominator_le_active_shell
    {Y N T : ℕ} (hheight : 4 * (T + 1) ≤ Y) :
    ∀ a ∈ detectorActiveShells Y N,
      adaptiveBlockDenominator T ≤ 2 ^ a := by
  intro a ha
  obtain ⟨n, hn⟩ := (Finset.mem_filter.mp ha).2
  have hnBand : Y < n := (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
  have hnShell := Finset.mem_Ioc.mp
    (detectorDyadicShell_subset Y N a (by omega) hn)
  have hP := adaptiveBlockDenominator_le_twice_vertical T
  omega

/-- Optimized whole-band hybrid estimate.  The height and conductor
hypotheses ensure that every local block length and the character-sieve
term are both paid for by its own dyadic shell length. -/
theorem intervalIntegral_primitiveNegativeDirichletMass_adaptive_optimized_le
    (Q Y N T : ℕ) (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ Y)
    (c : ℕ → ℂ) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
      2 * Real.exp 2 * (1 + 16 * Real.pi) *
        ∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 := by
  classical
  let D : ℕ := T + 1
  let P : ℕ := adaptiveBlockDenominator T
  let C : ℝ := 1 + 16 * Real.pi
  let E : adaptiveDetectorBlocks Y N T → ℝ := fun z ↦
    ∑ n ∈ adaptiveDetectorBlock Y N T z, ‖c n‖ ^ 2
  let V : ℝ := (T : ℝ) + 2 * Real.pi *
    ((8 * (T + 1 : ℕ) : ℝ)⁻¹)⁻¹
  have hden := adaptive_denominator_le_active_shell (N := N) hheight
  have hPpos : 0 < P := by
    dsimp [P]
    exact adaptiveBlockDenominator_pos T
  have hDP : D ≤ P := by
    simpa only [D, P] using vertical_le_adaptiveBlockDenominator T
  have hV : V ≤ C * D := by
    have hTD : (T : ℝ) ≤ D := by exact_mod_cast (show T ≤ D by omega)
    dsimp [V, C, D] at ⊢ hTD
    rw [inv_inv]
    push_cast
    nlinarith [Real.pi_pos]
  have hVnonneg : 0 ≤ V := by
    dsimp [V]
    positivity
  have hCnonneg : 0 ≤ C := by
    dsimp [C]
    positivity
  have hExp :
      Real.exp 1 * Real.exp ((((T : ℝ) * (P : ℝ)⁻¹) ^ 2)) ≤
        Real.exp 2 := by
    have hTPnat : T ≤ P := by omega
    have hTP : (T : ℝ) ≤ P := by exact_mod_cast hTPnat
    have hPinv : 0 ≤ (P : ℝ)⁻¹ := by positivity
    have hratio0 : 0 ≤ (T : ℝ) * (P : ℝ)⁻¹ := by positivity
    have hratio1 : (T : ℝ) * (P : ℝ)⁻¹ ≤ 1 := by
      calc
        (T : ℝ) * (P : ℝ)⁻¹ ≤ (P : ℝ) * (P : ℝ)⁻¹ :=
          mul_le_mul_of_nonneg_right hTP hPinv
        _ = 1 := mul_inv_cancel₀ (by exact_mod_cast hPpos.ne')
    have hsq : (((T : ℝ) * (P : ℝ)⁻¹) ^ 2) ≤ 1 := by
      simpa only [one_pow] using pow_le_pow_left₀ hratio0 hratio1 2
    calc
      Real.exp 1 * Real.exp ((((T : ℝ) * (P : ℝ)⁻¹) ^ 2)) ≤
          Real.exp 1 * Real.exp 1 := by gcongr
      _ = Real.exp 2 := by rw [← Real.exp_add]; norm_num
  have hsum :
      V * ∑ z : adaptiveDetectorBlocks Y N T,
          (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
              (Q : ℝ) ^ 2) * E z ≤
        2 * C * ∑ z : adaptiveDetectorBlocks Y N T,
          ((2 ^ z.1.1 : ℕ) : ℝ) * E z := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    let A : ℕ := 2 ^ z.1.1
    let H : ℕ := adaptiveShellBlockLength T z.1.1
    have hHA : H * P = A := by
      simpa only [H, P, A] using
        adaptiveShellBlockLength_mul_denominator (hden z.1.1 z.1.2)
    have hHD : H * D ≤ A := by
      calc
        H * D ≤ H * P := Nat.mul_le_mul_left H hDP
        _ = A := hHA
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp z.1.2).2
    have hnBand : Y < n :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    have hnShell := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N z.1.1 hY hn)
    have hDQ : D * Q ^ 2 ≤ A := by
      have htwo : 2 * (D * Q ^ 2) ≤ Y := by
        simpa only [D] using hconductor
      dsimp [A]
      omega
    have hHDreal : (H : ℝ) * D ≤ A := by exact_mod_cast hHD
    have hDQreal : (D : ℝ) * (Q : ℝ) ^ 2 ≤ A := by
      exact_mod_cast hDQ
    have hlocal : (D : ℝ) * ((H : ℝ) + (Q : ℝ) ^ 2) ≤
        2 * A := by
      nlinarith
    have hweight :
        V * ((H : ℝ) + (Q : ℝ) ^ 2) ≤ 2 * C * A := by
      calc
        V * ((H : ℝ) + (Q : ℝ) ^ 2) ≤
            (C * D) * ((H : ℝ) + (Q : ℝ) ^ 2) := by gcongr
        _ = C * ((D : ℝ) * ((H : ℝ) + (Q : ℝ) ^ 2)) := by ring
        _ ≤ C * (2 * A) := mul_le_mul_of_nonneg_left hlocal hCnonneg
        _ = 2 * C * A := by ring
    have hEnonneg : 0 ≤ E z := by dsimp [E]; positivity
    simpa only [adaptiveDetectorBlockLength, H, A, E, mul_assoc] using
      mul_le_mul_of_nonneg_right hweight hEnonneg
  have hraw := intervalIntegral_primitiveNegativeDirichletMass_adaptive_le
    Q Y N T hY hden c
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
        Real.exp 1 *
          Real.exp ((((T : ℝ) * (P : ℝ)⁻¹) ^ 2)) * V *
            ∑ z : adaptiveDetectorBlocks Y N T,
              (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                  (Q : ℝ) ^ 2) * E z := by
      simpa only [P, V, E] using hraw
    _ ≤ Real.exp 2 *
          (V * ∑ z : adaptiveDetectorBlocks Y N T,
            (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                (Q : ℝ) ^ 2) * E z) := by
      have hsumNonneg : 0 ≤ ∑ z : adaptiveDetectorBlocks Y N T,
          (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
              (Q : ℝ) ^ 2) * E z := by
        apply Finset.sum_nonneg
        intro z hz
        positivity
      rw [mul_assoc]
      exact mul_le_mul_of_nonneg_right hExp
        (mul_nonneg hVnonneg hsumNonneg)
    _ ≤ Real.exp 2 *
          (2 * C * ∑ z : adaptiveDetectorBlocks Y N T,
            ((2 ^ z.1.1 : ℕ) : ℝ) * E z) := by
      exact mul_le_mul_of_nonneg_left hsum (Real.exp_pos 2).le
    _ = 2 * Real.exp 2 * (1 + 16 * Real.pi) *
          ∑ a ∈ detectorActiveShells Y N,
            ((2 ^ a : ℕ) : ℝ) *
              ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 := by
      rw [sum_adaptiveDetectorBlock_shellEnergy_eq]
      dsimp [C, E]
      ring

/-- The optimized adaptive mean square with the sharp Chebyshev energy
inserted shell by shell. -/
theorem intervalIntegral_weightedDetectorBand_adaptive_le
    (Q Y N T k : ℕ) (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hconductor : 2 * ((T + 1) * Q ^ 2) ≤ Y)
    (eta : ℝ) (heta : 0 ≤ eta) :
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          (fun n ↦ (weightedVonMangoldtMajorant eta k n : ℂ)) t) ≤
      4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ∑ a ∈ detectorActiveShells Y N,
          ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * k + 1)) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) := by
  let c : ℕ → ℂ := fun n ↦
    (weightedVonMangoldtMajorant eta k n : ℂ)
  let C : ℝ := 2 * Real.exp 2 * (1 + 16 * Real.pi)
  let W : ℕ → ℝ := fun a ↦
    ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * k + 1)) *
      ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta))
  have hmain :=
    intervalIntegral_primitiveNegativeDirichletMass_adaptive_optimized_le
      Q Y N T hY hheight hconductor c
  have hterm : ∀ a ∈ detectorActiveShells Y N,
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 ≤
        2 * (Real.log 4 + 4) * W a := by
    intro a ha
    have henergy := sum_detectorDyadicShell_weighted_energy_sharp_le
      Y N a k hY eta heta
    have hApos : (0 : ℝ) < (2 ^ a : ℕ) := by positivity
    have hpow : ((2 ^ a : ℕ) : ℝ) *
          ((2 ^ a : ℕ) : ℝ) ^ (-(1 + 2 * eta)) =
        ((2 ^ a : ℕ) : ℝ) ^ (-(2 * eta)) := by
      calc
        ((2 ^ a : ℕ) : ℝ) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(1 + 2 * eta)) =
          ((2 ^ a : ℕ) : ℝ) ^ (1 : ℝ) *
            ((2 ^ a : ℕ) : ℝ) ^ (-(1 + 2 * eta)) := by
              rw [Real.rpow_one]
        _ = ((2 ^ a : ℕ) : ℝ) ^ ((1 : ℝ) + -(1 + 2 * eta)) := by
              rw [Real.rpow_add hApos]
        _ = _ := by congr 1 <;> ring
    calc
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 ≤
        ((2 ^ a : ℕ) : ℝ) *
          (2 * (Real.log 4 + 4) *
            ((((a + 1 : ℕ) : ℝ) * Real.log 2) ^ (2 * k + 1)) *
              ((2 ^ a : ℕ) : ℝ) ^ (-(1 + 2 * eta))) := by
        exact mul_le_mul_of_nonneg_left henergy hApos.le
      _ = 2 * (Real.log 4 + 4) * W a := by
        dsimp [W]
        rw [← hpow]
        ring
  have hsum :
      (∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2) ≤
        2 * (Real.log 4 + 4) *
          ∑ a ∈ detectorActiveShells Y N, W a := by
    calc
      _ ≤ ∑ a ∈ detectorActiveShells Y N,
          2 * (Real.log 4 + 4) * W a :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.mul_sum]
  calc
    (∫ t in (0 : ℝ)..(T : ℝ),
        primitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t) ≤
      C * ∑ a ∈ detectorActiveShells Y N,
        ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ detectorDyadicShell Y N a, ‖c n‖ ^ 2 := by
      simpa only [c, C] using hmain
    _ ≤ C * (2 * (Real.log 4 + 4) *
        ∑ a ∈ detectorActiveShells Y N, W a) := by
      exact mul_le_mul_of_nonneg_left hsum (by dsimp [C]; positivity)
    _ = 4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ∑ a ∈ detectorActiveShells Y N, W a := by
      dsimp [C]
      ring
    _ = _ := rfl

end

end Erdos48
