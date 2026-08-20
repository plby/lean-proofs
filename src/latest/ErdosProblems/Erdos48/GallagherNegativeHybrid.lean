/-
Copyright (c) 2026. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI Codex
-/
import ErdosProblems.Erdos48.GallagherCoefficient
import ErdosProblems.Erdos48.AdaptiveDetectorBand
import ErdosProblems.Erdos48.PrimePowerDetector

/-!
# Rough-amplified negative-phase hybrid estimates

This module transports the finite Bombieri--Davenport amplifier through
the Taylor hybrid large sieve, the adaptive detector partition, and the
prime-supported part of Gallagher's cutoff polynomial.  The resulting
mean square retains a uniform amplifier coefficient on the left.
-/

open scoped BigOperators

noncomputable section

namespace Erdos48

open BoundedGaps.Maynard

noncomputable def unweightedPrimitiveNegativeDirichletBlockMass
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (s : ι → Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    ∑ psi : primitiveCharacters q,
      ‖∑ i, ∑ n ∈ s i,
        c n * psi.1 n *
          Complex.exp (Complex.I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2

noncomputable def unweightedPrimitiveNegativeDirichletMass
    (Q : ℕ) (s : Finset ℕ) (c : ℕ → ℂ) (t : ℝ) : ℝ :=
  ∑ q ∈ Finset.Ioc 0 Q,
    ∑ psi : primitiveCharacters q,
      ‖∑ n ∈ s, c n * psi.1 n *
        Complex.exp (Complex.I * (((-t * Real.log n) : ℝ) : ℂ))‖ ^ 2

theorem unweightedPrimitiveHybridMass_neg_blockLogOffset_eq
    {ι : Type*} [Fintype ι]
    (Q : ℕ) (x : ι → ℝ) (s : ι → Finset ℕ)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j)) (t : ℝ) :
    unweightedPrimitiveHybridMass Q (fun i ↦ -x i) s c
        (fun n ↦ -blockLogOffset x s n) t =
      unweightedPrimitiveNegativeDirichletBlockMass Q s c t := by
  classical
  unfold unweightedPrimitiveHybridMass
    unweightedPrimitiveNegativeDirichletBlockMass
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  apply Finset.sum_congr rfl
  intro i hi
  apply Finset.sum_congr rfl
  intro n hn
  dsimp only
  rw [blockLogOffset_eq x s hdisj i hn]
  congr 2
  push_cast
  ring

theorem mul_intervalIntegral_unweightedPrimitiveNegativeDirichletBlockMass_variable_le
    {ι : Type*} [Fintype ι]
    (Q A : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (H : ι → ℕ) (s : ι → Finset ℕ) (m0 : ι → ℕ)
    (hs : ∀ i, s i ⊆ Finset.Ioc (m0 i) (m0 i + H i))
    (x : ι → ℝ) {δ T B : ℝ}
    (hδ : 0 < δ) (hT : 0 ≤ T)
    (hsep : ∀ r t, r ≠ t → δ ≤ |x r - x t|)
    (c : ℕ → ℂ)
    (hdisj : ∀ i j, i ≠ j → Disjoint (s i) (s j))
    (hB : 0 ≤ B)
    (hoffset : ∀ i, ∀ n ∈ s i, |Real.log n - x i| ≤ B)
    (hprime : ∀ i n, n ∈ s i → n.Prime)
    (hrough : ∀ i n, n ∈ s i → Q * A < n) :
    L * (∫ t in (0 : ℝ)..T,
        unweightedPrimitiveNegativeDirichletBlockMass Q s c t) ≤
      Real.exp 1 * Real.exp ((T * B) ^ 2) *
        (T + 2 * Real.pi * δ⁻¹) *
          ∑ i, (((H i : ℕ) : ℝ) + (Q * A : ℕ) ^ 2) *
            ∑ n ∈ s i, ‖c n‖ ^ 2 := by
  let d : ℕ → ℝ := fun n ↦ -blockLogOffset x s n
  have hd : ∀ i, ∀ n ∈ s i, |d n| ≤ B := by
    intro i n hn
    rw [show d n = -(Real.log n - x i) by
      dsimp [d]
      rw [blockLogOffset_eq x s hdisj i hn], abs_neg]
    exact hoffset i n hn
  have hsepNeg : ∀ r t, r ≠ t → δ ≤ |(-x r) - (-x t)| := by
    intro r t hrt
    simpa only [neg_sub_neg, abs_neg] using hsep t r hrt.symm
  have hmain := mul_intervalIntegral_unweightedPrimitiveHybridMass_variable_le
    Q A L hL hcoeff H s m0 hs (fun i ↦ -x i)
      hδ hT hsepNeg c d hB hd hprime hrough
  rw [show unweightedPrimitiveHybridMass Q (fun i ↦ -x i) s c d =
      unweightedPrimitiveNegativeDirichletBlockMass Q s c by
    funext t
    exact unweightedPrimitiveHybridMass_neg_blockLogOffset_eq
      Q x s c hdisj t] at hmain
  exact hmain

private theorem unweightedPrimitiveNegativeDirichletBlockMass_adaptive_eq
    (Q Y N T : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletBlockMass Q
        (adaptiveDetectorBlock Y N T) c t =
      unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N) c t := by
  classical
  have hp :
      ((Finset.univ : Finset (adaptiveDetectorBlocks Y N T)) : Set _).PairwiseDisjoint
        (adaptiveDetectorBlock Y N T) := by
    intro z hz w hw hzw
    exact adaptiveDetectorBlock_pairwise_disjoint Y N T z w hzw
  unfold unweightedPrimitiveNegativeDirichletBlockMass
    unweightedPrimitiveNegativeDirichletMass
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  rw [← Finset.sum_biUnion hp, biUnion_adaptiveDetectorBlock]

noncomputable def adaptivePrimeDetectorBlock
    (Y N T : ℕ) (z : adaptiveDetectorBlocks Y N T) : Finset ℕ :=
  (adaptiveDetectorBlock Y N T z).filter Nat.Prime

theorem adaptivePrimeDetectorBlock_subset_Ioc
    {Y N T : ℕ} (hY : 1 ≤ Y) (z : adaptiveDetectorBlocks Y N T) :
    adaptivePrimeDetectorBlock Y N T z ⊆
      Finset.Ioc (adaptiveDetectorBlockStart Y N T z)
        (adaptiveDetectorBlockStart Y N T z +
          adaptiveDetectorBlockLength Y N T z) := by
  intro n hn
  exact adaptiveDetectorBlock_subset_Ioc hY z (Finset.mem_filter.mp hn).1

theorem adaptivePrimeDetectorBlock_pairwise_disjoint
    (Y N T : ℕ) :
    ∀ z w : adaptiveDetectorBlocks Y N T, z ≠ w →
      Disjoint (adaptivePrimeDetectorBlock Y N T z)
        (adaptivePrimeDetectorBlock Y N T w) := by
  intro z w hzw
  exact (adaptiveDetectorBlock_pairwise_disjoint Y N T z w hzw).mono
    (Finset.filter_subset _ _) (Finset.filter_subset _ _)

theorem biUnion_adaptivePrimeDetectorBlock (Y N T : ℕ) :
    (Finset.univ.biUnion (adaptivePrimeDetectorBlock Y N T)) =
      (Finset.Ioc Y N).filter Nat.Prime := by
  classical
  ext n
  simp only [Finset.mem_biUnion, Finset.mem_univ, true_and,
    adaptivePrimeDetectorBlock, Finset.mem_filter]
  constructor
  · rintro ⟨z, hn, hp⟩
    exact ⟨by
      rw [← biUnion_adaptiveDetectorBlock Y N T]
      exact Finset.mem_biUnion.mpr ⟨z, Finset.mem_univ _, hn⟩, hp⟩
  · rintro ⟨hn, hp⟩
    rw [← biUnion_adaptiveDetectorBlock Y N T] at hn
    obtain ⟨z, hz, hnz⟩ := Finset.mem_biUnion.mp hn
    exact ⟨z, hnz, hp⟩

private theorem unweightedPrimitiveNegativeDirichletBlockMass_adaptivePrime_eq
    (Q Y N T : ℕ) (c : ℕ → ℂ) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletBlockMass Q
        (adaptivePrimeDetectorBlock Y N T) c t =
      unweightedPrimitiveNegativeDirichletMass Q
        ((Finset.Ioc Y N).filter Nat.Prime) c t := by
  classical
  have hp :
      ((Finset.univ : Finset (adaptiveDetectorBlocks Y N T)) : Set _).PairwiseDisjoint
        (adaptivePrimeDetectorBlock Y N T) :=
    fun z _ w _ hzw ↦ adaptivePrimeDetectorBlock_pairwise_disjoint Y N T z w hzw
  unfold unweightedPrimitiveNegativeDirichletBlockMass
    unweightedPrimitiveNegativeDirichletMass
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  rw [← Finset.sum_biUnion hp, biUnion_adaptivePrimeDetectorBlock]

/-- The exact rough-amplified hybrid estimate for the prime-filtered
adaptive detector band. -/
theorem mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_adaptivePrime_le
    (Q A Y N T : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (hY : 1 ≤ Y)
    (hden : ∀ a ∈ detectorActiveShells Y N,
      adaptiveBlockDenominator T ≤ 2 ^ a)
    (hrough : Q * A ≤ Y)
    (c : ℕ → ℂ) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q
          ((Finset.Ioc Y N).filter Nat.Prime) c t) ≤
      Real.exp 1 *
        Real.exp ((((T : ℝ) *
          (adaptiveBlockDenominator T : ℝ)⁻¹) ^ 2)) *
        ((T : ℝ) + 2 * Real.pi *
          ((8 * (T + 1 : ℕ) : ℝ)⁻¹)⁻¹) *
          ∑ z : adaptiveDetectorBlocks Y N T,
            (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                (Q * A : ℝ) ^ 2) *
              ∑ n ∈ adaptivePrimeDetectorBlock Y N T z, ‖c n‖ ^ 2 := by
  let P : ℕ := adaptiveBlockDenominator T
  have hmain :=
    mul_intervalIntegral_unweightedPrimitiveNegativeDirichletBlockMass_variable_le
      Q A L hL hcoeff (adaptiveDetectorBlockLength Y N T)
      (adaptivePrimeDetectorBlock Y N T) (adaptiveDetectorBlockStart Y N T)
      (adaptivePrimeDetectorBlock_subset_Ioc hY)
      (adaptiveDetectorBlockCenter Y N T)
      (show 0 < (8 * (T + 1 : ℕ) : ℝ)⁻¹ by positivity)
      (show 0 ≤ (T : ℝ) by positivity)
      (adaptiveDetectorBlockCenter_separated hY hden) c
      (adaptivePrimeDetectorBlock_pairwise_disjoint Y N T)
      (show 0 ≤ (P : ℝ)⁻¹ by positivity)
      (fun z n hn ↦ by
        simpa only [P] using adaptiveDetectorBlockCenter_offset_le hY hden z n
          (Finset.mem_filter.mp hn).1)
      (fun z n hn ↦ (Finset.mem_filter.mp hn).2)
      (fun z n hn ↦ by
        have hnBlock := Finset.mem_filter.mp hn |>.1
        have hnShell : n ∈ detectorDyadicShell Y N z.1.1 :=
          (Finset.mem_filter.mp hnBlock).1
        have hnBand : Y < n :=
          (Finset.mem_Ioc.mp (Finset.mem_filter.mp hnShell).1).1
        omega)
  have hmass : unweightedPrimitiveNegativeDirichletBlockMass Q
      (adaptivePrimeDetectorBlock Y N T) c =
        unweightedPrimitiveNegativeDirichletMass Q
          ((Finset.Ioc Y N).filter Nat.Prime) c := by
    funext t
    exact unweightedPrimitiveNegativeDirichletBlockMass_adaptivePrime_eq
      Q Y N T c t
  rw [hmass] at hmain
  simpa only [P, Nat.cast_mul] using hmain

private theorem adaptive_denominator_le_active_shell'
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

theorem sum_adaptivePrimeDetectorBlock_shellEnergy_eq
    (Y N T : ℕ) (c : ℕ → ℂ) :
    (∑ z : adaptiveDetectorBlocks Y N T,
        ((2 ^ z.1.1 : ℕ) : ℝ) *
          ∑ n ∈ adaptivePrimeDetectorBlock Y N T z, ‖c n‖ ^ 2) =
      ∑ a ∈ detectorActiveShells Y N,
        ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖c n‖ ^ 2 := by
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
        ∑ n ∈ (shortBlock (detectorDyadicShell Y N a.1) (2 ^ a.1)
          (adaptiveShellBlockLength T a.1) i).filter Nat.Prime,
          ‖c n‖ ^ 2) =
    ((2 ^ a.1 : ℕ) : ℝ) *
      ∑ n ∈ (detectorDyadicShell Y N a.1).filter Nat.Prime, ‖c n‖ ^ 2
  rw [← Finset.mul_sum]
  congr 1
  have hp :
      ((Finset.univ : Finset {i // i ∈ shortBlockIndices
        (detectorDyadicShell Y N a.1) (2 ^ a.1)
          (adaptiveShellBlockLength T a.1)}) : Set _).PairwiseDisjoint
        (fun i ↦ (shortBlock (detectorDyadicShell Y N a.1) (2 ^ a.1)
          (adaptiveShellBlockLength T a.1) i).filter Nat.Prime) := by
    intro i hi j hj hij
    exact (pairwiseDisjoint_shortBlock
      (detectorDyadicShell Y N a.1) (2 ^ a.1)
      (adaptiveShellBlockLength T a.1) hi hj hij).mono
        (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  rw [← Finset.sum_biUnion hp]
  rw [← Finset.filter_biUnion, biUnion_shortBlock]

/-- The optimized rough-amplified mean square on the prime part of the
cutoff band.  The logarithmic amplifier coefficient remains as the factor
`L` on the left. -/
theorem mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_adaptivePrime_optimized_le
    (Q A Y N T : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hrough : Q * A ≤ Y)
    (hconductor : 2 * ((T + 1) * (Q * A) ^ 2) ≤ Y)
    (c : ℕ → ℂ) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q
          ((Finset.Ioc Y N).filter Nat.Prime) c t) ≤
      2 * Real.exp 2 * (1 + 16 * Real.pi) *
        ∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
              ‖c n‖ ^ 2 := by
  classical
  let D : ℕ := T + 1
  let P : ℕ := adaptiveBlockDenominator T
  let C : ℝ := 1 + 16 * Real.pi
  let E : adaptiveDetectorBlocks Y N T → ℝ := fun z ↦
    ∑ n ∈ adaptivePrimeDetectorBlock Y N T z, ‖c n‖ ^ 2
  let V : ℝ := (T : ℝ) + 2 * Real.pi *
    ((8 * (T + 1 : ℕ) : ℝ)⁻¹)⁻¹
  have hden := adaptive_denominator_le_active_shell' (N := N) hheight
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
              (Q * A : ℝ) ^ 2) * E z ≤
        2 * C * ∑ z : adaptiveDetectorBlocks Y N T,
          ((2 ^ z.1.1 : ℕ) : ℝ) * E z := by
    rw [Finset.mul_sum, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro z hz
    let S : ℕ := 2 ^ z.1.1
    let H : ℕ := adaptiveShellBlockLength T z.1.1
    have hHS : H * P = S := by
      simpa only [H, P, S] using
        adaptiveShellBlockLength_mul_denominator (hden z.1.1 z.1.2)
    have hHD : H * D ≤ S := by
      calc
        H * D ≤ H * P := Nat.mul_le_mul_left H hDP
        _ = S := hHS
    obtain ⟨n, hn⟩ := (Finset.mem_filter.mp z.1.2).2
    have hnBand : Y < n :=
      (Finset.mem_Ioc.mp (Finset.mem_filter.mp hn).1).1
    have hnShell := Finset.mem_Ioc.mp
      (detectorDyadicShell_subset Y N z.1.1 hY hn)
    have hDQ : D * (Q * A) ^ 2 ≤ S := by
      have htwo : 2 * (D * (Q * A) ^ 2) ≤ Y := by
        simpa only [D] using hconductor
      dsimp [S]
      omega
    have hHDreal : (H : ℝ) * D ≤ S := by exact_mod_cast hHD
    have hDQreal : (D : ℝ) * (Q * A : ℝ) ^ 2 ≤ S := by
      exact_mod_cast hDQ
    have hlocal : (D : ℝ) * ((H : ℝ) + (Q * A : ℝ) ^ 2) ≤
        2 * S := by
      nlinarith
    have hweight :
        V * ((H : ℝ) + (Q * A : ℝ) ^ 2) ≤ 2 * C * S := by
      calc
        V * ((H : ℝ) + (Q * A : ℝ) ^ 2) ≤
            (C * D) * ((H : ℝ) + (Q * A : ℝ) ^ 2) := by gcongr
        _ = C * ((D : ℝ) * ((H : ℝ) + (Q * A : ℝ) ^ 2)) := by ring
        _ ≤ C * (2 * S) := mul_le_mul_of_nonneg_left hlocal hCnonneg
        _ = 2 * C * S := by ring
    have hEnonneg : 0 ≤ E z := by dsimp [E]; positivity
    simpa only [adaptiveDetectorBlockLength, H, S, E, mul_assoc] using
      mul_le_mul_of_nonneg_right hweight hEnonneg
  have hraw :=
    mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_adaptivePrime_le
      Q A Y N T L hL hcoeff hY hden hrough c
  calc
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q
          ((Finset.Ioc Y N).filter Nat.Prime) c t) ≤
        Real.exp 1 *
          Real.exp ((((T : ℝ) * (P : ℝ)⁻¹) ^ 2)) * V *
            ∑ z : adaptiveDetectorBlocks Y N T,
              (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                  (Q * A : ℝ) ^ 2) * E z := by
      simpa only [P, V, E] using hraw
    _ ≤ Real.exp 2 *
          (V * ∑ z : adaptiveDetectorBlocks Y N T,
            (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
                (Q * A : ℝ) ^ 2) * E z) := by
      have hsumNonneg : 0 ≤ ∑ z : adaptiveDetectorBlocks Y N T,
          (((adaptiveDetectorBlockLength Y N T z : ℕ) : ℝ) +
              (Q * A : ℝ) ^ 2) * E z := by
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
              ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
                ‖c n‖ ^ 2 := by
      rw [sum_adaptivePrimeDetectorBlock_shellEnergy_eq]
      dsimp [C, E]
      ring

theorem unweightedPrimitiveNegativeDirichletMass_filter_primeCutoffCoefficient
    (Q : ℕ) (s : Finset ℕ) (t : ℝ) :
    unweightedPrimitiveNegativeDirichletMass Q (s.filter Nat.Prime)
        primeCutoffCoefficient t =
      unweightedPrimitiveNegativeDirichletMass Q s
        primeCutoffCoefficient t := by
  classical
  unfold unweightedPrimitiveNegativeDirichletMass
  apply Finset.sum_congr rfl
  intro q hq
  apply Finset.sum_congr rfl
  intro psi hpsi
  congr 2
  rw [Finset.sum_filter]
  apply Finset.sum_congr rfl
  intro n hn
  by_cases hp : n.Prime <;> simp [primeCutoffCoefficient, hp]

theorem primeCutoffCoefficient_eq_weighted_of_prime
    {n : ℕ} (hn : n.Prime) :
    primeCutoffCoefficient n =
      (weightedVonMangoldtMajorant 0 0 n : ℂ) := by
  rw [primeCutoffCoefficient, if_pos hn,
    cutoffVonMangoldtCoefficient_eq_weighted]

/-- The prime-supported part of the Gallagher cutoff enjoys the extra
rough-amplifier factor `L`, while retaining the sharp one-logarithm shell
energy. -/
theorem mul_intervalIntegral_primeCutoff_adaptive_le
    (Q A Y N T : ℕ) (L : ℝ) (hL : 0 ≤ L)
    (hcoeff : ∀ q ∈ Finset.Ioc 0 Q,
      L ≤ roughAmplifierCoefficient q A)
    (hY : 1 ≤ Y)
    (hheight : 4 * (T + 1) ≤ Y)
    (hrough : Q * A ≤ Y)
    (hconductor : 2 * ((T + 1) * (Q * A) ^ 2) ≤ Y) :
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          primeCutoffCoefficient t) ≤
      4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ∑ a ∈ detectorActiveShells Y N,
          ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
  let C : ℝ := 2 * Real.exp 2 * (1 + 16 * Real.pi)
  have hmain :=
    mul_intervalIntegral_unweightedPrimitiveNegativeDirichletMass_adaptivePrime_optimized_le
      Q A Y N T L hL hcoeff hY hheight hrough hconductor
        primeCutoffCoefficient
  rw [show unweightedPrimitiveNegativeDirichletMass Q
      ((Finset.Ioc Y N).filter Nat.Prime) primeCutoffCoefficient =
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          primeCutoffCoefficient by
    funext t
    exact unweightedPrimitiveNegativeDirichletMass_filter_primeCutoffCoefficient
      Q (Finset.Ioc Y N) t] at hmain
  have hterm : ∀ a ∈ detectorActiveShells Y N,
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖primeCutoffCoefficient n‖ ^ 2 ≤
        2 * (Real.log 4 + 4) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) := by
    intro a ha
    have henergyFull := sum_detectorDyadicShell_weighted_energy_sharp_le
      Y N a 0 hY 0 (by positivity)
    have henergy :
        (∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖primeCutoffCoefficient n‖ ^ 2) ≤
          2 * (Real.log 4 + 4) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) *
              ((2 ^ a : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
      calc
        (∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖primeCutoffCoefficient n‖ ^ 2) =
            ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
              ‖(weightedVonMangoldtMajorant 0 0 n : ℂ)‖ ^ 2 := by
          apply Finset.sum_congr rfl
          intro n hn
          rw [primeCutoffCoefficient_eq_weighted_of_prime
            (Finset.mem_filter.mp hn).2]
        _ ≤ ∑ n ∈ detectorDyadicShell Y N a,
              ‖(weightedVonMangoldtMajorant 0 0 n : ℂ)‖ ^ 2 := by
          exact Finset.sum_le_sum_of_subset_of_nonneg
            (Finset.filter_subset _ _) (fun n hn hnot ↦ by positivity)
        _ ≤ 2 * (Real.log 4 + 4) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) *
              ((2 ^ a : ℕ) : ℝ) ^ (-(1 : ℝ)) := by
          simpa using henergyFull
    have hApos : (0 : ℝ) < (2 ^ a : ℕ) := by positivity
    calc
      ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖primeCutoffCoefficient n‖ ^ 2 ≤
        ((2 ^ a : ℕ) : ℝ) *
          (2 * (Real.log 4 + 4) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) *
              ((2 ^ a : ℕ) : ℝ) ^ (-(1 : ℝ))) :=
        mul_le_mul_of_nonneg_left henergy hApos.le
      _ = 2 * (Real.log 4 + 4) *
          (((a + 1 : ℕ) : ℝ) * Real.log 2) := by
        rw [Real.rpow_neg_one]
        field_simp
  have hsum :
      (∑ a ∈ detectorActiveShells Y N,
          ((2 ^ a : ℕ) : ℝ) *
            ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
              ‖primeCutoffCoefficient n‖ ^ 2) ≤
        2 * (Real.log 4 + 4) *
          ∑ a ∈ detectorActiveShells Y N,
            ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
    calc
      _ ≤ ∑ a ∈ detectorActiveShells Y N,
          2 * (Real.log 4 + 4) *
            (((a + 1 : ℕ) : ℝ) * Real.log 2) :=
        Finset.sum_le_sum hterm
      _ = _ := by rw [Finset.mul_sum]
  calc
    L * (∫ t in (0 : ℝ)..(T : ℝ),
        unweightedPrimitiveNegativeDirichletMass Q (Finset.Ioc Y N)
          primeCutoffCoefficient t) ≤
      C * ∑ a ∈ detectorActiveShells Y N,
        ((2 ^ a : ℕ) : ℝ) *
          ∑ n ∈ (detectorDyadicShell Y N a).filter Nat.Prime,
            ‖primeCutoffCoefficient n‖ ^ 2 := by
      simpa only [C] using hmain
    _ ≤ C * (2 * (Real.log 4 + 4) *
          ∑ a ∈ detectorActiveShells Y N,
            ((a + 1 : ℕ) : ℝ) * Real.log 2) := by
      exact mul_le_mul_of_nonneg_left hsum (by dsimp [C]; positivity)
    _ = 4 * Real.exp 2 * (1 + 16 * Real.pi) * (Real.log 4 + 4) *
        ∑ a ∈ detectorActiveShells Y N,
          ((a + 1 : ℕ) : ℝ) * Real.log 2 := by
      dsimp [C]
      ring

end Erdos48
