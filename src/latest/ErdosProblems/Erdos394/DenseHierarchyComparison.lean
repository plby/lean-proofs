import ErdosProblems.Erdos394.DenseHierarchyNumerator
import ErdosProblems.Erdos394.DenseHierarchyDenominator
import ErdosProblems.Erdos394.EulerGapAlgebra

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Adjacent hierarchy comparison on the dense grid
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- An integer coefficient dominating the explicit real root-box coefficient. -/
def denseRootCoefficient (L : ℕ) : ℕ :=
  2 + (((80 * (L * L - 1) + 160 * L) + 2 + 88) * (L + 1))

lemma generalRootMeanFactor_eq_denseRootCoefficient (L r : ℕ) :
    generalRootMeanFactor L r = 2 + (r : ℝ) * denseRootCoefficient L := by
  unfold generalRootMeanFactor denseRootCoefficient
  push_cast
  ring

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- Uniformly between consecutive dense-grid points, the adjacent numerator
is eventually at most `3/h` times the denominator, where `h=⌊log₂N⌋`. -/
theorem eventually_dense_adjacent_three_mul_bound_uniform
    (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ,
      denseHierarchyX N ≤ X → X ≤ denseHierarchyX (N + 1) →
      (denseHierarchyLog N : ℝ) *
          (∑ n ∈ Finset.Icc 1 X, (t (K + 1) n : ℝ)) ≤
        3 * (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) := by
  let L := K + 1
  let M := (K + 1) * (2 * K + 1)
  let Dexp := 1105 * M + 100
  let Fcoef := 4 * 1048576 * K
  let H0 := max (max (max (1001 + 2) (2 * (2 * K + 1)))
    (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)
  have hnumEv := eventually_dense_hierarchy_numerator_bound_uniform K hK
  have hdenEv := eventually_dense_hierarchy_denominator_bound_uniform K hK
  have horder := eventually_denseHierarchyOrder_le
  have hscaled := eventually_dense_primeInterval_euler_scaled
  have hE4 := eventually_four_le_dense_denominatorEuler K hK
  have hzy := eventually_denseLower_le_upper
  have hhlarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop H0)
  have hD := eventually_denseLog_pow_le Dexp
  have hpoly1003 := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_nat_pow_le_two_pow 1003)
  have hN1009 := eventually_nat_pow_le_two_pow 1009
  filter_upwards [eventually_gt_atTop 0, hnumEv, hdenEv, horder, hscaled,
    hE4, hzy, hhlarge, hD, hpoly1003, hN1009] with
      N hN hnumAll hdenAll hR hscaledN hE4N hzyN hh hDpow hpoly hNpoly
  intro X hXlower hXupper
  have hnum := hnumAll X
  have hden := hdenAll X hXlower hXupper
  let h := denseHierarchyLog N
  let z := denseHierarchyZ N
  let y := denseHierarchyY N
  let R := denseHierarchyOrder N
  let C0 := denseDenominatorDilution N
  let P := primeInterval z y
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let Eplus := ∏ p ∈ P, (1 + 1 / (((K + 1 : ℕ) : ℝ) * (p : ℝ)))
  let Eden := ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))
  let W := generalRootMeanFactor (K + 1) R
  let Dmain := (Real.log 2 * (X : ℝ) ^ 2 /
      (1048576 * (C0 : ℝ) * (K : ℝ) * Real.log X)) * Eden
  let U1 := (X : ℝ) ^ 2 / (z : ℝ)
  let U2 := 2 * (X : ℝ) ^ 2 * V * (W * Eplus)
  let U3 := 2 * (X : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) *
      (W * ((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ))
  have hhpos : 0 < h := by
    have : 1001 + 2 ≤ h :=
      (le_max_left (1001 + 2) (2 * (2 * K + 1))).trans
        ((le_max_left (max (1001 + 2) (2 * (2 * K + 1))) (Fcoef + 2)).trans
          ((le_max_left (max (max (1001 + 2) (2 * (2 * K + 1)))
            (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)).trans hh))
    omega
  have hRbound : R ≤ 1000 * h := by simpa [R, h] using hR
  have hWbound : W ≤ (h : ℝ) ^ 2 := by
    have hcoeff : 1000 * denseRootCoefficient L + 4 ≤ h :=
      (le_max_right (max (max (1001 + 2) (2 * (2 * K + 1)))
        (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)).trans hh
    dsimp [W]
    rw [generalRootMeanFactor_eq_denseRootCoefficient]
    change 2 + (R : ℝ) * (denseRootCoefficient L : ℝ) ≤ (h : ℝ) ^ 2
    have hRreal : (R : ℝ) ≤ 1000 * (h : ℝ) := by exact_mod_cast hRbound
    have hc0 : (0 : ℝ) ≤ denseRootCoefficient L := by positivity
    have hhR : (0 : ℝ) ≤ h := by positivity
    have hcoeffR : (1000 : ℝ) * denseRootCoefficient L + 4 ≤ h := by
      exact_mod_cast hcoeff
    have hRc := mul_le_mul_of_nonneg_right hRreal hc0
    have hch := mul_le_mul_of_nonneg_right hcoeffR hhR
    nlinarith
  have hW0 : 0 ≤ W := generalRootMeanFactor_nonneg _ _
  have hXposNat : 0 < X :=
    (by simp [denseHierarchyX] : 0 < denseHierarchyX N).trans_le hXlower
  have hlogXpos : 0 < Real.log (X : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < X by
      have : 1 < denseHierarchyX N := one_lt_pow₀ (by norm_num) hN.ne'
      omega))
  have hlogXbound : Real.log (X : ℝ) ≤ (h : ℝ) * (N : ℝ) := by
    have hnextpos : (0 : ℝ) < denseHierarchyX (N + 1) := by
      dsimp [denseHierarchyX]
      positivity
    have hlogle : Real.log (X : ℝ) ≤
        Real.log (denseHierarchyX (N + 1) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn
        (show (0 : ℝ) < X by exact_mod_cast hXposNat) hnextpos
        (by exact_mod_cast hXupper)
    have hlognext : Real.log (denseHierarchyX (N + 1) : ℝ) =
        ((N + 1 : ℕ) : ℝ) * Real.log 16 := by
      dsimp [denseHierarchyX]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.log_pow]
    have hlog16lt : Real.log (16 : ℝ) < 4 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      have hlt : Real.log 2 < (1 : ℝ) :=
        Real.log_two_lt_d9.trans (by norm_num)
      simpa using mul_lt_mul_of_pos_left hlt (show (0 : ℝ) < 4 by norm_num)
    have hN1nat : N + 1 ≤ 2 * N := by omega
    have hN1 : (((N + 1 : ℕ) : ℝ)) ≤ 2 * (N : ℝ) := by exact_mod_cast hN1nat
    have hN1pos : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
    have h8h : (8 : ℝ) ≤ h := by exact_mod_cast (show 8 ≤ h by omega)
    rw [hlognext] at hlogle
    calc
      Real.log (X : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * Real.log 16 := hlogle
      _ ≤ ((N + 1 : ℕ) : ℝ) * 4 :=
        mul_le_mul_of_nonneg_left hlog16lt.le hN1pos
      _ ≤ (2 * (N : ℝ)) * 4 := mul_le_mul_of_nonneg_right hN1 (by norm_num)
      _ = 8 * (N : ℝ) := by ring
      _ ≤ (h : ℝ) * (N : ℝ) := mul_le_mul_of_nonneg_right h8h (by positivity)
  have hC0eq : C0 = h ^ 1000 := rfl
  have hFbound : (2 * 1048576 * K : ℝ) / Real.log 2 ≤ (h : ℝ) := by
    have hF : Fcoef + 2 ≤ h :=
      (le_max_right (max (1001 + 2) (2 * (2 * K + 1)))
        (Fcoef + 2)).trans
          ((le_max_left (max (max (1001 + 2) (2 * (2 * K + 1)))
            (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)).trans hh)
    have hlog2half : (1 / 2 : ℝ) < Real.log 2 :=
      (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
    have hKR : (0 : ℝ) ≤ K := by positivity
    have hcast : (Fcoef : ℝ) ≤ h := by exact_mod_cast (show Fcoef ≤ h by omega)
    dsimp [Fcoef] at hcast
    push_cast at hcast
    rw [div_le_iff₀ (Real.log_pos (by norm_num))]
    have hhalf : (2 * 1048576 * (K : ℝ)) ≤ (h : ℝ) / 2 := by
      calc
        2 * 1048576 * (K : ℝ) = (4194304 * (K : ℝ)) / 2 := by ring
        _ ≤ (h : ℝ) / 2 := div_le_div_of_nonneg_right hcast (by norm_num)
    have hhmul : (h : ℝ) / 2 ≤ (h : ℝ) * Real.log 2 := by
      have hh0 : (0 : ℝ) ≤ h := by positivity
      calc
        (h : ℝ) / 2 = (h : ℝ) * (1 / 2) := by ring
        _ ≤ (h : ℝ) * Real.log 2 :=
          mul_le_mul_of_nonneg_left hlog2half.le hh0
    exact hhalf.trans hhmul
  have hV0 : 0 ≤ V := by
    dsimp [V, P]
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hpR).2 (by exact_mod_cast hpprime.one_le)
  have hscaled' : (N : ℝ) * V ≤ (h : ℝ) ^ (100 : ℕ) := by
    simpa [V, P, z, y, h] using hscaledN
  have hEden4 : 4 ≤ Eden := by simpa [Eden, P, z, y] using hE4N
  have hEdenPos : 0 < Eden := lt_of_lt_of_le (by norm_num) hEden4
  have hEplus0 : 0 ≤ Eplus := by dsimp [Eplus]; positivity
  have hA0 : 0 ≤ V * Eplus := mul_nonneg hV0 hEplus0
  have hzlarge : 2 * (2 * K + 1) ≤ z := by
    have hfixed : 2 * (2 * K + 1) ≤ h :=
      (le_max_right (1001 + 2) (2 * (2 * K + 1))).trans
        ((le_max_left (max (1001 + 2) (2 * (2 * K + 1))) (Fcoef + 2)).trans
          ((le_max_left (max (max (1001 + 2) (2 * (2 * K + 1)))
            (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)).trans hh))
    calc
      2 * (2 * K + 1) ≤ h := hfixed
      _ ≤ 16 ^ (h ^ 2) :=
        (hierarchy_self_le_two_pow h).trans <| by
          calc
            2 ^ h ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h
            _ ≤ 16 ^ (h ^ 2) := Nat.pow_le_pow_right (by omega)
              (Nat.le_pow (by omega))
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp; exact prime_of_mem_primeInterval hp
  have hsmall : ∀ p ∈ P,
      2 * (2 * K + 1 : ℕ) * (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hpz := (mem_primeInterval_bounds hp).1
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    rw [show 2 * (2 * K + 1 : ℕ) * (1 / (p : ℝ)) =
      ((2 * (2 * K + 1 : ℕ) : ℕ) : ℝ) / p by push_cast; ring]
    exact (div_le_one hpR).2 (by exact_mod_cast hzlarge.trans hpz.le)
  have hnumPower : (V * Eplus) ^ (K + 1) ≤ V ^ K := by
    have hraw := combinedEulerProduct_pow_le (K + 1) (by omega) P
      (fun p ↦ 1 / (p : ℝ)) (fun p hp ↦ by positivity) (fun p hp ↦ by
        have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
        exact (div_le_one hpR).2 (by exact_mod_cast (hprime p hp).one_le))
    have hEeq : (∏ p ∈ P, (1 + (1 / (p : ℝ)) / ((K + 1 : ℕ) : ℝ))) =
        Eplus := by
      dsimp [Eplus]
      apply Finset.prod_congr rfl
      intro p hp
      congr 1
      field_simp
    change (V * (∏ p ∈ P,
      (1 + (1 / (p : ℝ)) / ((K + 1 : ℕ) : ℝ)))) ^ (K + 1) ≤ V ^ K at hraw
    rw [hEeq] at hraw
    exact hraw
  have hdenPower : 1 ≤ V ^ 2 * Eden ^ (2 * K + 1) := by
    have hraw := one_le_denominatorEulerProduct K (by omega) P
      (fun p ↦ 1 / (p : ℝ)) (fun p hp ↦ by positivity) hsmall
    have hEeq : (∏ p ∈ P, (1 + (1 / (p : ℝ)) / (K : ℝ))) = Eden := by
      dsimp [Eden]
      apply Finset.prod_congr rfl
      intro p hp
      congr 1
      field_simp
    change 1 ≤ V ^ 2 *
      (∏ p ∈ P, (1 + (1 / (p : ℝ)) / (K : ℝ))) ^ (2 * K + 1) at hraw
    rw [hEeq] at hraw
    exact hraw
  have hratioPower : ((V * Eplus) / Eden) ^ M ≤ V ^ (M + 1) := by
    dsimp [M]
    exact hierarchy_euler_ratio_pow_le K (V * Eplus) V Eden
      hA0 hV0 hEdenPos hnumPower hdenPower
  have hMpos : M ≠ 0 := by
    dsimp [M]
    exact Nat.mul_ne_zero (by omega) (by omega)
  have hQ2 : ((2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W *
        ((V * Eplus) / Eden)) ≤
      (N : ℝ) * (h : ℝ) ^ (1005 : ℕ) * ((V * Eplus) / Eden) := by
    have hratio0 : 0 ≤ (V * Eplus) / Eden := div_nonneg hA0 hEdenPos.le
    have hC0R : (C0 : ℝ) = (h : ℝ) ^ (1000 : ℕ) := by
      exact_mod_cast hC0eq
    rw [hC0R]
    calc
      (2 * 1048576 * (K : ℝ) / Real.log 2) * (h : ℝ) ^ 1000 *
          Real.log X * (h : ℝ) * W * ((V * Eplus) / Eden) ≤
        (h : ℝ) * (h : ℝ) ^ 1000 * ((h : ℝ) * (N : ℝ)) *
          (h : ℝ) * ((h : ℝ) ^ 2) * ((V * Eplus) / Eden) := by
            gcongr
      _ = (N : ℝ) * (h : ℝ) ^ 1005 * ((V * Eplus) / Eden) := by ring
  have hQ2nonneg : 0 ≤ ((2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W *
        ((V * Eplus) / Eden)) := by positivity
  have hQ2pow : (((2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W *
        ((V * Eplus) / Eden)) ^ M) ≤ 1 := by
    let Q := (2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W * ((V * Eplus) / Eden)
    have hpowQ := pow_le_pow_left₀ hQ2nonneg hQ2 M
    have hNVpow : ((N : ℝ) * V) ^ (M + 1) ≤
        ((h : ℝ) ^ 100) ^ (M + 1) :=
      pow_le_pow_left₀ (mul_nonneg (by positivity) hV0) hscaled' (M + 1)
    have hbound : (N : ℝ) * Q ^ M ≤ (h : ℝ) ^ Dexp := by
      calc
        (N : ℝ) * Q ^ M ≤ (N : ℝ) *
            ((N : ℝ) * (h : ℝ) ^ 1005 * ((V * Eplus) / Eden)) ^ M :=
          mul_le_mul_of_nonneg_left hpowQ (by positivity)
        _ = (h : ℝ) ^ (1005 * M) * (N : ℝ) ^ (M + 1) *
            (((V * Eplus) / Eden) ^ M) := by ring
        _ ≤ (h : ℝ) ^ (1005 * M) * (N : ℝ) ^ (M + 1) *
            (V ^ (M + 1)) := by gcongr
        _ = (h : ℝ) ^ (1005 * M) * (((N : ℝ) * V) ^ (M + 1)) := by ring
        _ ≤ (h : ℝ) ^ (1005 * M) * (((h : ℝ) ^ 100) ^ (M + 1)) := by
          gcongr
        _ = (h : ℝ) ^ Dexp := by dsimp [Dexp]; ring
    have hDR : (h : ℝ) ^ Dexp ≤ (N : ℝ) := by exact_mod_cast hDpow
    have hNposR : (0 : ℝ) < N := by exact_mod_cast hN
    have hQN : (N : ℝ) * Q ^ M ≤ (N : ℝ) := hbound.trans hDR
    have : Q ^ M ≤ 1 := by nlinarith [mul_pos hNposR (show 0 < (1 : ℝ) by norm_num)]
    simpa [Q]
  have hQ2le : ((2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W *
        ((V * Eplus) / Eden)) ≤ 1 := by
    exact (pow_le_pow_iff_left₀ hQ2nonneg zero_le_one hMpos).mp (by simpa using hQ2pow)
  have hzposNat : 0 < z := by simp [z, denseHierarchyZ]
  have hC0posNat : 0 < C0 := by
    rw [hC0eq]
    exact pow_pos hhpos 1000
  have hDmainPos : 0 < Dmain := by
    dsimp [Dmain]
    positivity
  have hterm2 : (h : ℝ) * U2 ≤ Dmain := by
    let Q := (2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) * W * ((V * Eplus) / Eden)
    have hQ : Q ≤ 1 := by simpa [Q] using hQ2le
    have heq : (h : ℝ) * U2 = Q * Dmain := by
      dsimp [Q, U2, Dmain]
      field_simp [show (Real.log 2) ≠ 0 by positivity,
        show (C0 : ℝ) ≠ 0 by exact_mod_cast hC0posNat.ne',
        show (K : ℝ) ≠ 0 by exact_mod_cast (show 0 < K by omega).ne',
        hlogXpos.ne', hEdenPos.ne']
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hQ hDmainPos.le).trans_eq (one_mul _)
  have hNupper : N ≤ 2 ^ (h + 1) := by
    exact (Nat.lt_pow_succ_log_self (by norm_num) N).le
  have hsmall1Nat : N * h ^ 1003 ≤ z := by
    calc
      N * h ^ 1003 ≤ 2 ^ (h + 1) * 2 ^ h := Nat.mul_le_mul hNupper hpoly
      _ = 2 ^ (2 * h + 1) := by
        rw [← pow_add]
        congr 1
        omega
      _ ≤ 2 ^ (4 * (h * h)) := Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = 16 ^ (h * h) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, pow_mul]
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hQ1coef : (1048576 * (K : ℝ) / Real.log 2) ≤ (h : ℝ) := by
    have hnonneg : (0 : ℝ) ≤ 1048576 * (K : ℝ) / Real.log 2 := by positivity
    calc
      1048576 * (K : ℝ) / Real.log 2 ≤
          2 * (1048576 * (K : ℝ) / Real.log 2) := by nlinarith
      _ = 2 * 1048576 * (K : ℝ) / Real.log 2 := by ring
      _ ≤ (h : ℝ) := hFbound
  have hQ1num : (1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) ≤ (z : ℝ) := by
    have hC0R : (C0 : ℝ) = (h : ℝ) ^ (1000 : ℕ) := by exact_mod_cast hC0eq
    rw [hC0R]
    calc
      (1048576 * (K : ℝ) / Real.log 2) * (h : ℝ) ^ 1000 *
          Real.log X * (h : ℝ) ≤
        (h : ℝ) * (h : ℝ) ^ 1000 * ((h : ℝ) * (N : ℝ)) * (h : ℝ) := by
          gcongr
      _ = (N : ℝ) * (h : ℝ) ^ 1003 := by ring
      _ ≤ (z : ℝ) := by exact_mod_cast hsmall1Nat
  have hterm1 : (h : ℝ) * U1 ≤ Dmain := by
    let Q := ((1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ)) / ((z : ℝ) * Eden)
    have hdenQ : (0 : ℝ) < (z : ℝ) * Eden := by positivity
    have hQ : Q ≤ 1 := by
      dsimp [Q]
      rw [div_le_one hdenQ]
      exact hQ1num.trans (by
        calc
          (z : ℝ) ≤ (z : ℝ) * 4 := by nlinarith
          _ ≤ (z : ℝ) * Eden := mul_le_mul_of_nonneg_left hEden4 (by positivity))
    have heq : (h : ℝ) * U1 = Q * Dmain := by
      dsimp [Q, U1, Dmain]
      field_simp [show (Real.log 2) ≠ 0 by positivity,
        show (C0 : ℝ) ≠ 0 by exact_mod_cast hC0posNat.ne',
        show (K : ℝ) ≠ 0 by exact_mod_cast (show 0 < K by omega).ne',
        hlogXpos.ne', show (z : ℝ) ≠ 0 by exact_mod_cast hzposNat.ne',
        hEdenPos.ne']
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hQ hDmainPos.le).trans_eq (one_mul _)
  have hh6000 : 6000 ≤ h := by
    have hF : Fcoef + 2 ≤ h :=
      (le_max_right (max (1001 + 2) (2 * (2 * K + 1)))
        (Fcoef + 2)).trans
          ((le_max_left (max (max (1001 + 2) (2 * (2 * K + 1)))
            (Fcoef + 2)) (1000 * denseRootCoefficient L + 4)).trans hh)
    dsimp [Fcoef] at hF
    omega
  have hRoneSq : R + 1 ≤ h ^ 2 := by
    calc
      R + 1 ≤ 1001 * h := by nlinarith
      _ ≤ h * h := by nlinarith
      _ = h ^ 2 := by ring
  let Jy := denseUpperExponent N
  have hsixR : 6 * R ≤ h ^ 4 := by
    calc
      6 * R ≤ 6000 * h := by nlinarith
      _ ≤ h * h := by nlinarith
      _ ≤ h ^ 4 := by
        simpa [pow_two] using
          (Nat.pow_le_pow_right (n := h) hhpos (by omega : 2 ≤ 4))
  have hthreeExp : 3 * R * Jy ≤ N / 2 := by
    apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 2)).2
    calc
      3 * R * Jy * 2 = Jy * (6 * R) := by ring
      _ ≤ Jy * h ^ 4 := Nat.mul_le_mul_left Jy hsixR
      _ ≤ N := by
        dsimp [Jy, denseUpperExponent]
        exact Nat.div_mul_le_self N (h ^ 4)
  have hpolyDisc : N * h ^ 1008 ≤ 2 ^ N := by
    have hhN : h ≤ N := Nat.log_le_self 2 N
    calc
      N * h ^ 1008 ≤ N * N ^ 1008 :=
        Nat.mul_le_mul_left N (Nat.pow_le_pow_left hhN 1008)
      _ = N ^ 1009 := by ring
      _ ≤ 2 ^ N := hNpoly
  have htwoNle : 2 ^ N ≤ 16 ^ (N / 2) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    have hNlarge : 6000 ≤ N := hh6000.trans (Nat.log_le_self 2 N)
    omega
  have hhugeDisc : N * h ^ 1008 * y ^ (3 * R) ≤ X := by
    calc
      N * h ^ 1008 * y ^ (3 * R) ≤ 2 ^ N * 16 ^ (N / 2) := by
        apply Nat.mul_le_mul hpolyDisc
        dsimp [y, denseHierarchyY, Jy]
        rw [← pow_mul]
        exact Nat.pow_le_pow_right (by omega) (by simpa [mul_comm] using hthreeExp)
      _ ≤ 16 ^ (N / 2) * 16 ^ (N / 2) :=
        Nat.mul_le_mul_right _ htwoNle
      _ = 16 ^ (2 * (N / 2)) := by rw [← pow_add]; congr 1 <;> omega
      _ ≤ 16 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
      _ = denseHierarchyX N := rfl
      _ ≤ X := hXlower
  have hyRpos : 0 < y ^ R := pow_pos (by simp [y, denseHierarchyY]) R
  have hyone : y ^ R + 1 ≤ h * y ^ R := by
    calc
      y ^ R + 1 ≤ 2 * y ^ R := by omega
      _ ≤ h * y ^ R := Nat.mul_le_mul_right _ (by omega)
  have hdiscNum : (2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) *
      (((R + 1) * y ^ R : ℕ) : ℝ) * W * ((y ^ R : ℕ) : ℝ) *
        ((y ^ R + 1 : ℕ) : ℝ) ≤ (X : ℝ) := by
    have hC0R : (C0 : ℝ) = (h : ℝ) ^ (1000 : ℕ) := by exact_mod_cast hC0eq
    have hfirstCast : (((R + 1) * y ^ R : ℕ) : ℝ) ≤
        (h : ℝ) ^ 2 * (y ^ R : ℕ) := by
      push_cast
      exact mul_le_mul_of_nonneg_right (by exact_mod_cast hRoneSq)
        (by positivity)
    have hlastCast : ((y ^ R + 1 : ℕ) : ℝ) ≤
        (h : ℝ) * (y ^ R : ℕ) := by exact_mod_cast hyone
    rw [hC0R]
    calc
      (2 * 1048576 * (K : ℝ) / Real.log 2) * (h : ℝ) ^ 1000 *
          Real.log X * (h : ℝ) * (((R + 1) * y ^ R : ℕ) : ℝ) * W *
          ((y ^ R : ℕ) : ℝ) * ((y ^ R + 1 : ℕ) : ℝ) ≤
        (h : ℝ) * (h : ℝ) ^ 1000 * ((h : ℝ) * (N : ℝ)) *
          (h : ℝ) * ((h : ℝ) ^ 2 * (y ^ R : ℕ)) * ((h : ℝ) ^ 2) *
          ((y ^ R : ℕ) : ℝ) * ((h : ℝ) * (y ^ R : ℕ)) := by
            gcongr
      _ = (N : ℝ) * (h : ℝ) ^ 1008 * ((y ^ (3 * R) : ℕ) : ℝ) := by
        push_cast
        ring
      _ ≤ (X : ℝ) := by exact_mod_cast hhugeDisc
  have hterm3 : (h : ℝ) * U3 ≤ Dmain := by
    let Q := ((2 * 1048576 * (K : ℝ) / Real.log 2) *
      (C0 : ℝ) * Real.log X * (h : ℝ) *
      (((R + 1) * y ^ R : ℕ) : ℝ) * W * ((y ^ R : ℕ) : ℝ) *
        ((y ^ R + 1 : ℕ) : ℝ)) / ((X : ℝ) * Eden)
    have hdenQ : (0 : ℝ) < (X : ℝ) * Eden := by positivity
    have hQ : Q ≤ 1 := by
      dsimp [Q]
      rw [div_le_one hdenQ]
      exact hdiscNum.trans (by
        calc
          (X : ℝ) ≤ (X : ℝ) * 4 := by nlinarith
          _ ≤ (X : ℝ) * Eden := mul_le_mul_of_nonneg_left hEden4 (by positivity))
    have heq : (h : ℝ) * U3 = Q * Dmain := by
      dsimp [Q, U3, Dmain]
      field_simp [show (Real.log 2) ≠ 0 by positivity,
        show (C0 : ℝ) ≠ 0 by exact_mod_cast hC0posNat.ne',
        show (K : ℝ) ≠ 0 by exact_mod_cast (show 0 < K by omega).ne',
        hlogXpos.ne', show (X : ℝ) ≠ 0 by exact_mod_cast hXposNat.ne',
        hEdenPos.ne']
    rw [heq]
    exact (mul_le_mul_of_nonneg_right hQ hDmainPos.le).trans_eq (one_mul _)
  have hnum' : (∑ n ∈ Finset.Icc 1 X, (t (K + 1) n : ℝ)) ≤ U1 + U2 + U3 := by
    simpa [L, z, y, R, P, V, Eplus, W, U1, U2, U3] using hnum
  have hden' : Dmain ≤ ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
    simpa [P, Eden, C0, Dmain] using hden
  have hhsum := mul_le_mul_of_nonneg_left hnum' (show (0 : ℝ) ≤ h by positivity)
  calc
    (h : ℝ) * (∑ n ∈ Finset.Icc 1 X, (t (K + 1) n : ℝ)) ≤
        (h : ℝ) * (U1 + U2 + U3) := hhsum
    _ = (h : ℝ) * U1 + (h : ℝ) * U2 + (h : ℝ) * U3 := by ring
    _ ≤ Dmain + Dmain + Dmain := add_le_add (add_le_add hterm1 hterm2) hterm3
    _ = 3 * Dmain := by ring
    _ ≤ 3 * (∑ n ∈ Finset.Icc 1 X, (t K n : ℝ)) :=
      mul_le_mul_of_nonneg_left hden' (by norm_num)

/-- Dense-grid specialization of the uniform adjacent comparison. -/
theorem eventually_dense_adjacent_three_mul_bound (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      (denseHierarchyLog N : ℝ) *
          (∑ n ∈ Finset.Icc 1 (denseHierarchyX N), (t (K + 1) n : ℝ)) ≤
        3 * (∑ n ∈ Finset.Icc 1 (denseHierarchyX N), (t K n : ℝ)) := by
  filter_upwards [eventually_dense_adjacent_three_mul_bound_uniform K hK]
    with N hN
  exact hN (denseHierarchyX N) le_rfl
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))

end Erdos394
