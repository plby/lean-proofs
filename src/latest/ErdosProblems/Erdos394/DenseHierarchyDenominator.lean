import ErdosProblems.Erdos394.DenseEulerBounds
import ErdosProblems.Erdos394.DenominatorEulerLower

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Denominator lower bound on the dense hierarchy grid
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

/-- A deliberately generous polynomial dilution for the moving denominator
construction. -/
def denseDenominatorDilution (N : ℕ) : ℕ := denseHierarchyLog N ^ 1000

set_option maxRecDepth 20000 in
set_option maxHeartbeats 2000000 in
/-- F-090 specialized to the dense hierarchy, uniformly for cutoffs in the
next dense-grid interval. -/
theorem eventually_dense_hierarchy_denominator_bound_uniform
    (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop, ∀ X : ℕ,
      denseHierarchyX N ≤ X → X ≤ denseHierarchyX (N + 1) →
      let P := primeInterval (denseHierarchyZ N) (denseHierarchyY N)
      let E := ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))
      (Real.log 2 * (X : ℝ) ^ 2 /
          (1048576 * (denseDenominatorDilution N : ℝ) *
            (K : ℝ) * Real.log X)) * E ≤
        ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
  obtain ⟨Jmin, hJmin, hbrun⟩ := exists_geometric_primeInterval_brun_tail
  have hrecipAll := eventually_primeReciprocal_block_lower
  rw [eventually_atTop] at hrecipAll
  obtain ⟨B0, hrecipB0⟩ := hrecipAll
  have horder := eventually_denseHierarchyOrder_le
  have hzy := eventually_denseLower_le_upper
  have hJyMin := tendsto_denseUpperExponent_atTop.eventually
    (eventually_ge_atTop (max Jmin B0))
  have hhFixed := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max Jmin B0))
  have hscaled := eventually_dense_primeInterval_euler_scaled
  have hcut := eventually_dense_denominator_truncation K hK
  have hE4 := eventually_four_le_dense_denominatorEuler K hK
  have hhlarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max (max (max 262144 6000) (K + 2)) 4))
  have hpoly1000 := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_nat_pow_le_two_pow 1000)
  have hKsmall := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_const_le_two_pow K)
  have hKbase := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_const_le_two_pow (K ^ 1000))
  have hN3 := eventually_nat_pow_le_two_pow 3
  have hNlarge : ∀ᶠ N : ℕ in atTop, 2097152 * 1001 ≤ N :=
    eventually_ge_atTop _
  filter_upwards [eventually_gt_atTop 0, horder, hzy, hJyMin, hhFixed,
    hscaled, hcut, hE4, hhlarge, hpoly1000, hKsmall, hKbase,
    hN3, hNlarge] with N hN hR hzyN hJyMinN hhFixedN hscaledN hcutN hE4N
      hh hpoly hKtwo hK1000 hNpow hNcoef
  intro X hXlower hXupper
  let h := denseHierarchyLog N
  let Jz := denseLowerExponent N
  let Jy := denseUpperExponent N
  let z := denseHierarchyZ N
  let y := denseHierarchyY N
  let R := denseHierarchyOrder N
  let C0 := denseDenominatorDilution N
  let P := primeInterval z y
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let E := ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))
  have hh262 : 262144 ≤ h :=
    (le_max_left 262144 6000).trans
      ((le_max_left (max 262144 6000) (K + 2)).trans
        ((le_max_left (max (max 262144 6000) (K + 2)) 4).trans hh))
  have hh6000 : 6000 ≤ h :=
    (le_max_right 262144 6000).trans
      ((le_max_left (max 262144 6000) (K + 2)).trans
        ((le_max_left (max (max 262144 6000) (K + 2)) 4).trans hh))
  have hhK : K + 2 ≤ h :=
    (le_max_right (max 262144 6000) (K + 2)).trans
      ((le_max_left (max (max 262144 6000) (K + 2)) 4).trans hh)
  have hh4 : 4 ≤ h :=
    (le_max_right (max (max 262144 6000) (K + 2)) 4).trans hh
  have hhpos : 0 < h := by omega
  have hRbound : R ≤ 1000 * h := by simpa [R, h] using hR
  have hRone : R + 1 ≤ 1001 * h := by nlinarith
  have hJzMin : Jmin ≤ Jz := by
    calc
      Jmin ≤ h := (le_max_left Jmin B0).trans hhFixedN
      _ ≤ h ^ 2 := Nat.le_pow (by omega)
      _ = Jz := rfl
  have hzyNat : z ≤ y := by
    dsimp [z, y, denseHierarchyZ, denseHierarchyY]
    exact Nat.pow_le_pow_right (by omega) hzyN
  have hzpos : 0 < z := by simp [z, denseHierarchyZ]
  have hypos : 0 < y := by simp [y, denseHierarchyY]
  have hXpos : 0 < X := (by simp [denseHierarchyX] : 0 < denseHierarchyX N).trans_le hXlower
  have hC0pos : 0 < C0 := by
    dsimp [C0, denseDenominatorDilution]
    exact pow_pos hhpos 1000
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeInterval hp
  have hPbounds : ∀ p ∈ P, z < p ∧ p ≤ y := by
    intro p hp
    exact mem_primeInterval_bounds hp
  have hKlarge : ∀ p ∈ P, K < p := by
    intro p hp
    have hpz := (hPbounds p hp).1
    have hKz : K < z := by
      calc
        K < h := by omega
        _ ≤ 16 ^ (h ^ 2) :=
          (hierarchy_self_le_two_pow h).trans <| by
            calc
              2 ^ h ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h
              _ ≤ 16 ^ (h ^ 2) := Nat.pow_le_pow_right (by omega)
                (Nat.le_pow (by omega))
        _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
    exact hKz.trans hpz
  have htail :
      (∑ p ∈ P, (1 / (p : ℝ))) ^ (R + 1) /
          ((R + 1).factorial : ℝ) ≤ V := by
    dsimp [P, V, R, z, y, denseHierarchyZ, denseHierarchyY]
    exact hbrun Jz Jy hJzMin hzyN
  have hReven : Even R := by
    dsimp [R]
    exact denseHierarchyOrder_even N
  have hC02 : C0 ≤ 2 ^ (h * h) := by
    calc
      C0 = h ^ 1000 := rfl
      _ ≤ 2 ^ h := hpoly
      _ ≤ 2 ^ (h * h) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have htwo2 : 2 ≤ 2 ^ (h * h) := by
    exact (show 2 = 2 ^ 1 by norm_num) ▸
      Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hKpow : K ^ (R + 1) ≤ 2 ^ (2 * (h * h)) := by
    calc
      K ^ (R + 1) ≤ K ^ (1000 * h + 1) :=
        Nat.pow_le_pow_right (by omega) (by nlinarith)
      _ = K * (K ^ 1000) ^ h := by
        rw [pow_add, ← pow_mul]
        ring
      _ ≤ 2 ^ h * (2 ^ h) ^ h :=
        Nat.mul_le_mul hKtwo (Nat.pow_le_pow_left hK1000 h)
      _ = 2 ^ (h + h * h) := by rw [← pow_mul, ← pow_add]
      _ ≤ 2 ^ (2 * (h * h)) := Nat.pow_le_pow_right (by omega) (by nlinarith)
  have hcanonicalHorizon : ∀ T ∈ denominatorSelectedSubsets P R,
      2 * (C0 * K ^ (T.card + 1)) ≤ primeProduct T := by
    intro T hT
    have hmem := mem_denominatorSelectedSubsets_iff.mp hT
    have hcard : T.card ≤ R := hmem.2.1
    have hcardpos : 0 < T.card := Finset.card_pos.mpr
      (Finset.nonempty_iff_ne_empty.mpr hmem.2.2)
    have hqLower : z ≤ primeProduct T := by
      calc
        z ≤ z ^ T.card := Nat.le_pow hcardpos
        _ ≤ primeProduct T := pow_card_le_primeProduct_of_le z T (fun p hp ↦
          (hPbounds p (hmem.1 hp)).1.le)
    have hKcard : K ^ (T.card + 1) ≤ 2 ^ (2 * (h * h)) :=
      (Nat.pow_le_pow_right (by omega) (Nat.add_le_add_right hcard 1)).trans hKpow
    calc
      2 * (C0 * K ^ (T.card + 1)) ≤
          2 ^ (h * h) * (2 ^ (h * h) * 2 ^ (2 * (h * h))) :=
        Nat.mul_le_mul htwo2 (Nat.mul_le_mul hC02 hKcard)
      _ = 2 ^ (4 * (h * h)) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
      _ = 16 ^ (h * h) := by
        rw [show (16 : ℕ) = 2 ^ 4 by norm_num, pow_mul]
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
      _ ≤ primeProduct T := hqLower
  have htwoRexp : 2 * (Jy * (R + 1)) ≤ N := by
    have hcoeff : 2 * (R + 1) ≤ h ^ 4 := by
      calc
        2 * (R + 1) ≤ 2002 * h := by nlinarith
        _ ≤ h * h := by nlinarith
        _ ≤ h ^ 4 := by
          simpa [pow_two] using
            (Nat.pow_le_pow_right (n := h) hhpos (by omega : 2 ≤ 4))
    have hdivmul : Jy * h ^ 4 ≤ N := by
      dsimp [Jy, denseUpperExponent]
      exact Nat.div_mul_le_self N (h ^ 4)
    calc
      2 * (Jy * (R + 1)) = Jy * (2 * (R + 1)) := by ring
      _ ≤ Jy * h ^ 4 := Nat.mul_le_mul_left Jy hcoeff
      _ ≤ N := hdivmul
  have hwideExponent : 2 + Jy * (R + 1) ≤ N := by omega
  have hwide : 64 * y ^ (R + 1) ≤ X := by
    calc
      64 * y ^ (R + 1) ≤ 16 ^ 2 * (16 ^ Jy) ^ (R + 1) := by
        dsimp [y, denseHierarchyY, Jy]
        exact Nat.mul_le_mul (by norm_num) le_rfl
      _ = 16 ^ (2 + Jy * (R + 1)) := by rw [← pow_mul, ← pow_add]
      _ ≤ 16 ^ N := Nat.pow_le_pow_right (by omega) hwideExponent
      _ = denseHierarchyX N := rfl
      _ ≤ X := hXlower
  have hylarg : max B0 (2 * K) ≤ y := by
    have hJyB : max B0 (2 * K) ≤ Jy := by
      have hB : B0 ≤ Jy := (le_max_right Jmin B0).trans hJyMinN
      have h2K : 2 * K ≤ Jy := by
        calc
          2 * K ≤ h * h := by nlinarith
          _ = Jz := by simp [Jz, denseLowerExponent, h, pow_two]
          _ ≤ Jy := hzyN
      exact max_le hB h2K
    exact hJyB.trans <| by
      calc
        Jy ≤ 2 ^ Jy := hierarchy_self_le_two_pow Jy
        _ ≤ 16 ^ Jy := Nat.pow_le_pow_left (by norm_num) Jy
        _ = y := rfl
  have hqUpper : ∀ T ∈ denominatorSelectedSubsets P R,
      primeProduct T ≤ y ^ R := by
    intro T hT
    have hmem := mem_denominatorSelectedSubsets_iff.mp hT
    calc
      primeProduct T ≤ y ^ T.card :=
        primeProduct_le_pow_card T (fun p hp ↦ (hPbounds p (hmem.1 hp)).2)
      _ ≤ y ^ R := Nat.pow_le_pow_right (by omega) hmem.2.1
  have hcanonicalX : ∀ T ∈ denominatorSelectedSubsets P R,
      64 * primeProduct T ≤ X := by
    intro T hT
    calc
      64 * primeProduct T ≤ 64 * y ^ R := Nat.mul_le_mul_left 64 (hqUpper T hT)
      _ ≤ 64 * y ^ (R + 1) := Nat.mul_le_mul_left 64
        (Nat.pow_le_pow_right (by omega) (Nat.le_succ R))
      _ ≤ X := hwide
  have hbaseAbove : ∀ T ∈ denominatorSelectedSubsets P R,
      y < selectedPrimeBase X T := by
    intro T hT
    have hqpos : 0 < primeProduct T := by
      unfold primeProduct
      exact Finset.prod_pos fun p hp ↦ (hprime p
        ((mem_denominatorSelectedSubsets_iff.mp hT).1 hp)).pos
    have hq := hqUpper T hT
    have hmul : (y + 1) * (32 * primeProduct T) ≤ X := by
      calc
        (y + 1) * (32 * primeProduct T) ≤ (2 * y) * (32 * y ^ R) := by
          apply Nat.mul_le_mul
          · omega
          · exact Nat.mul_le_mul_left 32 hq
        _ = 64 * y ^ (R + 1) := by rw [pow_succ]; ring
        _ ≤ X := hwide
    have hbase : y + 1 ≤ X / (32 * primeProduct T) :=
      (Nat.le_div_iff_mul_le (by positivity)).2 hmul
    dsimp [selectedPrimeBase]
    omega
  have hheight : ∀ T ∈ denominatorSelectedSubsets P R,
      2 * K ≤ selectedHorizon K C0 T * selectedPrimeBase X T := by
    intro T hT
    have hhor := hcanonicalHorizon T hT
    have hdenpos : 0 < C0 * K ^ (T.card + 1) := by positivity
    have hYtwo : 2 ≤ selectedHorizon K C0 T := by
      dsimp [selectedHorizon]
      exact (Nat.le_div_iff_mul_le hdenpos).2 hhor
    have hNtwoK : 2 * K ≤ selectedPrimeBase X T := by
      calc
        2 * K ≤ y := (le_max_right B0 (2 * K)).trans hylarg
        _ ≤ selectedPrimeBase X T := (hbaseAbove T hT).le
    exact hNtwoK.trans (Nat.le_mul_of_pos_left _ (by omega :
      0 < selectedHorizon K C0 T))
  have hrecip : ∀ T ∈ denominatorSelectedSubsets P R,
      Real.log 2 / (16 * Real.log (selectedPrimeBase X T)) ≤
        primeReciprocalSum (16 * selectedPrimeBase X T) -
          primeReciprocalSum (selectedPrimeBase X T) := by
    intro T hT
    apply hrecipB0
    exact (le_max_left B0 (2 * K)).trans (hylarg.trans_lt (hbaseAbove T hT)).le
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
  have hCbigNat : 2 * 131072 * h ^ 100 ≤ C0 := by
    have hcoef900 : 2 * 131072 ≤ h ^ 900 := by
      calc
        2 * 131072 ≤ h := by omega
        _ ≤ h ^ 900 := Nat.le_pow (by omega)
    calc
      2 * 131072 * h ^ 100 ≤ h ^ 900 * h ^ 100 :=
        Nat.mul_le_mul_right _ hcoef900
      _ = h ^ 1000 := by ring
      _ = C0 := rfl
  have hCbig : (131072 : ℝ) * (h : ℝ) ^ (100 : ℕ) ≤
      Real.log 2 * (C0 : ℝ) := by
    have hc : (2 : ℝ) * 131072 * (h : ℝ) ^ (100 : ℕ) ≤ C0 := by
      exact_mod_cast hCbigNat
    nlinarith [Real.log_two_gt_d9,
      show (0 : ℝ) ≤ (h : ℝ) ^ (100 : ℕ) by positivity]
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
  have hpolyN : 2097152 * N * (R + 1) ≤ 2 ^ N := by
    have hRN : R + 1 ≤ 1001 * N := by
      exact hRone.trans (Nat.mul_le_mul_left 1001 (Nat.log_le_self 2 N))
    calc
      2097152 * N * (R + 1) ≤ 2097152 * N * (1001 * N) :=
        Nat.mul_le_mul_left (2097152 * N) hRN
      _ = (2097152 * 1001) * N ^ 2 := by ring
      _ ≤ N * N ^ 2 := Nat.mul_le_mul_right _ hNcoef
      _ = N ^ 3 := by ring
      _ ≤ 2 ^ N := hNpow
  have htwoN_le : 2 ^ N ≤ 16 ^ (N / 2) := by
    rw [show (16 : ℕ) = 2 ^ 4 by norm_num, ← pow_mul]
    apply Nat.pow_le_pow_right (by omega)
    omega
  have hhuge : 2097152 * N * (R + 1) * y ^ (3 * R) ≤ X := by
    calc
      2097152 * N * (R + 1) * y ^ (3 * R) ≤
          2 ^ N * 16 ^ (N / 2) := by
        apply Nat.mul_le_mul hpolyN
        dsimp [y, denseHierarchyY]
        rw [← pow_mul]
        apply Nat.pow_le_pow_right (by omega)
        simpa [mul_comm] using hthreeExp
      _ ≤ 16 ^ (N / 2) * 16 ^ (N / 2) :=
        Nat.mul_le_mul_right _ htwoN_le
      _ = 16 ^ (2 * (N / 2)) := by rw [← pow_add]; congr 1 <;> omega
      _ ≤ 16 ^ N := Nat.pow_le_pow_right (by omega) (by omega)
      _ = denseHierarchyX N := rfl
      _ ≤ X := hXlower
  have hbad : ∀ T ∈ denominatorSelectedSubsets P R, 2 *
      ((((16 * selectedPrimeBase X T : ℕ) : ℝ) ^ 2 /
          (C0 : ℝ)) * V +
        ((primeProduct T : ℝ) / (C0 : ℝ)) *
          ((truncatedSubsets (P \ T) R).card : ℝ) *
            (2 * ((16 * selectedPrimeBase X T : ℕ) : ℝ))) ≤
      Real.log 2 * (selectedPrimeBase X T : ℝ) ^ 2 /
        (16 * Real.log (selectedPrimeBase X T)) := by
    intro T hT
    let q := primeProduct T
    let B := selectedPrimeBase X T
    let A := (truncatedSubsets (P \ T) R).card
    have hmem := mem_denominatorSelectedSubsets_iff.mp hT
    have hqposNat : 0 < q := by
      dsimp [q, primeProduct]
      exact Finset.prod_pos fun p hp ↦ (hprime p (hmem.1 hp)).pos
    have hqpos : (0 : ℝ) < q := by exact_mod_cast hqposNat
    have hBabove : y < B := hbaseAbove T hT
    have hBposNat : 0 < B := by omega
    have hBpos : (0 : ℝ) < B := by exact_mod_cast hBposNat
    have hBlog : 0 < Real.log (B : ℝ) :=
      Real.log_pos (by exact_mod_cast (show 1 < B by omega))
    have hBX : B ≤ X := by
      dsimp [B, selectedPrimeBase]
      exact Nat.div_le_self X (32 * primeProduct T)
    have hBnext : B ≤ denseHierarchyX (N + 1) := hBX.trans hXupper
    have hlogBnext : Real.log (B : ℝ) ≤
        Real.log (denseHierarchyX (N + 1) : ℝ) :=
      Real.strictMonoOn_log.monotoneOn hBpos
        (show (0 : ℝ) < denseHierarchyX (N + 1) by
          dsimp [denseHierarchyX]
          positivity)
        (by exact_mod_cast hBnext)
    have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
      rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
      norm_num
    have hlogNext : Real.log (denseHierarchyX (N + 1) : ℝ) =
        (N + 1 : ℕ) * Real.log 16 := by
      dsimp [denseHierarchyX]
      norm_num only [Nat.cast_pow, Nat.cast_ofNat]
      rw [Real.log_pow]
    have hlogB8N : Real.log (B : ℝ) ≤ 8 * (N : ℝ) := by
      rw [hlogNext, hlog16] at hlogBnext
      have hlog2lt : Real.log 2 < 1 := Real.log_two_lt_d9.trans (by norm_num)
      have hN1nat : N + 1 ≤ 2 * N := by omega
      have hN1 : ((N + 1 : ℕ) : ℝ) ≤ 2 * (N : ℝ) := by exact_mod_cast hN1nat
      have hN1pos : (0 : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by positivity
      calc
        Real.log (B : ℝ) ≤ ((N + 1 : ℕ) : ℝ) * (4 * Real.log 2) := hlogBnext
        _ ≤ ((N + 1 : ℕ) : ℝ) * 4 :=
          mul_le_mul_of_nonneg_left (by nlinarith : 4 * Real.log 2 ≤ (4 : ℝ)) hN1pos
        _ ≤ (2 * (N : ℝ)) * 4 := mul_le_mul_of_nonneg_right hN1 (by norm_num)
        _ = 8 * (N : ℝ) := by ring
    have hVlog : V * Real.log (B : ℝ) ≤ 8 * (h : ℝ) ^ (100 : ℕ) := by
      have hlogmul := mul_le_mul_of_nonneg_left hlogB8N hV0
      have hNV8 : 8 * ((N : ℝ) * V) ≤ 8 * (h : ℝ) ^ (100 : ℕ) :=
        mul_le_mul_of_nonneg_left hscaled' (by norm_num)
      nlinarith
    have hfirstScale : 16384 * V * Real.log (B : ℝ) ≤
        Real.log 2 * (C0 : ℝ) := by
      nlinarith [mul_le_mul_of_nonneg_left hVlog (by norm_num : (0 : ℝ) ≤ 16384)]
    have hfirst : 4 * ((((16 * B : ℕ) : ℝ) ^ 2 / (C0 : ℝ)) * V) ≤
        Real.log 2 * (B : ℝ) ^ 2 / (16 * Real.log B) := by
      have hC0R : (0 : ℝ) < C0 := by exact_mod_cast hC0pos
      have hdenR : (0 : ℝ) < 16 * Real.log (B : ℝ) := by positivity
      rw [show 4 * ((((16 * B : ℕ) : ℝ) ^ 2 / (C0 : ℝ)) * V) =
        (1024 * (B : ℝ) ^ 2 * V) / (C0 : ℝ) by push_cast; ring]
      rw [div_le_div_iff₀ hC0R hdenR]
      have hs := mul_le_mul_of_nonneg_right hfirstScale
        (show 0 ≤ (B : ℝ) ^ 2 by positivity)
      nlinarith
    have hAupperNat : A ≤ (R + 1) * y ^ R := by
      dsimp [A]
      apply card_truncatedSubsets_le (P \ T) R y (by omega)
      exact (Finset.card_le_card (Finset.sdiff_subset)).trans
        (card_primeInterval_le hypos)
    have hqUpperT : q ≤ y ^ R := by simpa [q] using hqUpper T hT
    have hq2A : q ^ 2 * A ≤ (R + 1) * y ^ (3 * R) := by
      calc
        q ^ 2 * A ≤ (y ^ R) ^ 2 * ((R + 1) * y ^ R) :=
          Nat.mul_le_mul (Nat.pow_le_pow_left hqUpperT 2) hAupperNat
        _ = (R + 1) * y ^ (3 * R) := by ring
    have hlargeSuff : (131072 : ℝ) * (q : ℝ) ^ 2 * (A : ℝ) *
        Real.log (B : ℝ) ≤ Real.log 2 * (C0 : ℝ) * (X : ℝ) := by
      have hleftNat : 2097152 * N * (q ^ 2 * A) ≤ X := by
        calc
          2097152 * N * (q ^ 2 * A) ≤
              2097152 * N * ((R + 1) * y ^ (3 * R)) :=
            Nat.mul_le_mul_left (2097152 * N) hq2A
          _ = 2097152 * N * (R + 1) * y ^ (3 * R) := by ring
          _ ≤ X := hhuge
      have hleftR : (2097152 : ℝ) * (N : ℝ) *
          ((q : ℝ) ^ 2 * (A : ℝ)) ≤ (X : ℝ) := by exact_mod_cast hleftNat
      have hlognonneg : 0 ≤ Real.log (B : ℝ) := hBlog.le
      have htemp := mul_le_mul_of_nonneg_left hlogB8N
        (show 0 ≤ (131072 : ℝ) * (q : ℝ) ^ 2 * (A : ℝ) by positivity)
      have hhalfX : (131072 : ℝ) * (q : ℝ) ^ 2 * (A : ℝ) *
          Real.log (B : ℝ) ≤ (X : ℝ) / 2 := by
        nlinarith
      have hC01 : (1 : ℝ) ≤ C0 := by exact_mod_cast (show 1 ≤ C0 by omega)
      have hlog2half : (1 / 2 : ℝ) < Real.log 2 :=
        (by norm_num : (1 / 2 : ℝ) < 0.6931471803).trans Real.log_two_gt_d9
      have hright : (X : ℝ) / 2 ≤ Real.log 2 * (C0 : ℝ) * X := by
        have hXR : (0 : ℝ) ≤ X := by positivity
        have hlog2pos : 0 < Real.log 2 := Real.log_pos (by norm_num)
        have hcoeff : (1 / 2 : ℝ) ≤ Real.log 2 * (C0 : ℝ) := by
          have hm := mul_le_mul_of_nonneg_left hC01 hlog2pos.le
          nlinarith
        nlinarith [mul_le_mul_of_nonneg_right hcoeff hXR]
      exact hhalfX.trans hright
    have hNlower : (X : ℝ) / (64 * (q : ℝ)) ≤ (B : ℝ) := by
      dsimp [q, B]
      exact primeBase_floor_lower X (primeProduct T) hqposNat
        (hcanonicalX T hT)
    have hsecondScale : 2048 * (q : ℝ) * (A : ℝ) * Real.log (B : ℝ) ≤
        Real.log 2 * (C0 : ℝ) * (B : ℝ) := by
      have hdenq : (0 : ℝ) < 64 * (q : ℝ) := by positivity
      have hsdiv := div_le_div_of_nonneg_right hlargeSuff hdenq.le
      have hcoefnonneg : 0 ≤ Real.log 2 * (C0 : ℝ) := by positivity
      have hrightLower := mul_le_mul_of_nonneg_left hNlower hcoefnonneg
      calc
        2048 * (q : ℝ) * (A : ℝ) * Real.log (B : ℝ) =
            ((131072 : ℝ) * (q : ℝ) ^ 2 * (A : ℝ) *
              Real.log (B : ℝ)) / (64 * (q : ℝ)) := by
          field_simp [hqpos.ne']
          ring
        _ ≤ (Real.log 2 * (C0 : ℝ) * (X : ℝ)) /
            (64 * (q : ℝ)) := hsdiv
        _ = (Real.log 2 * (C0 : ℝ)) *
            ((X : ℝ) / (64 * (q : ℝ))) := by ring
        _ ≤ (Real.log 2 * (C0 : ℝ)) * (B : ℝ) := hrightLower
    have hsecond : 4 * (((q : ℝ) / (C0 : ℝ)) * (A : ℝ) *
          (2 * ((16 * B : ℕ) : ℝ))) ≤
        Real.log 2 * (B : ℝ) ^ 2 / (16 * Real.log B) := by
      have hC0R : (0 : ℝ) < C0 := by exact_mod_cast hC0pos
      have hdenR : (0 : ℝ) < 16 * Real.log (B : ℝ) := by positivity
      rw [show 4 * (((q : ℝ) / (C0 : ℝ)) * (A : ℝ) *
          (2 * ((16 * B : ℕ) : ℝ))) =
        (128 * (q : ℝ) * (A : ℝ) * (B : ℝ)) / (C0 : ℝ) by push_cast; ring]
      rw [div_le_div_iff₀ hC0R hdenR]
      have hs := mul_le_mul_of_nonneg_right hsecondScale
        (show 0 ≤ (B : ℝ) by positivity)
      nlinarith
    dsimp [q, B, A] at hfirst hsecond ⊢
    nlinarith
  have hselected := sum_canonical_selected_main_le_full_tSum
    P K C0 X R y R (by omega) hC0pos hprime hKlarge
    (fun p hp ↦ (hPbounds p hp).2) hReven htail hbaseAbove hheight hrecip hbad
  have hXlog : 1 < X :=
    (one_lt_pow₀ (by norm_num) hN.ne' : 1 < denseHierarchyX N).trans_le hXlower
  have hden := denominatorEulerProduct_lower_of_selected_sum
    P K C0 X R (by omega) hC0pos hXlog hprime
    hcanonicalHorizon hcanonicalX hcutN hE4N hselected
  simpa [P, E, C0] using hden

/-- Dense-grid specialization of the uniform denominator bound. -/
theorem eventually_dense_hierarchy_denominator_bound (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      let X := denseHierarchyX N
      let P := primeInterval (denseHierarchyZ N) (denseHierarchyY N)
      let E := ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))
      (Real.log 2 * (X : ℝ) ^ 2 /
          (1048576 * (denseDenominatorDilution N : ℝ) *
            (K : ℝ) * Real.log X)) * E ≤
        ∑ n ∈ Finset.Icc 1 X, (t K n : ℝ) := by
  filter_upwards [eventually_dense_hierarchy_denominator_bound_uniform K hK]
    with N hN
  exact hN (denseHierarchyX N) le_rfl
    (Nat.pow_le_pow_right (by norm_num) (Nat.le_succ N))

end Erdos394
