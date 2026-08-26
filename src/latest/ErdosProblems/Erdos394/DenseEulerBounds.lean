import ErdosProblems.Erdos394.DenseHierarchyParameters
import ErdosProblems.Erdos394.EndpointEulerLower
import ErdosProblems.Erdos394.PrimeReciprocal
import ErdosProblems.Erdos394.HierarchyNumerator

set_option backward.defeqAttrib.useBackward true
set_option backward.isDefEq.respectTransparency false

/-!
# Euler bounds on the dense hierarchy interval
-/

open Nat Finset Filter Asymptotics
open scoped Topology

namespace Erdos394

set_option maxRecDepth 10000 in
/-- The medium-prime Euler density on the dense hierarchy interval is at most
`h^100/N`.  The intentionally generous exponent absorbs the fixed endpoint
constant and all floor losses. -/
theorem eventually_dense_primeInterval_euler_scaled :
    ∀ᶠ N : ℕ in atTop,
      (N : ℝ) * localEulerProduct
          (primeInterval (denseHierarchyZ N) (denseHierarchyY N))
          (fun p ↦ 1 / (p : ℝ)) ≤
        (denseHierarchyLog N : ℝ) ^ (100 : ℕ) := by
  obtain ⟨J0, c, hJ0, hc, hendpoint⟩ :=
    exists_geometric_endpoint_primeEuler_lower
  let A : ℝ := c * Real.exp (-24)
  have hA : 0 < A := mul_pos hc (Real.exp_pos _)
  let B : ℕ := ⌈1 / A⌉₊ + 1
  have hhlarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max (max B 2) J0))
  have h5 := eventually_denseLog_pow_le 5
  have hzy := eventually_denseLower_le_upper
  filter_upwards [eventually_gt_atTop 0, hhlarge, h5, hzy] with N hN hh hpow hJzy
  let h := denseHierarchyLog N
  let Jz := denseLowerExponent N
  let Jy := denseUpperExponent N
  let z := denseHierarchyZ N
  let y := denseHierarchyY N
  let V := localEulerProduct (primeInterval z y) (fun p ↦ 1 / (p : ℝ))
  have hh2 : 2 ≤ h := (le_max_right B 2).trans
    ((le_max_left (max B 2) J0).trans hh)
  have hhB : B ≤ h := (le_max_left B 2).trans
    ((le_max_left (max B 2) J0).trans hh)
  have hJz0 : J0 ≤ Jz := by
    calc
      J0 ≤ h := (le_max_right (max B 2) J0).trans hh
      _ ≤ h ^ 2 := Nat.le_pow (by omega)
      _ = Jz := rfl
  have hhpos : 0 < h := by omega
  have htwoh4 : 2 * h ^ 4 ≤ N := by
    calc
      2 * h ^ 4 ≤ h ^ 5 := by
        calc
          2 * h ^ 4 ≤ h * h ^ 4 := Nat.mul_le_mul_right _ hh2
          _ = h ^ 5 := by ring
      _ ≤ N := hpow
  have hJypos : 0 < Jy := by
    dsimp [Jy, denseUpperExponent]
    apply Nat.div_pos
    · exact (show h ^ 4 ≤ N by omega)
    · exact pow_pos hhpos 4
  have hNle : (N : ℝ) ≤ 2 * (Jy : ℝ) * (h : ℝ) ^ 4 := by
    have hf := half_real_div_le_cast_nat_div
      (a := N) (d := h ^ 4) (pow_pos hhpos 4) htwoh4
    dsimp [Jy, denseUpperExponent]
    push_cast at hf ⊢
    have hd : (0 : ℝ) < (h : ℝ) ^ 4 := by positivity
    rw [div_le_iff₀ (by positivity : (0 : ℝ) < 2 * (h : ℝ) ^ 4)] at hf
    nlinarith
  have hzpos : 0 < z := by simp [z, denseHierarchyZ]
  have hzyNat : z ≤ y := by
    dsimp [z, y, denseHierarchyZ, denseHierarchyY]
    exact Nat.pow_le_pow_right (by omega) hJzy
  have hJzpos : (0 : ℝ) < Jz := by
    exact_mod_cast (show 0 < Jz by dsimp [Jz, denseLowerExponent]; positivity)
  have hCeq : c * Real.exp (-24 * (1 + Real.log (Jz : ℝ))) =
      A / (h : ℝ) ^ (48 : ℕ) := by
    rw [exp_neg_twentyfour_one_add_log_eq (Jz : ℝ) hJzpos]
    dsimp [A, Jz, denseLowerExponent]
    push_cast
    rw [show ((h : ℝ) ^ 2) ^ (24 : ℕ) = (h : ℝ) ^ (48 : ℕ) by ring]
    ring
  have hCpos : 0 < A / (h : ℝ) ^ (48 : ℕ) := by positivity
  have hlow : A / (h : ℝ) ^ (48 : ℕ) ≤
      localEulerProduct z.primesLE (fun p ↦ 1 / (p : ℝ)) := by
    rw [← hCeq]
    dsimp [z, denseHierarchyZ, Jz]
    exact hendpoint (denseLowerExponent N) hJz0
  have hVupper : V ≤
      1 / ((A / (h : ℝ) ^ (48 : ℕ)) * Real.log (y + 1 : ℕ)) := by
    dsimp [V]
    exact primeInterval_euler_le_inv_mul_log hzpos hzyNat hCpos hlow
  have hV0 : 0 ≤ V := by
    dsimp [V]
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hpR).2 (by exact_mod_cast hpprime.one_le)
  have hlog16 : Real.log (16 : ℝ) = 4 * Real.log 2 := by
    rw [show (16 : ℝ) = 2 ^ 4 by norm_num, Real.log_pow]
    norm_num
  have hlog16two : (2 : ℝ) < Real.log 16 := by
    rw [hlog16]
    nlinarith [Real.log_two_gt_d9]
  have hlogy : Real.log (y : ℝ) = (Jy : ℕ) * Real.log 16 := by
    dsimp [y, denseHierarchyY]
    norm_num only [Nat.cast_pow, Nat.cast_ofNat]
    rw [Real.log_pow]
  have hypos : 0 < y := by simp [y, denseHierarchyY]
  have hlogmono : Real.log (y : ℝ) ≤ Real.log ((y + 1 : ℕ) : ℝ) := by
    exact Real.strictMonoOn_log.monotoneOn
      (show (0 : ℝ) < y by exact_mod_cast hypos)
      (show (0 : ℝ) < (y + 1 : ℕ) by exact_mod_cast (by omega : 0 < y + 1))
      (by exact_mod_cast (Nat.le_add_right y 1))
  have hloglower : 2 * (Jy : ℝ) ≤ Real.log ((y + 1 : ℕ) : ℝ) := by
    rw [hlogy] at hlogmono
    have hJy0 : (0 : ℝ) ≤ Jy := by positivity
    nlinarith [mul_le_mul_of_nonneg_left hlog16two.le hJy0]
  have hlogpos : 0 < Real.log ((y + 1 : ℕ) : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < y + 1 by omega))
  have hmulV : V * ((A / (h : ℝ) ^ (48 : ℕ)) *
      Real.log ((y + 1 : ℕ) : ℝ)) ≤ 1 := by
    have hdenpos : 0 < (A / (h : ℝ) ^ (48 : ℕ)) *
        Real.log ((y + 1 : ℕ) : ℝ) := mul_pos hCpos hlogpos
    calc
      V * ((A / (h : ℝ) ^ (48 : ℕ)) * Real.log ((y + 1 : ℕ) : ℝ)) ≤
          (1 / ((A / (h : ℝ) ^ (48 : ℕ)) *
            Real.log ((y + 1 : ℕ) : ℝ))) *
            ((A / (h : ℝ) ^ (48 : ℕ)) *
              Real.log ((y + 1 : ℕ) : ℝ)) :=
        mul_le_mul_of_nonneg_right hVupper hdenpos.le
      _ = 1 := by field_simp [hdenpos.ne']
  have hcore : 2 * A * (Jy : ℝ) * V ≤ (h : ℝ) ^ (48 : ℕ) := by
    have hdenmono :
        V * ((A / (h : ℝ) ^ (48 : ℕ)) * (2 * (Jy : ℝ))) ≤
          V * ((A / (h : ℝ) ^ (48 : ℕ)) *
            Real.log ((y + 1 : ℕ) : ℝ)) := by
      gcongr
    have hle := hdenmono.trans hmulV
    have hhpow : (0 : ℝ) < (h : ℝ) ^ (48 : ℕ) := by positivity
    calc
      2 * A * (Jy : ℝ) * V =
          (V * ((A / (h : ℝ) ^ (48 : ℕ)) * (2 * (Jy : ℝ)))) *
            (h : ℝ) ^ (48 : ℕ) := by
        field_simp [hhpow.ne']
      _ ≤ 1 * (h : ℝ) ^ (48 : ℕ) :=
        mul_le_mul_of_nonneg_right hle hhpow.le
      _ = (h : ℝ) ^ (48 : ℕ) := one_mul _
  have hBinv : 1 / A ≤ (B : ℝ) := by
    dsimp [B]
    have := Nat.le_ceil (1 / A)
    push_cast
    linarith
  have hBpow : (B : ℝ) ≤ (h : ℝ) ^ (48 : ℕ) := by
    have hBh : (B : ℝ) ≤ h := by exact_mod_cast hhB
    have hhpow : (h : ℝ) ≤ (h : ℝ) ^ (48 : ℕ) := by
      exact_mod_cast (Nat.le_pow (by omega : 0 < 48) : h ≤ h ^ 48)
    exact hBh.trans hhpow
  have hinvA : 1 / A ≤ (h : ℝ) ^ (48 : ℕ) := hBinv.trans hBpow
  have hresult : (N : ℝ) * V ≤ (h : ℝ) ^ (100 : ℕ) := by
    have hNV : (N : ℝ) * V ≤
        (2 * (Jy : ℝ) * (h : ℝ) ^ 4) * V :=
      mul_le_mul_of_nonneg_right hNle hV0
    have hscale : 0 ≤ (h : ℝ) ^ 4 / A := by positivity
    have hcorescaled := mul_le_mul_of_nonneg_right hcore hscale
    have hmid : (2 * (Jy : ℝ) * (h : ℝ) ^ 4) * V ≤
        (h : ℝ) ^ (52 : ℕ) / A := by
      calc
        (2 * (Jy : ℝ) * (h : ℝ) ^ 4) * V =
            (2 * A * (Jy : ℝ) * V) * ((h : ℝ) ^ 4 / A) := by
          field_simp [hA.ne']
        _ ≤ (h : ℝ) ^ 48 * ((h : ℝ) ^ 4 / A) := hcorescaled
        _ = (h : ℝ) ^ 52 / A := by ring
    calc
      (N : ℝ) * V ≤ (h : ℝ) ^ 52 / A := hNV.trans hmid
      _ = (h : ℝ) ^ 52 * (1 / A) := by ring
      _ ≤ (h : ℝ) ^ 52 * (h : ℝ) ^ 48 :=
        mul_le_mul_of_nonneg_left hinvA (by positivity)
      _ = (h : ℝ) ^ 100 := by ring
  simpa [h, V, z, y] using hresult

set_option maxRecDepth 10000 in
/-- The dense hierarchy order is large enough for the weighted-subset
truncation used by the denominator Euler product. -/
theorem eventually_dense_denominator_truncation (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      4 * (∑ p ∈ primeInterval (denseHierarchyZ N) (denseHierarchyY N),
        (1 / ((K : ℝ) * (p : ℝ)))) ≤
          (denseHierarchyOrder N + 1 : ℝ) := by
  obtain ⟨Jmin, hJmin, hbounds⟩ :=
    exists_geometric_interval_primeReciprocal_bounds
  have hJz := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max Jmin 2))
  have hzy := eventually_denseLower_le_upper
  filter_upwards [hJz, hzy] with N hh hzyN
  let h := denseHierarchyLog N
  let Jz := denseLowerExponent N
  let Jy := denseUpperExponent N
  let P := primeInterval (denseHierarchyZ N) (denseHierarchyY N)
  have hJzmin : Jmin ≤ Jz := by
    calc
      Jmin ≤ h := (le_max_left Jmin 2).trans hh
      _ ≤ h ^ 2 := Nat.le_pow (by omega)
      _ = Jz := rfl
  have hrecip := (hbounds Jz Jy hJzmin hzyN).2
  have hsum : (∑ p ∈ P, (1 / (p : ℝ))) ≤
      12 * (1 + Real.log Jy) := by
    rw [sum_primeInterval_one_div]
    · exact hrecip
    · exact Nat.pow_le_pow_right (by omega) hzyN
  have hweighted : (∑ p ∈ P, (1 / ((K : ℝ) * (p : ℝ)))) =
      (1 / (K : ℝ)) * ∑ p ∈ P, (1 / (p : ℝ)) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro p hp
    field_simp
  have hsum0 : 0 ≤ (∑ p ∈ P, (1 / (p : ℝ))) := by positivity
  have hKhalf : (1 / (K : ℝ)) ≤ 1 / 2 :=
    one_div_le_one_div_of_le (by norm_num) (by exact_mod_cast hK)
  have hweighted2 : 4 * (∑ p ∈ P, (1 / ((K : ℝ) * (p : ℝ)))) ≤
      2 * (∑ p ∈ P, (1 / (p : ℝ))) := by
    rw [hweighted]
    nlinarith [mul_le_mul_of_nonneg_right hKhalf hsum0]
  have harg0 : 0 ≤ 100 * (1 + Real.log Jy) := by
    have hJynat : 2 ≤ Jy := by
      have : 2 ≤ Jz := by
        calc
          2 ≤ h := (le_max_right Jmin 2).trans hh
          _ ≤ h ^ 2 := Nat.le_pow (by omega)
          _ = Jz := rfl
      exact this.trans hzyN
    have hJypos : (0 : ℝ) < Jy := by exact_mod_cast (show 0 < Jy by omega)
    have : 0 ≤ Real.log (Jy : ℝ) := Real.log_nonneg (by
      exact_mod_cast (show 1 ≤ Jy by omega))
    positivity
  have hceil := Nat.le_ceil (100 * (1 + Real.log Jy))
  have hRlower : 200 * (1 + Real.log Jy) ≤
      (denseHierarchyOrder N : ℝ) := by
    unfold denseHierarchyOrder geometricBrunOrder
    push_cast
    nlinarith
  calc
    4 * (∑ p ∈ primeInterval (denseHierarchyZ N) (denseHierarchyY N),
        1 / ((K : ℝ) * (p : ℝ))) ≤
      2 * (∑ p ∈ P, (1 / (p : ℝ))) := hweighted2
    _ ≤ 24 * (1 + Real.log Jy) := by nlinarith
    _ ≤ (denseHierarchyOrder N : ℝ) := by nlinarith
    _ ≤ (denseHierarchyOrder N : ℝ) + 1 := by linarith

set_option maxRecDepth 10000 in
/-- The denominator Euler product on the dense hierarchy interval eventually
exceeds four. -/
theorem eventually_four_le_dense_denominatorEuler (K : ℕ) (hK : 2 ≤ K) :
    ∀ᶠ N : ℕ in atTop,
      4 ≤ ∏ p ∈ primeInterval (denseHierarchyZ N) (denseHierarchyY N),
        (1 + 1 / ((K : ℝ) * (p : ℝ))) := by
  let r := 2 * K + 1
  let Cnat := 2 * 4 ^ r
  have hscaled := eventually_dense_primeInterval_euler_scaled
  have h102 := eventually_denseLog_pow_le 102
  have hhlarge := tendsto_denseHierarchyLog_atTop.eventually
    (eventually_ge_atTop (max Cnat (2 * (2 * K + 1))))
  filter_upwards [eventually_gt_atTop 0, hscaled, h102, hhlarge] with
      N hN hscaledN hpow hh
  let h := denseHierarchyLog N
  let z := denseHierarchyZ N
  let y := denseHierarchyY N
  let P := primeInterval z y
  let V := localEulerProduct P (fun p ↦ 1 / (p : ℝ))
  let E := ∏ p ∈ P, (1 + (1 / (p : ℝ)) / (K : ℝ))
  have hhC : Cnat ≤ h := (le_max_left Cnat (2 * (2 * K + 1))).trans hh
  have hhz : 2 * (2 * K + 1) ≤ z := by
    calc
      2 * (2 * K + 1) ≤ h :=
        (le_max_right Cnat (2 * (2 * K + 1))).trans hh
      _ ≤ 16 ^ (h ^ 2) :=
        (hierarchy_self_le_two_pow h).trans <| by
          calc
            2 ^ h ≤ 16 ^ h := Nat.pow_le_pow_left (by norm_num) h
            _ ≤ 16 ^ (h ^ 2) := Nat.pow_le_pow_right (by omega)
              (Nat.le_pow (by omega))
      _ = z := by simp [z, denseHierarchyZ, denseLowerExponent, h, pow_two]
  have hCscale : (Cnat : ℝ) * (h : ℝ) ^ (100 : ℕ) ≤ (N : ℝ) := by
    have hC2 : Cnat ≤ h ^ 2 := hhC.trans
      (Nat.le_pow (by omega : 0 < 2))
    have hnat : Cnat * h ^ 100 ≤ N := by
      calc
        Cnat * h ^ 100 ≤ h ^ 2 * h ^ 100 := Nat.mul_le_mul_right _ hC2
        _ = h ^ 102 := by ring
        _ ≤ N := hpow
    exact_mod_cast hnat
  have hV0 : 0 ≤ V := by
    dsimp [V, P]
    apply localEulerProduct_nonneg
    · intro p hp; positivity
    · intro p hp
      have hpprime := (Nat.mem_primesLE.mp (Finset.mem_sdiff.mp hp).1).2
      have hpR : (0 : ℝ) < p := by exact_mod_cast hpprime.pos
      exact (div_le_one hpR).2 (by exact_mod_cast hpprime.one_le)
  have hVsmall : V ≤ 1 / (Cnat : ℝ) := by
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hscaled' : (N : ℝ) * V ≤ (h : ℝ) ^ (100 : ℕ) := by
      simpa [V, P, z, y, h] using hscaledN
    rw [le_div_iff₀ (by positivity : (0 : ℝ) < (Cnat : ℝ))]
    have := mul_le_mul_of_nonneg_left hscaled'
      (show (0 : ℝ) ≤ Cnat by positivity)
    calc
      V * (Cnat : ℝ) ≤ ((N : ℝ) * V) * (Cnat : ℝ) / (N : ℝ) := by
        field_simp [hNpos.ne']
        rfl
      _ ≤ ((h : ℝ) ^ 100) * (Cnat : ℝ) / (N : ℝ) := by gcongr
      _ ≤ 1 := (div_le_one hNpos).2 (by nlinarith [hCscale])
  have hprime : ∀ p ∈ P, p.Prime := by
    intro p hp
    exact prime_of_mem_primeInterval hp
  have hsmall : ∀ p ∈ P,
      2 * (2 * K + 1 : ℕ) * (1 / (p : ℝ)) ≤ 1 := by
    intro p hp
    have hpz := (mem_primeInterval_bounds hp).1
    have hpR : (0 : ℝ) < p := by exact_mod_cast (hprime p hp).pos
    rw [show 2 * (2 * K + 1 : ℕ) * (1 / (p : ℝ)) =
      ((2 * (2 * K + 1 : ℕ) : ℕ) : ℝ) / p by push_cast; ring]
    exact (div_le_one hpR).2 (by exact_mod_cast hhz.trans hpz.le)
  have hone := one_le_denominatorEulerProduct K (by omega) P
    (fun p ↦ 1 / (p : ℝ)) (fun p hp ↦ by positivity) hsmall
  have hE0 : 0 ≤ E := by dsimp [E]; positivity
  have hEeq : E = ∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ))) := by
    dsimp [E]
    apply Finset.prod_congr rfl
    intro p hp
    congr 1
    field_simp
  by_contra hnot
  have hE4target : (∏ p ∈ P, (1 + 1 / ((K : ℝ) * (p : ℝ)))) < 4 :=
    lt_of_not_ge (by simpa [P, z, y] using hnot)
  have hE4 : E < 4 := by rw [hEeq]; exact hE4target
  have hrpos : r ≠ 0 := by dsimp [r]; omega
  have hEpow : E ^ r < (4 : ℝ) ^ r :=
    pow_lt_pow_left₀ hE4 hE0 hrpos
  have hVpow : V ^ 2 ≤ (1 / (Cnat : ℝ)) ^ 2 :=
    pow_le_pow_left₀ hV0 hVsmall 2
  have hCeq : (Cnat : ℝ) = 2 * (4 : ℝ) ^ r := by
    dsimp [Cnat]
    push_cast
    ring
  have hQ : 1 ≤ (4 : ℝ) ^ r := one_le_pow₀ (by norm_num)
  have hprodlt : V ^ 2 * E ^ r < 1 := by
    calc
      V ^ 2 * E ^ r ≤ (1 / (Cnat : ℝ)) ^ 2 * E ^ r :=
        mul_le_mul_of_nonneg_right hVpow (pow_nonneg hE0 _)
      _ < (1 / (Cnat : ℝ)) ^ 2 * (4 : ℝ) ^ r :=
        mul_lt_mul_of_pos_left hEpow (by positivity)
      _ ≤ 1 / 4 := by
        rw [hCeq]
        have hQpos : 0 < (4 : ℝ) ^ r := by positivity
        field_simp [hQpos.ne']
        nlinarith
      _ < 1 := by norm_num
  exact (not_lt_of_ge (by simpa [V, E, P, r] using hone)) hprodlt

end Erdos394
