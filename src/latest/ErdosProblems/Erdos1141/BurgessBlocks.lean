import ErdosProblems.Erdos1141.BurgessCompositeAmplifier

/-!
# Burgess cancellation on a fixed positive-power block length

The inequalities on the exponents below record the parameter budget. They
will be instantiated with arbitrarily small positive slack above one quarter.
-/

namespace Pollack17.Burgess

open Filter
open scoped BigOperators

theorem eventually_power_block_bound (k : ℕ) {c u v δ η : ℝ}
    (hc : 0 < c) (hu : 0 < u) (hv : 0 ≤ v) (hδ : 0 < δ) (hη : 0 < η)
    (hu1 : u ≤ 1) (huδ : u ≤ c + δ) (huv : u + v < c - η) (huc : u + c < 1)
    (hvk : v * (k + 1 : ℝ) = 1 / 2)
    (hgap : (c + u) * (2 * k + 1 : ℕ) + 3 / 2 + 3 * δ <
      (u + v + c - δ - η) * (2 * (k + 1) : ℕ)) :
    ∀ᶠ q : ℕ in atTop, ∀ (s : Finset ℕ) (hs : ∀ p ∈ s, p.Prime),
      primeModulus s = q → ∀ M : ℕ,
        |∑ i ∈ Finset.range ⌊(q : ℝ) ^ c⌋₊, productChar s hs (M + i : ℕ)| ≤
          (q : ℝ) ^ (c - η) := by
  obtain ⟨Qm, hm⟩ := eventually_productChar_moment_le (k + 1) (by omega) hδ
  obtain ⟨Qd, hd⟩ := eventually_coprimeDenominators_lower (half_pos hu) hδ
  have hroot := eventually_const_mul_rpow_le (C := 1) (d := 1 / 2)
    (a := u / 2) (b := u) (by norm_num) (by linarith)
  have hshift := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + v) (b := c) (by norm_num) (by linarith)
  have hsmall := eventually_const_mul_rpow_le (C := 2) (d := 1 / 2)
    (a := u + c) (b := 1) (by norm_num) huc
  have herror := eventually_const_mul_rpow_le (C := 4) (d := 1 / 2)
    (a := u + v) (b := c - η) (by norm_num) huv
  have hbudget := eventually_const_mul_rpow_le
    (C := 2 * ((2 : ℝ) ^ (k + 1) + 2 ^ (2 * (k + 1))))
    (d := (1 / 4 : ℝ) ^ (2 * (k + 1))) (by positivity) hgap
  filter_upwards [eventually_ge_atTop Qm, eventually_ge_atTop Qd,
    eventually_ge_atTop 1, eventually_floor_rpow_bounds hc, eventually_floor_rpow_bounds hu,
    eventually_one_add_log_le_rpow hδ, hroot, hshift, hsmall, herror, hbudget]
    with q hqm hqd hq1 hHbounds hUbounds hlog hrootq hshiftq hsmallq herrorq hbudgetq
  intro s hs hsq M
  subst q
  let q := primeModulus s
  let H := ⌊(q : ℝ) ^ c⌋₊
  let U := ⌊(q : ℝ) ^ u⌋₊
  let V := ⌈(q : ℝ) ^ v⌉₊
  let D := coprimeDenominators s U
  let A : ℝ := (D.card : ℝ) * V
  let B : ℝ := (q : ℝ) ^ (c - η) / 2
  have : NeZero (primeModulus s) := ⟨(primeModulus_pos s hs).ne'⟩
  let W := amplifierNumerator (productChar s hs) M H D V
  have hq0 : 0 < (q : ℝ) := by exact_mod_cast hq1
  have hHlo : (q : ℝ) ^ c / 2 ≤ (H : ℝ) := hHbounds.1
  have hHhi : (H : ℝ) ≤ (q : ℝ) ^ c := hHbounds.2
  have hUlo : (q : ℝ) ^ u / 2 ≤ (U : ℝ) := hUbounds.1
  have hUhi : (U : ℝ) ≤ (q : ℝ) ^ u := hUbounds.2
  have hVbounds := ceil_rpow_bounds hv hq1
  have hVlo : (q : ℝ) ^ v ≤ (V : ℝ) := hVbounds.1
  have hVhi : (V : ℝ) ≤ 2 * (q : ℝ) ^ v := hVbounds.2
  have hHpos : 0 < H := by
    have h : (0 : ℝ) < H := lt_of_lt_of_le (by positivity) hHlo
    exact_mod_cast h
  have hUpos : 0 < U := by
    have h : (0 : ℝ) < U := lt_of_lt_of_le (by positivity) hUlo
    exact_mod_cast h
  have hVpos : 0 < (V : ℝ) := (Real.rpow_pos_of_pos hq0 v).trans_le hVlo
  have hUroot : (q : ℝ) ^ (u / 2) ≤ U := by
    have h : (q : ℝ) ^ (u / 2) ≤ (q : ℝ) ^ u / 2 := by
      simpa only [one_mul, one_div, div_eq_mul_inv, mul_comm] using hrootq
    exact h.trans hUlo
  have hDbase : (U : ℝ) * (q : ℝ) ^ (-δ) ≤ (D.card : ℝ) := hd s hs hqd U hUroot
  have hDlo : (1 / 2 : ℝ) * (q : ℝ) ^ (u - δ) ≤ (D.card : ℝ) := by
    calc
      _ = ((q : ℝ) ^ u / 2) * (q : ℝ) ^ (-δ) := by
        rw [sub_eq_add_neg, Real.rpow_add hq0]
        ring
      _ ≤ (U : ℝ) * (q : ℝ) ^ (-δ) :=
        mul_le_mul_of_nonneg_right hUlo (Real.rpow_nonneg hq0.le _)
      _ ≤ _ := hDbase
  have hDpos : (0 : ℝ) < D.card := lt_of_lt_of_le (by positivity) hDlo
  have hApos : 0 < A := mul_pos hDpos hVpos
  have hUV : (U : ℝ) * V ≤ 2 * (q : ℝ) ^ (u + v) := by
    calc
      _ ≤ (q : ℝ) ^ u * (2 * (q : ℝ) ^ v) :=
        mul_le_mul hUhi hVhi (Nat.cast_nonneg V) (Real.rpow_nonneg hq0.le _)
      _ = _ := by rw [mul_left_comm, ← Real.rpow_add hq0]
  have hUVH : U * V ≤ H := by
    have h : (U : ℝ) * V ≤ H := hUV.trans (hshiftq.trans (by
      simpa only [one_div, div_eq_mul_inv, mul_comm, one_mul] using hHlo))
    exact_mod_cast h
  have hUHsmall : 2 * (U * H) < q := by
    have hUH : (U : ℝ) * H ≤ (q : ℝ) ^ (u + c) := by
      simpa only [Real.rpow_add hq0] using
        mul_le_mul hUhi hHhi (Nat.cast_nonneg H) (Real.rpow_nonneg hq0.le _)
    have hsmall' : 2 * (q : ℝ) ^ (u + c) ≤ (q : ℝ) / 2 := by
      simpa only [Real.rpow_one, one_div, div_eq_mul_inv, mul_comm, one_mul] using hsmallq
    have hstrict : 2 * ((U : ℝ) * H) < q := by
      have hle := (mul_le_mul_of_nonneg_left hUH (by norm_num : (0 : ℝ) ≤ 2)).trans hsmall'
      exact hle.trans_lt (half_lt_self hq0)
    exact_mod_cast hstrict
  have hWpow := amplifier_scale_le hq1 (productChar s hs) M H U V k D
    (Finset.filter_subset _ _) (fun _ h => (Finset.mem_filter.mp h).2)
    hHpos hUpos hUHsmall hu1 huδ hHhi hUhi hVhi hvk hlog (hm s hs hqm V)
  have hAB : (1 / 4 : ℝ) * (q : ℝ) ^ (u + v + c - δ - η) ≤ A * B := by
    have hprod := mul_le_mul hDlo hVlo (Real.rpow_nonneg hq0.le v) (le_of_lt hDpos)
    have hscaled := mul_le_mul_of_nonneg_right hprod
      (by dsimp [B]; positivity : 0 ≤ B)
    refine le_trans ?_ hscaled
    apply le_of_eq
    dsimp [B]
    rw [div_eq_mul_inv]
    calc
      _ = (1 / 4 : ℝ) * ((q : ℝ) ^ (u - δ) * (q : ℝ) ^ v * (q : ℝ) ^ (c - η)) := by
        rw [← Real.rpow_add hq0, ← Real.rpow_add hq0]
        congr 2
        ring
      _ = _ := by ring
  have hABpow := scaled_rpow_le_pow (by norm_num : (0 : ℝ) ≤ 1 / 4) hq0.le hAB (2 * (k + 1))
  have hWle : W ≤ A * B := le_of_pow_le_pow_left₀ (n := 2 * (k + 1)) (by omega)
    (by dsimp [A, B]; positivity) (hWpow.trans (hbudgetq.trans hABpow))
  have hamp := productChar_amplified_abs_le s hs (M := M) hUVH
  have hS : |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ B + 2 * (U : ℝ) * V := by
    apply (mul_le_mul_iff_right₀ hApos).mp
    change (D.card : ℝ) * V * |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
    calc
      _ ≤ W + 2 * (D.card : ℝ) * V * (U * V) := hamp
      _ ≤ A * B + 2 * A * ((U : ℝ) * V) := by
        dsimp only [A]
        nlinarith only [hWle]
      _ = _ := by ring
  have hboundary : 2 * (U : ℝ) * V ≤ (q : ℝ) ^ (c - η) / 2 := by
    have hUV2 := mul_le_mul_of_nonneg_left hUV (by norm_num : (0 : ℝ) ≤ 2)
    nlinarith only [hUV2, herrorq]
  change |∑ i ∈ Finset.range H, productChar s hs (M + i : ℕ)| ≤ _
  dsimp only [B] at hS
  linarith

end Pollack17.Burgess
