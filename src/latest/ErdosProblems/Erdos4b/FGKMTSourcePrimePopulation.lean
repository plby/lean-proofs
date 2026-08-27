/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceDegreeScale

/-! # Two-sided cardinality bounds for the literal source prime population -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem sourceIntervalLength_floor_tendsto {c : ℝ} (hc : 0 < c) :
    Tendsto (fun x : ℕ => ⌊sourceIntervalLength c x⌋₊) atTop atTop := by
  apply tendsto_atTop.mpr
  intro N
  filter_upwards [eventually_sourceIntervalLength_bounds hc, eventually_ge_atTop N] with x hy hx
  exact hx.trans ((Nat.le_floor_iff ((Nat.cast_nonneg x).trans hy.1)).mpr hy.1)

theorem eventually_sourceIntervalLength_eight_mul {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, 8 * (x : ℝ) ≤ sourceIntervalLength c x := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hpow := (tendsto_rpow_atTop (by norm_num : (0 : ℝ) < 1 / 10)).comp hlog
  filter_upwards [eventually_sourceIntervalLength_bounds hc,
    hpow.eventually (eventually_ge_atTop (2 : ℝ))] with x hy hk
  have h := hy.2.2 2 (by simpa only [Nat.cast_ofNat, Function.comp_apply] using hk)
  norm_num only [Nat.cast_ofNat] at h
  exact h

theorem sourceSievingPrimes_card_le_primeCounting (c : ℝ) (x : ℕ) :
    (sourceSievingPrimes c x).card ≤ Nat.primeCounting ⌊sourceIntervalLength c x⌋₊ := by
  rw [← Nat.primesLE_card_eq_primeCounting]
  apply Finset.card_le_card
  intro p hp
  have h := mem_commonPinnedPrimeSet.mp hp
  exact Nat.mem_primesLE.mpr ⟨h.2.1, h.2.2⟩

theorem eventually_sourceSievingPrimes_card_bounds {c : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop,
      sourceIntervalLength c x / (32 * Real.log (x : ℝ)) ≤ (sourceSievingPrimes c x).card ∧
      ((sourceSievingPrimes c x).card : ℝ) ≤
        2 * sourceIntervalLength c x / Real.log (x : ℝ) := by
  have hfloor := sourceIntervalLength_floor_tendsto hc
  filter_upwards [eventually_sourceIntervalLength_eight_mul hc, eventually_sourceTuple_ranges hc,
    hfloor.eventually eventually_commonPinnedPrimeSet_half_card_lower,
    hfloor.eventually eventually_primeCounting_le_two_div_log,
    eventually_ge_atTop (2 : ℕ)] with x hy8 hy2 hcountlo hcounthi hx
  let y := sourceIntervalLength c x
  let m : ℕ := ⌊y⌋₊
  let L := Real.log (x : ℝ)
  have hxR : (2 : ℝ) ≤ x := by exact_mod_cast hx
  have hxpos : (0 : ℝ) < x := by linarith
  have hypos : 0 < y := by dsimp only [y]; linarith
  have hL : 0 < L := Real.log_pos (by linarith)
  have hmle : (m : ℝ) ≤ y := Nat.floor_le hypos.le
  have hym : y < (m : ℝ) + 1 := Nat.lt_floor_add_one y
  have hmhalf : y / 2 ≤ (m : ℝ) := by linarith
  have hxm : 2 * x ≤ m := by
    apply (Nat.le_floor_iff hypos.le).mpr
    push_cast
    linarith
  have hxhalf : x ≤ m / 2 := by omega
  have hmx : x ≤ m := by omega
  have hmxR : (x : ℝ) ≤ m := by exact_mod_cast hmx
  have hmpos : (0 : ℝ) < m := hxpos.trans_le hmxR
  have hlogm : 0 < Real.log (m : ℝ) := Real.log_pos (by linarith)
  have hloglo : L ≤ Real.log (m : ℝ) := Real.log_le_log hxpos hmxR
  have hlogsq : Real.log (m : ℝ) ≤ 2 * L := by
    have hmsq : (m : ℝ) ≤ (x : ℝ) ^ 2 := by linarith [hy2.2]
    simpa only [Real.log_pow, Nat.cast_ofNat] using Real.log_le_log hmpos hmsq
  have hsubset : commonPinnedPrimeSet (m / 2) m ⊆ sourceSievingPrimes c x := by
    intro p hp
    have h := mem_commonPinnedPrimeSet.mp hp
    exact mem_commonPinnedPrimeSet.mpr ⟨hxhalf.trans_lt h.1, h.2.1, h.2.2⟩
  constructor
  · calc
      y / (32 * L) = (y / 2) / (8 * (2 * L)) := by ring
      _ ≤ (m : ℝ) / (8 * Real.log (m : ℝ)) :=
        div_le_div₀ hmpos.le hmhalf (by positivity)
          (mul_le_mul_of_nonneg_left hlogsq (by norm_num))
      _ ≤ (commonPinnedPrimeSet (m / 2) m).card := hcountlo
      _ ≤ _ := by exact_mod_cast Finset.card_le_card hsubset
  · calc
      _ ≤ (Nat.primeCounting m : ℝ) := by
        exact_mod_cast sourceSievingPrimes_card_le_primeCounting c x
      _ ≤ 2 * (m : ℝ) / Real.log (m : ℝ) := hcounthi
      _ ≤ 2 * y / L := div_le_div₀ (by positivity)
        (mul_le_mul_of_nonneg_left hmle (by norm_num)) hL hloglo

end

end Erdos4b.FGKMT
