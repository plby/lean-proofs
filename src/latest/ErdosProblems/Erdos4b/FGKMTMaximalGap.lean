/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTExponentialEndpoint
import ErdosProblems.Erdos4b.FGKMTGapScale

/-! # The stronger maximal-gap bound for every sufficiently large real endpoint -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_eventual_maximal_gap :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop, ∃ n : ℕ,
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
      c * fgkmtScale X ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, B, hc, hB, hgaps⟩ := exists_source_gaps_exponential
  have hBpos : 0 < B := by linarith
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  have hgood : ∀ᶠ x : ℕ in atTop,
      (∃ n : ℕ, (⌊sourceIntervalLength c x⌋₊ - x : ℕ) <
        (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
        (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Real.exp (B * x)) ∧
      sourceIntervalLength c x / 2 ≤ ((⌊sourceIntervalLength c x⌋₊ - x : ℕ) : ℝ) ∧
      1 ≤ Real.log (x : ℝ) ∧ 1 ≤ Real.log (Real.log (x : ℝ)) ∧
      1 ≤ Real.log (Real.log (Real.log (x : ℝ))) ∧ 2 * B ≤ (x : ℝ) ∧ 1 ≤ x := by
    filter_upwards [hgaps, eventually_source_gap_length_lower hc,
      hlog.eventually_ge_atTop 1, hloglog.eventually_ge_atTop 1,
      hlogloglog.eventually_ge_atTop 1,
      (tendsto_natCast_atTop_atTop (R := ℝ)).eventually_ge_atTop (2 * B),
      eventually_ge_atTop (1 : ℕ)] with x hg hl hL hℓ ht hx hx1
    exact ⟨hg, hl, hL, hℓ, ht, hx, hx1⟩
  have hfloorTop : Tendsto (fun X : ℝ => ⌊Real.log X / B⌋₊) atTop atTop :=
    tendsto_nat_floor_atTop.comp (Real.tendsto_log_atTop.atTop_div_const hBpos)
  have hc' : 0 < c / (16 * B) := by positivity
  refine ⟨c / (16 * B), hc', ?_⟩
  filter_upwards [hfloorTop.eventually hgood, eventually_ge_atTop (1 : ℝ)] with X hXdata hX1
  let x := ⌊Real.log X / B⌋₊
  change (∃ n : ℕ, (⌊sourceIntervalLength c x⌋₊ - x : ℕ) <
      (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
      (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Real.exp (B * x)) ∧ _ at hXdata
  obtain ⟨hg, hlength, hL, hℓ, ht, hx, hx1⟩ := hXdata
  obtain ⟨n, hgap, hright⟩ := hg
  have hXpos : 0 < X := by linarith
  have hlogX0 : 0 ≤ Real.log X := Real.log_nonneg hX1
  have hBx : B * (x : ℝ) ≤ Real.log X := by
    have hh := (le_div_iff₀ hBpos).mp (Nat.floor_le (div_nonneg hlogX0 hBpos.le))
    simpa only [mul_comm] using hh
  have hlo : Real.exp (B * x) ≤ X := (Real.le_log_iff_exp_le hXpos).mp hBx
  have hhi : X ≤ Real.exp (2 * B * x) := by
    have hh := (div_lt_iff₀ hBpos).mp (Nat.lt_floor_add_one (Real.log X / B))
    have hx1R : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    apply (Real.log_le_iff_le_exp hXpos).mp
    change Real.log X < ((x : ℝ) + 1) * B at hh
    nlinarith
  have henvelope := fgkmtScale_le_source_envelope hB hx hL hℓ ht hlo hhi
  have hscale : (c / (16 * B)) * (8 * B * sourceIntervalLength 1 x) =
      sourceIntervalLength c x / 2 := by
    unfold sourceIntervalLength
    field_simp
    ring
  have hbound : (c / (16 * B)) * fgkmtScale X ≤ sourceIntervalLength c x / 2 := by
    exact (mul_le_mul_of_nonneg_left henvelope hc'.le).trans_eq hscale
  exact ⟨n, hright.trans hlo, (hbound.trans hlength).trans hgap.le⟩

end

end Erdos4b.FGKMT
