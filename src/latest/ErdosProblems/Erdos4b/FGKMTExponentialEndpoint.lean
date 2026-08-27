/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTCompleteCover
import ErdosProblems.Erdos4b.FGKMTBoundedCrtGap

/-! # Constructed prime gaps below a fixed exponential endpoint -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem source_endpoint_le_exp {x M y : ℕ} (hx : 10 ≤ x) (hM : 2 ≤ M)
    (hy : (y : ℝ) ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2)
    (hP : Real.log (primorial (M * x) : ℝ) ≤ 2 * (M * x : ℕ)) :
    ((2 * (3 * primorial (M * x) + y + 1) : ℕ) : ℝ) ≤
      Real.exp ((2 * (M : ℝ) + 1) * x) := by
  have hxpos : (0 : ℝ) < x := by exact_mod_cast (show 0 < x by omega)
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have hlog0 : 0 ≤ Real.log (x : ℝ) := Real.log_natCast_nonneg x
  have hlogx : Real.log (x : ℝ) ≤ (x : ℝ) := Real.log_le_self hxpos.le
  have hycube : (y : ℝ) ≤ (x : ℝ) ^ 3 := by
    have hsq := pow_le_pow_left₀ hlog0 hlogx 2
    nlinarith [mul_le_mul_of_nonneg_left hsq hxpos.le]
  have hyexp : (y : ℝ) ≤ Real.exp (2 * (M : ℝ) * x) := by
    calc
      _ ≤ (x : ℝ) ^ 3 := hycube
      _ = Real.exp (3 * Real.log (x : ℝ)) := by
        rw [show 3 * Real.log (x : ℝ) = Real.log ((x : ℝ) ^ 3) by
          rw [Real.log_pow]; norm_num, Real.exp_log (pow_pos hxpos 3)]
      _ ≤ _ := Real.exp_le_exp.mpr (by
        nlinarith [mul_le_mul_of_nonneg_right hM2 hxpos.le])
  have hPexp : (primorial (M * x) : ℝ) ≤ Real.exp (2 * (M : ℝ) * x) := by
    apply Real.le_exp_of_log_le
    simpa only [Nat.cast_mul, mul_assoc] using hP
  have hone : 1 ≤ Real.exp (2 * (M : ℝ) * x) := Real.one_le_exp (by positivity)
  have hten : (10 : ℝ) ≤ Real.exp (x : ℝ) := by
    have hxR : (10 : ℝ) ≤ x := by exact_mod_cast hx
    linarith [Real.add_one_le_exp (x : ℝ)]
  calc
    _ ≤ 10 * Real.exp (2 * (M : ℝ) * x) := by
      push_cast
      linarith
    _ ≤ Real.exp (x : ℝ) * Real.exp (2 * (M : ℝ) * x) :=
      mul_le_mul_of_nonneg_right hten (Real.exp_pos _).le
    _ = _ := by rw [← Real.exp_add]; congr 1; ring

theorem exists_source_gaps_exponential :
    ∃ c B : ℝ, 0 < c ∧ 1 ≤ B ∧ ∀ᶠ x : ℕ in atTop,
      ∃ n : ℕ,
        (⌊sourceIntervalLength c x⌋₊ - x : ℕ) <
          (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n ∧
        (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ Real.exp (B * x) := by
  obtain ⟨c, M, hc, hM, hcover⟩ := exists_complete_source_covers
  have hMpos : 0 < M := by omega
  have htop : Tendsto (fun x : ℕ => M * x) atTop atTop :=
    tendsto_atTop_mono (fun x => Nat.le_mul_of_pos_left x hMpos) tendsto_id
  have hB : (1 : ℝ) ≤ 2 * (M : ℝ) + 1 := by
    have hm : (0 : ℝ) ≤ M := Nat.cast_nonneg M
    linarith
  refine ⟨c, 2 * (M : ℝ) + 1, hc, hB, ?_⟩
  filter_upwards [hcover, eventually_sourceIntervalLength_bounds hc,
    htop.eventually eventually_log_primorial_lt_two_mul, eventually_ge_atTop (10 : ℕ)]
      with x hcov hy hP hx
  obtain ⟨cover, hprimes⟩ := hcov
  obtain ⟨n, hgap, hright⟩ := exists_bounded_gap_of_cover cover hprimes
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  have hlength : ((⌊sourceIntervalLength c x⌋₊ - x : ℕ) : ℝ) ≤
      (x : ℝ) * Real.log (x : ℝ) ^ 2 :=
    (show ((⌊sourceIntervalLength c x⌋₊ - x : ℕ) : ℝ) ≤ ⌊sourceIntervalLength c x⌋₊ by
      exact_mod_cast Nat.sub_le ⌊sourceIntervalLength c x⌋₊ x).trans
        ((Nat.floor_le hy0).trans hy.2.1)
  refine ⟨n, hgap, ?_⟩
  have hrR : (Nat.nth Nat.Prime (n + 1) : ℝ) ≤
      ((2 * (3 * primorial (M * x) + (⌊sourceIntervalLength c x⌋₊ - x) + 1) : ℕ) : ℝ) := by
    exact_mod_cast hright
  exact hrR.trans (source_endpoint_le_exp hx hM hlength hP.le)

end

end Erdos4b.FGKMT
