/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceSmallPrimes

/-! # Two-sided source density and the exact source-length cancellation -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

def sourceDensityScale (a : ℝ) (x : ℕ) : ℝ :=
  a * Real.log (Real.log (x : ℝ)) ^ 2 /
    (Real.log (x : ℝ) * Real.log (Real.log (Real.log (x : ℝ))))

theorem sourceDensityScale_pos {a : ℝ} {x : ℕ} (ha : 0 < a)
    (hL : 0 < Real.log (x : ℝ)) (hl : 0 < Real.log (Real.log (x : ℝ)))
    (ht : 0 < Real.log (Real.log (Real.log (x : ℝ)))) : 0 < sourceDensityScale a x := by
  unfold sourceDensityScale
  positivity

theorem sourceSmallPrime_log_ratio {a : ℝ} {x : ℕ} (ha : 0 < a)
    (hL : 0 < Real.log (x : ℝ)) (hl : 0 < Real.log (Real.log (x : ℝ)))
    (ht : 0 < Real.log (Real.log (Real.log (x : ℝ)))) :
    Real.log (sourceSmallPrimeLower x) / Real.log (sourceSmallPrimeUpper a x) =
      20 * sourceDensityScale a x := by
  rw [log_sourceSmallPrimeLower, log_sourceSmallPrimeUpper]
  unfold sourceDensityScale
  field_simp [ha.ne', hL.ne', hl.ne', ht.ne']

theorem exists_sourceSmallPrimes_density_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ a : ℝ, 0 < a →
      ∀ᶠ x : ℕ in atTop,
        A * sourceDensityScale a x ≤ residueSieveDensity (sourceSmallPrimes a x) ∧
        residueSieveDensity (sourceSmallPrimes a x) ≤ B * sourceDensityScale a x := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_primeInterval_density_bounds
  refine ⟨20 * A, 20 * B, by positivity, by positivity, ?_⟩
  intro a ha
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  filter_upwards [eventually_sourceSmallPrime_ranges ha,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    hlogloglog.eventually (eventually_gt_atTop (0 : ℝ))] with x hx hL hl ht
  have h := hbound (sourceSmallPrimeLower x) (sourceSmallPrimeUpper a x) hx.1 hx.2.1
  rw [sourceSmallPrime_log_ratio ha hL hl ht] at h
  change A * (20 * sourceDensityScale a x) ≤ residueSieveDensity (sourceSmallPrimes a x) ∧
    residueSieveDensity (sourceSmallPrimes a x) ≤ B * (20 * sourceDensityScale a x) at h
  constructor <;> nlinarith [h.1, h.2]

theorem sourceDensityScale_mul_interval {a c : ℝ} {x : ℕ}
    (hL : Real.log (x : ℝ) ≠ 0) (hl : Real.log (Real.log (x : ℝ)) ≠ 0)
    (ht : Real.log (Real.log (Real.log (x : ℝ))) ≠ 0) :
    sourceDensityScale a x * sourceIntervalLength c x =
      a * c * x * Real.log (Real.log (x : ℝ)) := by
  unfold sourceDensityScale sourceIntervalLength
  field_simp [hL, hl, ht]

theorem exists_source_density_length_bounds :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧ ∀ a c : ℝ, 0 < a → 0 < c →
      ∀ᶠ x : ℕ in atTop,
        A * a * c * x * Real.log (Real.log (x : ℝ)) ≤
            residueSieveDensity (sourceSmallPrimes a x) * sourceIntervalLength c x ∧
        residueSieveDensity (sourceSmallPrimes a x) * sourceIntervalLength c x ≤
            B * a * c * x * Real.log (Real.log (x : ℝ)) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_sourceSmallPrimes_density_bounds
  refine ⟨A, B, hA, hB, ?_⟩
  intro a c ha hc
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  have hlogloglog := Real.tendsto_log_atTop.comp hloglog
  filter_upwards [hbound a ha, eventually_sourceIntervalLength_bounds hc,
    hlog.eventually (eventually_gt_atTop (0 : ℝ)),
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    hlogloglog.eventually (eventually_gt_atTop (0 : ℝ))] with x hσ hy hL hl ht
  have hy0 : 0 ≤ sourceIntervalLength c x := (Nat.cast_nonneg x).trans hy.1
  have hlow := mul_le_mul_of_nonneg_right hσ.1 hy0
  have hupp := mul_le_mul_of_nonneg_right hσ.2 hy0
  rw [mul_assoc, sourceDensityScale_mul_interval hL.ne' hl.ne' ht.ne'] at hlow
  rw [mul_assoc, sourceDensityScale_mul_interval hL.ne' hl.ne' ht.ne'] at hupp
  constructor <;> nlinarith [hlow, hupp]

end

end Erdos4b.FGKMT
