/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTSourceDensity
import ErdosProblems.Erdos4b.FGKMTExpectedDegreeBudget

/-! # Unconditional bounds for the actual source degree scale -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter

theorem exists_source_expectedDegreeScale_bounds :
    ∃ d K : ℝ, 0 < d ∧ 0 < K ∧ ∀ a c : ℝ, 0 < a → 0 < c →
      ∀ᶠ x : ℕ in atTop, ∀ e : ℝ, ∀ D : SourceProbabilityData c e x,
        d / (a * c) ≤ D.expectedDegreeScale (sourceSmallPrimes a x) ∧
        D.expectedDegreeScale (sourceSmallPrimes a x) ≤ K / (a * c) := by
  obtain ⟨A, B, hA, hB, hbound⟩ := exists_source_density_length_bounds
  refine ⟨(1 / 368640) / (2 * B), ((6 / 5) * Real.exp 24) / (2 * A),
    by positivity, by positivity, ?_⟩
  intro a c ha hc
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [hbound a c ha hc, eventually_sourceIntervalLength_bounds hc,
    hloglog.eventually (eventually_gt_atTop (0 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hden hy hl hx
  intro e D
  let l := Real.log (Real.log (x : ℝ))
  let V := residueSieveDensity (sourceSmallPrimes a x) * sourceIntervalLength c x
  change 0 < l at hl
  have hxpos : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hypos : 0 < sourceIntervalLength c x := hxR.trans_le hy.1
  have hσpos := residueSieveDensity_pos
    (fun p hp => (sourceSmallPrimes_prime a x p hp).one_lt)
  have hV : 0 < V := mul_pos hσpos hypos
  have hu := D.gain_pos
  have hlow : A * a * c * x * l ≤ V := hden.1
  have hupp : V ≤ B * a * c * x * l := hden.2
  have hscale : D.expectedDegreeScale (sourceSmallPrimes a x) = D.gain * x / (2 * V) := by
    rw [D.expectedDegreeScale_eq]
    dsimp only [V]
    ring
  rw [hscale]
  constructor
  · calc
      (1 / 368640 / (2 * B)) / (a * c) =
          ((l / 368640) * x) / (2 * (B * a * c * x * l)) := by
        field_simp [hB.ne', ha.ne', hc.ne', hxR.ne', hl.ne']
      _ ≤ D.gain * x / (2 * V) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right D.gain_lower hxR.le)
          (by positivity) (by nlinarith [hupp])
  · calc
      D.gain * x / (2 * V) ≤
          (((6 / 5) * Real.exp 24 * l) * x) / (2 * (A * a * c * x * l)) :=
        div_le_div₀ (by positivity)
          (mul_le_mul_of_nonneg_right D.gain_upper hxR.le)
          (by positivity) (by nlinarith [hlow])
      _ = (((6 / 5) * Real.exp 24) / (2 * A)) / (a * c) := by
        field_simp [hA.ne', ha.ne', hc.ne', hxR.ne', hl.ne']

theorem exists_source_expectedDegree_range {a T : ℝ} (ha : 0 < a) (hT : 0 < T) :
    ∃ c K : ℝ, 0 < c ∧ 0 < K ∧
      ∀ᶠ x : ℕ in atTop, ∀ e : ℝ, ∀ D : SourceProbabilityData c e x,
        T ≤ D.expectedDegreeScale (sourceSmallPrimes a x) ∧
        D.expectedDegreeScale (sourceSmallPrimes a x) ≤ K := by
  obtain ⟨d, K, hd, hK, hbound⟩ := exists_source_expectedDegreeScale_bounds
  let c := d / (a * (T + 1))
  have hT1 : 0 < T + 1 := by linarith
  have hc : 0 < c := div_pos hd (mul_pos ha hT1)
  have hcancel : d / (a * c) = T + 1 := by
    dsimp only [c]
    field_simp [ha.ne', hd.ne', hT1.ne']
  refine ⟨c, K / (a * c), hc, div_pos hK (mul_pos ha hc), ?_⟩
  filter_upwards [hbound a c ha hc] with x hx
  intro e D
  have h := hx e D
  rw [hcancel] at h
  exact ⟨(by linarith [h.1]), h.2⟩

theorem eventually_actualSource_expectedDegree_good_vertices {a c e : ℝ}
    (ha : 0 < a) (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ b : ResidueAssignment (sourceSmallPrimes a x), ∀ q ∈ sourceSievingPrimes c x,
        residueAssignmentAvoids (sourceSmallPrimes a x) {(q : ℤ)} b →
        q ∉ D.badPinnedVertices (sourceSmallPrimes a x) b →
        q ∉ D.lostDegreeVertices (sourceSmallPrimes a x)
          (1 / Real.log (Real.log (x : ℝ)) ^ 3) b →
        |D.primeTupleExpectedDegree (sourceSmallPrimes a x) (sourceSievingPrimes c x) b q -
            D.expectedDegreeScale (sourceSmallPrimes a x)| ≤
          1 / Real.log (Real.log (x : ℝ)) ^ 2 := by
  obtain ⟨_d, K, _hd, hK, hbound⟩ := exists_source_expectedDegreeScale_bounds
  have hcap : 0 < K / (a * c) := div_pos hK (mul_pos ha hc)
  filter_upwards [hbound a c ha hc, eventually_source_expectedDegree_good_vertices
    (e := e) hc hcap] with x hx hgood
  intro D b q hq hsurv hpin hlost
  exact hgood D (sourceSmallPrimes a x) (sourceSmallPrimes_prime a x)
    (hx e D).2 b q hq hsurv hpin hlost

end

end Erdos4b.FGKMT
