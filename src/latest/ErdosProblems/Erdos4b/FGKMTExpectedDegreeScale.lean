/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTExpectedDegreeComparison

/-! # The common expected-degree scale, with all finite normalization errors -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

theorem two_stage_relative_mass_error {T B G s M r η : ℝ}
    (hBpos : 0 < B) (hs : 0 < s) (hM : 0 < M) (hr : 0 ≤ r)
    (hpin : |T / (B * s) - 1| ≤ r) (hB : |B - G| ≤ η * G) :
    |T / M - s * G / M| ≤ (r * (1 + η) + η) * (s * G / M) := by
  have hratio : T / (B * s) - 1 = (T - s * B) / (B * s) := by
    field_simp [hBpos.ne', hs.ne']
  rw [hratio, abs_div, abs_of_pos (mul_pos hBpos hs)] at hpin
  have hpin' : |T - s * B| ≤ r * (s * B) := by
    have h := (div_le_iff₀ (mul_pos hBpos hs)).mp hpin
    nlinarith
  have hBupper : B ≤ (1 + η) * G := by linarith [(abs_le.mp hB).2]
  have hscaled : |s * B - s * G| ≤ s * (η * G) := by
    rw [← mul_sub, abs_mul, abs_of_pos hs]
    exact mul_le_mul_of_nonneg_left hB hs.le
  calc
    _ = |T - s * G| / M := by rw [← sub_div, abs_div, abs_of_pos hM]
    _ ≤ (|T - s * B| + |s * B - s * G|) / M :=
      div_le_div_of_nonneg_right (abs_sub_le _ _ _) hM.le
    _ ≤ (r * (s * B) + s * (η * G)) / M :=
      div_le_div_of_nonneg_right (add_le_add hpin' hscaled) hM.le
    _ ≤ (r * (s * ((1 + η) * G)) + s * (η * G)) / M := by
      apply div_le_div_of_nonneg_right _ hM.le
      exact add_le_add
        (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hBupper hs.le) hr) le_rfl
    _ = _ := by ring

def SourceProbabilityData.expectedDegreeScale {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) : ℝ :=
  (D.gain * x / (2 * sourceIntervalLength c x)) / residueSieveDensity S

theorem SourceProbabilityData.expectedDegreeScale_eq {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (S : Finset ℕ) :
    D.expectedDegreeScale S =
      D.gain * x / (2 * residueSieveDensity S * sourceIntervalLength c x) := by
  unfold expectedDegreeScale
  ring

theorem SourceProbabilityData.expectedDegreeScale_pos {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hx : 0 < x) (hy : 0 < sourceIntervalLength c x) : 0 < D.expectedDegreeScale S := by
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hu := D.gain_pos
  unfold expectedDegreeScale
  positivity

def sourcePinnedRelativeError (x : ℕ) : ℝ :=
  (1 / Real.log (x : ℝ) ^ 3) * (1 + 4 / Real.log (Real.log (x : ℝ)) ^ 10) +
    4 / Real.log (Real.log (x : ℝ)) ^ 10

def sourceDegreeRelativeError (x : ℕ) : ℝ :=
  sourcePinnedRelativeError x + 2 * (1 / Real.log (x : ℝ) ^ 3) * (1 + sourcePinnedRelativeError x)

theorem SourceProbabilityData.pinnedMass_error_scale {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime)
    (hx : 0 < x) (hy : 0 < sourceIntervalLength c x) (hL : 2 ≤ Real.log (x : ℝ))
    (a : ResidueAssignment S) {q : ℕ} (hq : q ∈ sourceSievingPrimes c x)
    (hBpos : 0 < D.pinnedTotalMass q) (hsurv : residueAssignmentAvoids S {(q : ℤ)} a)
    (hgood : q ∉ D.badPinnedVertices S a) :
    |D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension - D.expectedDegreeScale S| ≤
      sourcePinnedRelativeError x * D.expectedDegreeScale S := by
  classical
  have hσ := residueSieveDensity_pos (fun p hp => (hS p hp).one_lt)
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hpin : |D.pinnedNormalizedSurvival S q a /
      residueSieveDensity S ^ (D.dimension - 1) - 1| ≤ 1 / Real.log (x : ℝ) ^ 3 := by
    apply le_of_not_gt
    intro hb
    exact hgood (Finset.mem_filter.mpr ⟨hq, hsurv, hb⟩)
  have hpinEq : D.pinnedNormalizedSurvival S q a /
        residueSieveDensity S ^ (D.dimension - 1) =
      D.pinnedSurvivalMass S q a /
        (D.pinnedTotalMass q * residueSieveDensity S ^ (D.dimension - 1)) := by
    rw [D.pinnedNormalizedSurvival_eq]
    ring
  rw [hpinEq] at hpin
  obtain ⟨hqPrime, hxq, hqy⟩ := (mem_sourceSievingPrimes hy.le).mp hq
  have hB := D.pinnedTotalMass_error hqPrime hxq hqy
  have h := two_stage_relative_mass_error hBpos (pow_pos hσ (D.dimension - 1))
    (pow_pos hσ D.dimension) (by positivity) hpin hB
  have hpow : residueSieveDensity S ^ D.dimension =
      residueSieveDensity S ^ (D.dimension - 1) * residueSieveDensity S := by
    rw [← pow_succ]
    congr 1
    have hk := D.dimension_ge
    omega
  have hcenter : residueSieveDensity S ^ (D.dimension - 1) *
        (D.gain * x / (2 * sourceIntervalLength c x)) / residueSieveDensity S ^ D.dimension =
      D.expectedDegreeScale S := by
    rw [hpow]
    unfold expectedDegreeScale
    field_simp [hσ.ne', (pow_pos hσ (D.dimension - 1)).ne']
  rw [hcenter] at h
  exact h

theorem SourceProbabilityData.expectedDegree_error_scale {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x)
    (hshift : 2 * (D.dimension : ℝ) ^ 2 * x ≤ sourceIntervalLength c x)
    {S : Finset ℕ} (hS : ∀ p ∈ S, p.Prime) (hx : 0 < x)
    (hy : 0 < sourceIntervalLength c x) (hL : 2 ≤ Real.log (x : ℝ))
    (a : ResidueAssignment S) {q : ℕ} (hq : q ∈ sourceSievingPrimes c x)
    (hBpos : 0 < D.pinnedTotalMass q) (hsurv : residueAssignmentAvoids S {(q : ℤ)} a)
    (hgood : q ∉ D.badPinnedVertices S a) :
    |D.primeTupleExpectedDegree S (sourceSievingPrimes c x) a q - D.expectedDegreeScale S| ≤
      D.pinnedBadMass S q a + sourceDegreeRelativeError x * D.expectedDegreeScale S := by
  have hpin := D.pinnedMass_error_scale hS hx hy hL a hq hBpos hsurv hgood
  have htotal := D.primeTupleExpectedDegree_error_total hshift hS (sourceSievingPrimes c x)
    (fun q hq => ((mem_sourceSievingPrimes hy.le).mp hq).1) a hL hq
    ((mem_sourceSievingPrimes hy.le).mp hq).2.2 hsurv
  have hupper : D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension ≤
      (1 + sourcePinnedRelativeError x) * D.expectedDegreeScale S := by
    linarith [(abs_le.mp hpin).2]
  have hfactor : 0 ≤ 2 * (1 / Real.log (x : ℝ) ^ 3) := by positivity
  calc
    _ ≤ |D.primeTupleExpectedDegree S (sourceSievingPrimes c x) a q -
          D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension| +
        |D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension -
          D.expectedDegreeScale S| :=
      abs_sub_le _ _ _
    _ ≤ (D.pinnedBadMass S q a + 2 * (1 / Real.log (x : ℝ) ^ 3) *
          (D.pinnedSurvivalMass S q a / residueSieveDensity S ^ D.dimension)) +
        sourcePinnedRelativeError x * D.expectedDegreeScale S := add_le_add htotal hpin
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_left hupper hfactor
      unfold sourceDegreeRelativeError
      nlinarith

theorem eventually_source_expectedDegree_error_scale {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x, ∀ S : Finset ℕ,
      (∀ p ∈ S, p.Prime) → ∀ a : ResidueAssignment S, ∀ q ∈ sourceSievingPrimes c x,
      residueAssignmentAvoids S {(q : ℤ)} a → q ∉ D.badPinnedVertices S a →
      |D.primeTupleExpectedDegree S (sourceSievingPrimes c x) a q - D.expectedDegreeScale S| ≤
        D.pinnedBadMass S q a + sourceDegreeRelativeError x * D.expectedDegreeScale S := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  filter_upwards [eventually_sourceIntervalLength_bounds hc, eventually_pinnedTotalMass_lower hc,
    hlog.eventually (eventually_ge_atTop (2 : ℝ)), eventually_ge_atTop (1 : ℕ)]
    with x hy hB hL hx
  intro D S hS a q hq hsurv hgood
  have hxpos : 0 < x := by omega
  have hxR : (0 : ℝ) < x := by exact_mod_cast hxpos
  have hypos : 0 < sourceIntervalLength c x := hxR.trans_le hy.1
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hBpos : 0 < D.pinnedTotalMass q :=
    (by positivity : (0 : ℝ) < 1 / (4 * Real.log (x : ℝ) ^ 2)).trans_le (hB D q hq)
  have hk : (D.dimension : ℝ) ≤ Real.log (x : ℝ) ^ (1 / 10 : ℝ) := by
    simpa only [D.dimension_eq] using growingSieveDimension_le x
  exact D.expectedDegree_error_scale
    (hy.2.2 D.dimension hk) hS hxpos hypos hL a hq hBpos hsurv hgood

end

end Erdos4b.FGKMT
