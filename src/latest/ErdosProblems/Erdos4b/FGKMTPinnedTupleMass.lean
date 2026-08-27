/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos4b.FGKMTPrimeEdgeCodegree

/-! # Aggregated pinned source mass and its finite normalization -/

namespace Erdos4b.FGKMT

noncomputable section

open Filter
open scoped BigOperators

def SourceProbabilityData.pinnedTotalMass {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) : ℝ :=
  ∑ i : Fin D.dimension, ∑ p ∈ commonPinnedPrimeSet (x / 2) x,
    D.mass p ((q : ℤ) - (D.shifts i : ℤ) * p)

theorem SourceProbabilityData.pinnedTotalMass_error {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) {q : ℕ} (hq : q.Prime) (hxq : x < q)
    (hqy : (q : ℝ) ≤ sourceIntervalLength c x) :
    |D.pinnedTotalMass q - D.gain * x / (2 * sourceIntervalLength c x)| ≤
      (4 / Real.log (Real.log (x : ℝ)) ^ 10) *
        (D.gain * x / (2 * sourceIntervalLength c x)) := by
  have hk : (D.dimension : ℝ) ≠ 0 := by
    exact_mod_cast (by have hh := D.dimension_ge; omega : D.dimension ≠ 0)
  have hmain : (D.dimension : ℝ) * ((D.gain / D.dimension) * x /
      (2 * sourceIntervalLength c x)) = D.gain * x / (2 * sourceIntervalLength c x) := by
    field_simp [hk]
  have hsub : D.pinnedTotalMass q - D.gain * x / (2 * sourceIntervalLength c x) =
      ∑ i : Fin D.dimension,
        ((∑ p ∈ commonPinnedPrimeSet (x / 2) x,
            D.mass p ((q : ℤ) - (D.shifts i : ℤ) * p)) -
          (D.gain / D.dimension) * x / (2 * sourceIntervalLength c x)) := by
    simp only [pinnedTotalMass, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, hmain]
  rw [hsub]
  calc
    _ ≤ ∑ i : Fin D.dimension,
        |(∑ p ∈ commonPinnedPrimeSet (x / 2) x,
            D.mass p ((q : ℤ) - (D.shifts i : ℤ) * p)) -
          (D.gain / D.dimension) * x / (2 * sourceIntervalLength c x)| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i : Fin D.dimension,
        (4 / Real.log (Real.log (x : ℝ)) ^ 10) *
          ((D.gain / D.dimension) * x / (2 * sourceIntervalLength c x)) :=
      Finset.sum_le_sum fun i _hi => D.pinned_mean q hq hxq hqy i
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      calc
        _ = (4 / Real.log (Real.log (x : ℝ)) ^ 10) *
            ((D.dimension : ℝ) * ((D.gain / D.dimension) * x /
              (2 * sourceIntervalLength c x))) := by ring
        _ = _ := by rw [hmain]

theorem eventually_pinnedTotalMass_lower {c e : ℝ} (hc : 0 < c) :
    ∀ᶠ x : ℕ in atTop, ∀ D : SourceProbabilityData c e x,
      ∀ q ∈ sourceSievingPrimes c x,
        1 / (4 * Real.log (x : ℝ) ^ 2) ≤ D.pinnedTotalMass q := by
  have hlog : Tendsto (fun x : ℕ => Real.log (x : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hloglog := Real.tendsto_log_atTop.comp hlog
  filter_upwards [eventually_sourceIntervalLength_bounds hc,
    hlog.eventually (eventually_ge_atTop (1 : ℝ)),
    hloglog.eventually (eventually_ge_atTop (368640 : ℝ)),
    eventually_ge_atTop (1 : ℕ)] with x hy hL hv hx
  change 368640 ≤ Real.log (Real.log (x : ℝ)) at hv
  intro D q hq
  have hxR : (0 : ℝ) < x := by exact_mod_cast hx
  have hLpos : 0 < Real.log (x : ℝ) := by linarith
  have hypos : 0 < sourceIntervalLength c x := hxR.trans_le hy.1
  obtain ⟨hqPrime, hxq, hqy⟩ := (mem_sourceSievingPrimes hypos.le).mp hq
  have hu : 1 ≤ D.gain := by linarith [D.gain_lower]
  have hv2 : (2 : ℝ) ≤ Real.log (Real.log (x : ℝ)) := by linarith
  have heta : 4 / Real.log (Real.log (x : ℝ)) ^ 10 ≤ (1 / 2 : ℝ) := by
    have hh := pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 2) hv2 10
    apply (div_le_iff₀ (by positivity : 0 < Real.log (Real.log (x : ℝ)) ^ 10)).mpr
    norm_num at hh
    linarith
  have hGpos : 0 < D.gain * x / (2 * sourceIntervalLength c x) := by positivity
  have herr := D.pinnedTotalMass_error hqPrime hxq hqy
  have hhalf : (D.gain * x / (2 * sourceIntervalLength c x)) / 2 ≤ D.pinnedTotalMass q := by
    have hs := mul_le_mul_of_nonneg_right heta hGpos.le
    linarith [(abs_le.mp herr).1]
  have hG : 1 / (2 * Real.log (x : ℝ) ^ 2) ≤
      D.gain * x / (2 * sourceIntervalLength c x) := by
    apply (div_le_div_iff₀ (by positivity : 0 < 2 * Real.log (x : ℝ) ^ 2)
      (by positivity : 0 < 2 * sourceIntervalLength c x)).mpr
    have hs := mul_le_mul_of_nonneg_right hu
      (by positivity : 0 ≤ (x : ℝ) * Real.log (x : ℝ) ^ 2)
    nlinarith [hy.2.1]
  calc
    _ = (1 / (2 * Real.log (x : ℝ) ^ 2)) / 2 := by ring
    _ ≤ (D.gain * x / (2 * sourceIntervalLength c x)) / 2 :=
      div_le_div_of_nonneg_right hG (by norm_num)
    _ ≤ _ := hhalf

def SourceProbabilityData.pinnedTupleWeight {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (j : Fin D.dimension × ℕ) : ℝ :=
  D.mass j.2 ((q : ℤ) - (D.shifts j.1 : ℤ) * j.2)

theorem SourceProbabilityData.pinnedTupleWeight_sum {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) :
    (∑ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x, D.pinnedTupleWeight q j) =
      D.pinnedTotalMass q := by
  rw [Finset.sum_product]
  rfl

def SourceProbabilityData.pinnedNormalizedWeight {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (j : Fin D.dimension × ℕ) : ℝ :=
  D.pinnedTupleWeight q j / D.pinnedTotalMass q

theorem SourceProbabilityData.pinnedNormalizedWeight_nonneg {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (hq : 0 < D.pinnedTotalMass q)
    {j : Fin D.dimension × ℕ} (hj : j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x) :
    0 ≤ D.pinnedNormalizedWeight q j :=
  div_nonneg (D.mass_nonneg j.2 (Finset.mem_product.mp hj).2 _) hq.le

theorem SourceProbabilityData.pinnedNormalizedWeight_sum_one {c e : ℝ} {x : ℕ}
    (D : SourceProbabilityData c e x) (q : ℕ) (hq : 0 < D.pinnedTotalMass q) :
    (∑ j ∈ Finset.univ ×ˢ commonPinnedPrimeSet (x / 2) x, D.pinnedNormalizedWeight q j) = 1 := by
  simp only [pinnedNormalizedWeight, ← Finset.sum_div, D.pinnedTupleWeight_sum, div_self hq.ne']

end

end Erdos4b.FGKMT

#print axioms Erdos4b.FGKMT.SourceProbabilityData.pinnedTotalMass_error
#print axioms Erdos4b.FGKMT.eventually_pinnedTotalMass_lower
#print axioms Erdos4b.FGKMT.SourceProbabilityData.pinnedNormalizedWeight_sum_one
