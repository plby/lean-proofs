import ErdosProblems.Erdos4.FGKMTPrimeGapEndpoint
import ErdosProblems.Erdos4.FGKMTEndpointScale

/-! The full FGKMT18 bound below every sufficiently large real endpoint. -/

namespace Erdos4.FGKMT

open Filter

theorem endpointParameter_exp_le {D : ℕ} (hD : 1 ≤ D) {X : ℝ} (hX : 1 ≤ X) :
    Real.exp ((D : ℝ) * endpointParameter D X) ≤ X := by
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  have hXpos : 0 < X := lt_of_lt_of_le (by norm_num) hX
  have hlogX : 0 ≤ Real.log X := Real.log_nonneg hX
  have hfloor : (endpointParameter D X : ℝ) ≤ Real.log X / (2 * (D : ℝ)) :=
    Nat.floor_le (div_nonneg hlogX (by positivity))
  have hbound : (D : ℝ) * endpointParameter D X ≤ Real.log X := by
    calc
      _ ≤ (D : ℝ) * (Real.log X / (2 * (D : ℝ))) := mul_le_mul_of_nonneg_left hfloor hDpos.le
      _ = Real.log X / 2 := by field_simp [hDpos.ne']
      _ ≤ _ := by linarith
  exact (Real.exp_le_exp.mpr hbound).trans_eq (Real.exp_log hXpos)

theorem exists_all_endpoint_gaps :
    ∃ c : ℝ, 0 < c ∧ ∀ᶠ X : ℝ in atTop,
      ∃ n : ℕ, (Nat.nth Nat.Prime (n + 1) : ℝ) ≤ X ∧
        c * gapScale X ≤ (Nat.nth Nat.Prime (n + 1) : ℝ) - Nat.nth Nat.Prime n := by
  obtain ⟨c, D, hc, hD, hgaps⟩ := exists_growing_prime_gaps
  have hDpos : (0 : ℝ) < D := by exact_mod_cast hD
  refine ⟨c / (32 * (D : ℝ)), by positivity, ?_⟩
  have htendsto := endpointParameter_tendsto hD
  filter_upwards [htendsto.eventually hgaps,
    htendsto.eventually (eventually_growing_gap_length_bounds hc),
    eventually_endpoint_scale_compare hD, eventually_ge_atTop (1 : ℝ)]
    with X hgap hlength hcompare hX
  let x := endpointParameter D X
  obtain ⟨n, hn, hgap⟩ := hgap
  refine ⟨n, hn.trans (endpointParameter_exp_le hD hX), ?_⟩
  calc
    _ = (c / 2) * (gapScale X / (16 * (D : ℝ))) := by field_simp [hDpos.ne'] <;> ring
    _ ≤ (c / 2) * ((x : ℝ) * growingOuterScale x) :=
      mul_le_mul_of_nonneg_left hcompare (by positivity)
    _ = (c / 2) * (x : ℝ) * growingOuterScale x := by ring
    _ ≤ (growingGapLength c x : ℝ) := hlength.2.2.2.2.2.1
    _ ≤ _ := hgap.le

end Erdos4.FGKMT
