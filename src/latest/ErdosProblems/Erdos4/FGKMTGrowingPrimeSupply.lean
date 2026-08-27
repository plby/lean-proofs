import ErdosProblems.Erdos4.FGKMTGrowingRadius
import ErdosProblems.Erdos4.ChebyshevIntervals

/-! A fixed-ratio source-prime interval at every large endpoint, above the Gram cutoff. -/

namespace Erdos4.FGKMT

open Filter ChebyshevIntervals

def growingSourcePrimes (x : ℕ) : Finset ℕ := primeInterval (x / 32) x

theorem mem_growingSourcePrimes {x p : ℕ} :
    p ∈ growingSourcePrimes x ↔ p.Prime ∧ x / 32 < p ∧ p ≤ x := mem_primeInterval

theorem growingRadius_sq_le_source_start {x : ℕ} (hR : 2 ≤ growingRadius x) :
    growingRadius x ^ 2 ≤ x / 32 := by
  have hR1 : 1 ≤ growingRadius x := by omega
  have h32 : 32 ≤ growingRadius x ^ 5 := by
    simpa using Nat.pow_le_pow_left hR 5
  apply (Nat.le_div_iff_mul_le (by norm_num : 0 < (32 : ℕ))).mpr
  calc
    _ ≤ growingRadius x ^ 2 * growingRadius x ^ 5 := Nat.mul_le_mul_left _ h32
    _ = growingRadius x ^ 7 := by ring
    _ ≤ growingRadius x ^ 50 := Nat.pow_le_pow_right hR1 (by norm_num)
    _ ≤ x := growingRadius_pow_fifty_le x

theorem eventually_growing_source_count :
    ∀ᶠ x : ℕ in atTop,
      (Real.log 2 / 64) * x / Real.log (x : ℝ) ≤ (growingSourcePrimes x).card := by
  have hdiv : Tendsto (fun x : ℕ => x / 32) atTop atTop := by
    apply tendsto_atTop.2
    intro n
    filter_upwards [eventually_ge_atTop (32 * n)] with x hx
    omega
  filter_upwards [hdiv.eventually eventually_primeInterval_lower, eventually_ge_atTop 64]
    with x hsource hx
  have hn : 16 ≤ x / 32 := hsource.1
  have hnpos : (0 : ℝ) < (x / 32 : ℕ) := by exact_mod_cast (by omega : 0 < x / 32)
  have hlogn : 0 < Real.log (x / 32 : ℕ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x / 32 by omega))
  have hlogx : 0 < Real.log (x : ℝ) :=
    Real.log_pos (by exact_mod_cast (show 1 < x by omega))
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hhalf : (x : ℝ) / 64 ≤ (x / 32 : ℕ) := by
    have hh : x ≤ 64 * (x / 32) := by omega
    have hhr : (x : ℝ) ≤ 64 * (x / 32 : ℕ) := by exact_mod_cast hh
    linarith
  have hlogle : Real.log (x / 32 : ℕ) ≤ Real.log (x : ℝ) :=
    Real.log_le_log hnpos (by exact_mod_cast Nat.div_le_self x 32)
  have hsub : primeInterval (x / 32) (16 * (x / 32)) ⊆ growingSourcePrimes x := by
    intro p hp
    have hh := mem_primeInterval.mp hp
    exact mem_growingSourcePrimes.mpr ⟨hh.1, hh.2.1, by omega⟩
  calc
    _ = Real.log 2 * ((x : ℝ) / 64) / Real.log (x : ℝ) := by ring
    _ ≤ Real.log 2 * (x / 32 : ℕ) / Real.log (x : ℝ) :=
      div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hhalf hlog2.le) hlogx.le
    _ ≤ Real.log 2 * (x / 32 : ℕ) / Real.log (x / 32 : ℕ) :=
      div_le_div_of_nonneg_left (by positivity) hlogn hlogle
    _ ≤ (primeInterval (x / 32) (16 * (x / 32))).card := hsource.2
    _ ≤ _ := by exact_mod_cast Finset.card_le_card hsub

theorem eventually_growing_source_supply :
    ∀ᶠ x : ℕ in atTop,
      2 ≤ x ∧ growingRadius x ^ 2 ≤ x / 32 ∧
      (Real.log 2 / 64) * x / Real.log (x : ℝ) ≤ (growingSourcePrimes x).card ∧
      (x : ℝ) / Real.log (x : ℝ) ^ 2 ≤ (growingSourcePrimes x).card := by
  have hlogTop := Real.tendsto_log_atTop.comp (tendsto_natCast_atTop_atTop (R := ℝ))
  filter_upwards [eventually_growing_source_count, eventually_growingRadius_bounds,
    hlogTop.eventually (eventually_ge_atTop (64 / Real.log 2)), eventually_ge_atTop 2]
    with x hcount hR hlarge hx
  refine ⟨hx, growingRadius_sq_le_source_start hR.1, hcount, ?_⟩
  have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
  have hlogx : 0 < Real.log (x : ℝ) := Real.log_pos (by exact_mod_cast hx)
  change 64 / Real.log 2 ≤ Real.log (x : ℝ) at hlarge
  have hprod : 64 ≤ Real.log (x : ℝ) * Real.log 2 := (div_le_iff₀ hlog2).mp hlarge
  have hcoef : 1 ≤ (Real.log 2 / 64) * Real.log (x : ℝ) := by nlinarith
  apply le_trans _ hcount
  calc
    _ ≤ ((x : ℝ) * ((Real.log 2 / 64) * Real.log (x : ℝ))) / Real.log (x : ℝ) ^ 2 :=
      div_le_div_of_nonneg_right
        (by simpa only [mul_one] using mul_le_mul_of_nonneg_left hcoef (Nat.cast_nonneg x))
        (sq_nonneg _)
    _ = _ := by field_simp

end Erdos4.FGKMT
