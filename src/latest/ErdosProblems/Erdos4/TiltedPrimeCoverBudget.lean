import ErdosProblems.Erdos4.TiltedPrimeExposure
import ErdosProblems.Erdos4.FGKMTGrowingPartitionBudget

/-! The exceptional primes and the final hypergraph remainder fit an arbitrarily small reserve. -/

namespace Erdos4.Tilted

open Filter FGKMT

theorem prime_cover_numeric_budget {σ x Y L j G K C η N M κ ε : ℝ}
    (hσ : 0 ≤ σ) (hx : 0 ≤ x) (hY : 0 ≤ Y) (hL : 0 < L) (hj : 0 < j)
    (hG : 0 ≤ G) (hK : 0 ≤ K) (hC : 0 ≤ C) (hN : 0 ≤ N) (_hκ : 0 ≤ κ)
    (hη : η ≤ 1 / j ^ 2) (hcount : N ≤ K * Y / L) (hbad : M ≤ C * Y / (L * j ^ 2))
    (hproduct : σ * Y ≤ G * x * j) (hκupper : κ ≤ 2 / j)
    (hcoeff : (C + K) * G / j ≤ ε) :
    σ * (M + η * N) + 2 * κ * (σ * N) ≤ (ε + 4 * K * G) * x / L := by
  have hn : σ * N ≤ K * G * (x * j / L) := by
    calc
      _ ≤ σ * (K * Y / L) := mul_le_mul_of_nonneg_left hcount hσ
      _ = K * (σ * Y) / L := by ring
      _ ≤ K * (G * x * j) / L :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct hK) hL.le
      _ = _ := by ring
  have hηN : η * N ≤ K * Y / (L * j ^ 2) := by
    calc
      _ ≤ (1 / j ^ 2) * (K * Y / L) := mul_le_mul hη hcount hN (by positivity)
      _ = _ := by ring
  have hcombined : M + η * N ≤ (C + K) * Y / (L * j ^ 2) :=
    (add_le_add hbad hηN).trans_eq (by ring)
  have hmiss : σ * (M + η * N) ≤ ε * x / L := by
    calc
      _ ≤ σ * ((C + K) * Y / (L * j ^ 2)) := mul_le_mul_of_nonneg_left hcombined hσ
      _ = (C + K) * (σ * Y) / (L * j ^ 2) := by ring
      _ ≤ (C + K) * (G * x * j) / (L * j ^ 2) :=
        div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hproduct (by positivity)) (by positivity)
      _ = ((C + K) * G / j) * x / L := by field_simp
      _ ≤ _ := div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_right hcoeff hx) hL.le
  have hcover : 2 * κ * (σ * N) ≤ 4 * K * G * x / L := by
    calc
      _ ≤ 2 * (2 / j) * (K * G * (x * j / L)) :=
        mul_le_mul (mul_le_mul_of_nonneg_left hκupper (by norm_num)) hn (mul_nonneg hσ hN) (by positivity)
      _ = _ := by field_simp; ring
  exact (add_le_add hmiss hcover).trans_eq (by ring)

theorem eventually_prime_cover_numeric_budget {c G C ε : ℝ}
    (hc : 0 < c) (hG : 0 < G) (hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ x : ℕ in atTop, ∀ D : PrimeExposureData c x G C,
      primeDensity x * ((D.bad.card : ℝ) +
          (1 / Real.log (x : ℝ) ^ (40 : ℕ)) * (primeTargets c x).card) +
        2 * growingCoverDensity x * (primeDensity x * (primeTargets c x).card) ≤
          (ε + 4 * (3 * Real.log 2) * G) * (x : ℝ) / Real.log (x : ℝ) := by
  have hjtop : Tendsto (fun x => (growingIndex x : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop.comp growingIndex_tendsto
  filter_upwards [eventually_gapTarget_bounds hc, eventually_growing_target_count,
    eventually_growing_count_budgets, eventually_growing_cover_parameters,
    hjtop.eventually (eventually_ge_atTop ((C + 3 * Real.log 2) * G / ε))]
    with x hY hcount hcounts hpar hj
  intro D
  have hjpos : (0 : ℝ) < growingIndex x := by exact_mod_cast hcounts.1
  have hLpos : 0 < Real.log (x : ℝ) := hjpos.trans_le hpar.2.1
  have hcoeff : (C + 3 * Real.log 2) * G / (growingIndex x : ℝ) ≤ ε := by
    apply (div_le_iff₀ hjpos).mpr
    have hh := (div_le_iff₀ hε).mp hj
    nlinarith only [hh]
  exact prime_cover_numeric_budget (primeDensity_pos x).le (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    hLpos hjpos hG.le (by have hh := Real.log_pos (by norm_num : (1 : ℝ) < 2); positivity)
    hC.le (Nat.cast_nonneg _) (by unfold growingCoverDensity; positivity)
    hcounts.2.2 (hcount (gapTarget c x) hY.2.1) D.bad_count D.density_target hpar.2.2.2.2.2 hcoeff

end Erdos4.Tilted
