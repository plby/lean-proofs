import ErdosProblems.Erdos4.OuterAtomDecay
import ErdosProblems.Erdos4.OuterPrimeSupply

/-!
# Prime and smooth cleanup costs on the outer ray

The short initial prime-target segment has negligible survival cost.
One fixed Rankin loss parameter makes the entire smooth set negligible
relative to the reserve-prime scale. The zero-residue survivor
classification also applies eventually at every fixed length multiplier.
-/

open Filter
open scoped BigOperators Topology

namespace Erdos4.OuterCleanup

open SmoothParameters ChebyshevIntervals OuterRay OuterAccuracy OuterDensity OuterAtomDecay

theorem primeCounting_scaled {t U : ℕ} (ht : 2 ≤ t) (htU : t ≤ U)
    (hπ : (Nat.primeCounting U : ℝ) ≤ (3 * Real.log 2) * U / Real.log U) :
    (Nat.primeCounting U : ℝ) ≤ (3 * Real.log 2) * U / Real.log t := by
  have hlog : 0 < Real.log (t : ℝ) := Real.log_pos (by exact_mod_cast ht)
  exact hπ.trans (div_le_div_of_nonneg_left (by positivity) hlog
    (Real.log_le_log (by exact_mod_cast (show 0 < t by omega)) (by exact_mod_cast htU)))

theorem eventually_target_count (a : ℕ) {D : ℕ} (hD : 1 ≤ D) :
    ∀ᶠ r : ℕ in atTop,
      ((primeInterval (base a r) (length a D r)).card : ℝ) ≤
        (3 * Real.log 2) * length a D r / Real.log (primaryFrontier a r : ℝ) := by
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_length a hD).eventually eventually_primeCounting_upper] with r hr hπ
  have hcard : (primeInterval (base a r) (length a D r)).card ≤ Nat.primeCounting (length a D r) := by
    simpa only [primeInterval, Nat.primesLE_card_eq_primeCounting] using
      Finset.card_le_card (Finset.sdiff_subset :
        primeInterval (base a r) (length a D r) ⊆ (length a D r).primesLE)
  exact (show ((primeInterval (base a r) (length a D r)).card : ℝ) ≤
      Nat.primeCounting (length a D r) by exact_mod_cast hcard).trans
    (primeCounting_scaled (primary_two_le a r) (primary_le_length a hD hr) hπ)

theorem eventually_small_prime_cost (a H : ℕ) (hH : 1 ≤ H) {C ε : ℝ}
    (_hC : 0 < C) (hε : 0 < ε) :
    ∀ᶠ r : ℕ in atTop, ∀ σ : ℝ, 0 ≤ σ → σ ≤ C / ((r : ℝ) * core r) →
      σ * Nat.primeCounting (H * frontier a r) ≤
        ε * frontier a r / Real.log (primaryFrontier a r : ℝ) := by
  have hHtop : Tendsto (fun r : ℕ => H * frontier a r) atTop atTop :=
    tendsto_atTop_mono (fun r => by simpa using Nat.mul_le_mul_right (frontier a r) hH)
      (tendsto_frontier a)
  have hVtop : Tendsto (fun r : ℕ => (core r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_core
  filter_upwards [eventually_ge_atTop 1, hHtop.eventually eventually_primeCounting_upper,
    hVtop.eventually (eventually_ge_atTop ((3 * Real.log 2) * C * H / ε))] with r hr hπ hlarge
  intro σ hσ0 hσ
  have hrR : (1 : ℝ) ≤ r := by exact_mod_cast hr
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hs : 0 < (r : ℝ) * core r := mul_pos (by linarith) hV
  have hlog : 0 < Real.log (primaryFrontier a r : ℝ) :=
    Real.log_pos (by exact_mod_cast primary_two_le a r)
  have hXHX : frontier a r ≤ H * frontier a r := by
    simpa using Nat.mul_le_mul_right (frontier a r) hH
  have hcount := primeCounting_scaled (primary_two_le a r)
    (((primary_le_base a r).trans (base_le_frontier a r)).trans hXHX) hπ
  have hlarge' : (3 * Real.log 2) * C * H ≤ ε * ((r : ℝ) * core r) := by
    have hh := (div_le_iff₀ hε).mp hlarge
    have hcoord : (core r : ℝ) ≤ (r : ℝ) * core r :=
      le_mul_of_one_le_left hV.le hrR
    have hh' := mul_le_mul_of_nonneg_left hcoord hε.le
    nlinarith only [hh, hh']
  have hcoeff : (C / ((r : ℝ) * core r)) * ((3 * Real.log 2) * H) ≤ ε := by
    rw [div_mul_eq_mul_div]
    apply (div_le_iff₀ hs).mpr
    nlinarith only [hlarge']
  calc
    _ ≤ σ * ((3 * Real.log 2) * (H * frontier a r : ℕ) /
        Real.log (primaryFrontier a r : ℝ)) := mul_le_mul_of_nonneg_left hcount hσ0
    _ ≤ (C / ((r : ℝ) * core r)) * ((3 * Real.log 2) * (H * frontier a r : ℕ) /
        Real.log (primaryFrontier a r : ℝ)) := mul_le_mul_of_nonneg_right hσ (by positivity)
    _ = ((C / ((r : ℝ) * core r)) * ((3 * Real.log 2) * H)) * frontier a r /
        Real.log (primaryFrontier a r : ℝ) := by push_cast; ring
    _ ≤ _ := div_le_div_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (Nat.cast_nonneg _)) hlog.le

theorem eventually_length_le_zeroCutoff (a D : ℕ) :
    ∀ᶠ r : ℕ in atTop, length a D r ≤ smallCutoff a r * base a r := by
  filter_upwards [tendsto_core.eventually (eventually_ge_atTop (256 * D))] with r hr
  have hcoeff : 256 * D ≤ core r ^ 2 := hr.trans (Nat.le_pow (by norm_num))
  have hh := Nat.mul_le_mul_right (core r ^ 2) hcoeff
  have hfour : 256 * D * core r ^ 2 ≤ smallCutoff a r := by
    calc
      _ ≤ core r ^ 2 * core r ^ 2 := hh
      _ = core r ^ 4 := by ring
      _ ≤ primaryExponent a r ^ 4 := Nat.pow_le_pow_left (core_le_primaryExponent a r) 4
  calc
    _ ≤ (256 * D) * primaryFrontier a r ^ 50 * core r ^ 2 := length_le_core_square a D r
    _ = (256 * D * core r ^ 2) * base a r := by unfold OuterRay.base; ring
    _ ≤ _ := Nat.mul_le_mul_right (base a r) hfour

theorem exists_negligible_smooth :
    ∃ a : ℕ, ∀ D : ℕ, 1 ≤ D → ∀ ε : ℝ, 0 < ε → ∀ᶠ r : ℕ in atTop,
      ((Nat.smoothNumbersUpTo (length a D r) (smoothFrontier r + 1)).card : ℝ) ≤
        ε * frontier a r / Real.log (primaryFrontier a r : ℝ) := by
  obtain ⟨a, hsmooth⟩ := PlainSmoothBound.exists_uniform_plain_smooth_bound
  refine ⟨a, ?_⟩
  intro D hD ε hε
  have hVtop : Tendsto (fun r : ℕ => (core r : ℝ)) atTop atTop :=
    (tendsto_natCast_atTop_atTop (R := ℝ)).comp tendsto_core
  filter_upwards [eventually_ge_atTop (max a 4),
    hVtop.eventually (eventually_ge_atTop (D * Real.log 2 / ε))] with r hr hlarge
  have hra : a ≤ r := (le_max_left _ _).trans hr
  have hr4 : 4 ≤ r := (le_max_right _ _).trans hr
  have hr1 : 1 ≤ r := by omega
  have hV : (0 : ℝ) < core r := by exact_mod_cast core_pos r
  have hV1 : (1 : ℝ) ≤ core r := by exact_mod_cast core_pos r
  have hlog : 0 < Real.log (primaryFrontier a r : ℝ) :=
    Real.log_pos (by exact_mod_cast primary_two_le a r)
  have hlog2 : 0 ≤ Real.log (2 : ℝ) := (Real.log_pos (by norm_num)).le
  have hEsq : (primaryExponent a r : ℝ) ≤ (core r : ℝ) ^ 2 := by
    exact_mod_cast primaryExponent_le_core_sq_of (stable_exponent_comparison hra hr4)
  have hlogupper : Real.log (primaryFrontier a r : ℝ) ≤ (core r : ℝ) ^ 2 * Real.log 2 := by
    rw [log_primary]
    exact mul_le_mul_of_nonneg_right hEsq hlog2
  have hlarge' : (D : ℝ) * Real.log 2 ≤ ε * (core r : ℝ) ^ 4 := by
    have hh := (div_le_iff₀ hε).mp hlarge
    have hpow : (core r : ℝ) ≤ (core r : ℝ) ^ 4 := le_self_pow₀ hV1 (by norm_num)
    exact hh.trans (by nlinarith [mul_le_mul_of_nonneg_left hpow hε.le])
  have hmain : (D : ℝ) * Real.log (primaryFrontier a r : ℝ) ≤ ε * (core r : ℝ) ^ 6 := by
    calc
      _ ≤ D * ((core r : ℝ) ^ 2 * Real.log 2) :=
        mul_le_mul_of_nonneg_left hlogupper (Nat.cast_nonneg _)
      _ = (D * Real.log 2) * (core r : ℝ) ^ 2 := by ring
      _ ≤ (ε * (core r : ℝ) ^ 4) * (core r : ℝ) ^ 2 :=
        mul_le_mul_of_nonneg_right hlarge' (sq_nonneg _)
      _ = _ := by ring
  have hs := hsmooth r hr1 (256 * D) (length a D r) (primary_le_length a hD hr1)
    (by exact_mod_cast length_le_core_square a D r)
  have hfront : (256 * (D : ℝ)) * (primaryFrontier a r : ℝ) ^ 50 = D * frontier a r := by
    rw [OuterRay.frontier, OuterRay.base]
    push_cast
    ring
  rw [hfront] at hs
  apply hs.trans
  apply (div_le_div_iff₀ (pow_pos hV 6) hlog).mpr
  have hh := mul_le_mul_of_nonneg_right hmain (Nat.cast_nonneg (frontier a r) : (0 : ℝ) ≤ frontier a r)
  nlinarith only [hh]

end Erdos4.OuterCleanup
