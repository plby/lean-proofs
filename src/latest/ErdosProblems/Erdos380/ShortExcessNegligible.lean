import ErdosProblems.Erdos380.ShortExcessScale
import ErdosProblems.Erdos380.IneligibleScale
import ErdosProblems.Erdos380.SingletonScaleLower

/-! # The short-interval excess is negligible relative to the singleton count -/

open Filter Asymptotics
open scoped Topology

namespace Erdos380

lemma scale_quotient_mono (N : ℕ) {a b : ℕ} (hab : a ≤ b) :
    (N : ℝ) / (scaleBase N : ℝ) ^ b ≤ (N : ℝ) / (scaleBase N : ℝ) ^ a := by
  have hS1 : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast one_le_scaleBase N
  exact div_le_div_of_nonneg_left (Nat.cast_nonneg N) (pow_pos (by linarith) a)
    (pow_le_pow_right₀ hS1 hab)

lemma scale_quotient_succ_mul (N a : ℕ) :
    ((N : ℝ) / (scaleBase N : ℝ) ^ (a + 1)) * scaleBase N =
      (N : ℝ) / (scaleBase N : ℝ) ^ a := by
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  rw [pow_succ]
  field_simp

lemma eventually_initial_short_error_bound (E : ℕ) : ∀ᶠ N : ℕ in atTop,
    (E : ℝ) + Nat.sqrt N + 2 * shortWidth N ≤ 4 * N / (scaleBase N : ℝ) ^ 2002 := by
  filter_upwards [eventually_scaleBase_pow_le 4004,
    eventually_logarithmicCeiling_pow_le_scaleBase 20,
    scaleBase_tendsto_atTop.eventually (eventually_ge_atTop E)] with N hpow hW hE
  have hS1 := one_le_scaleBase N
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast (by omega : 0 < scaleBase N)
  have hsmallpow : scaleBase N ^ 2003 ≤ N := (pow_le_pow_right₀ hS1 (by decide : 2003 ≤ 4004)).trans hpow
  have hroot : scaleBase N ^ 2002 ≤ Nat.sqrt N := by
    apply Nat.le_sqrt'.mpr
    rw [← pow_mul]
    exact hpow
  have hrootmul : Nat.sqrt N * scaleBase N ^ 2002 ≤ N := by
    calc
      _ ≤ Nat.sqrt N * Nat.sqrt N := Nat.mul_le_mul_left _ hroot
      _ = Nat.sqrt N ^ 2 := (pow_two _).symm
      _ ≤ N := Nat.sqrt_le' N
  have hEmul : E * scaleBase N ^ 2002 ≤ N := by
    calc
      _ ≤ scaleBase N * scaleBase N ^ 2002 := Nat.mul_le_mul_right _ hE
      _ = scaleBase N ^ 2003 := (pow_succ' _ _).symm
      _ ≤ N := hsmallpow
  have hWmul : shortWidth N * scaleBase N ^ 2002 ≤ N := by
    calc
      _ ≤ scaleBase N * scaleBase N ^ 2002 := Nat.mul_le_mul_right _ hW
      _ = scaleBase N ^ 2003 := (pow_succ' _ _).symm
      _ ≤ N := hsmallpow
  have hrootR : (Nat.sqrt N : ℝ) ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2002 := by
    apply (le_div_iff₀ (pow_pos hSpos 2002)).mpr
    exact_mod_cast hrootmul
  have hER : (E : ℝ) ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2002 := by
    apply (le_div_iff₀ (pow_pos hSpos 2002)).mpr
    exact_mod_cast hEmul
  have hWR : (shortWidth N : ℝ) ≤ (N : ℝ) / (scaleBase N : ℝ) ^ 2002 := by
    apply (le_div_iff₀ (pow_pos hSpos 2002)).mpr
    exact_mod_cast hWmul
  rw [mul_div_assoc]
  linarith

lemma short_ineligible_error_bound {N : ℕ} (hW : shortWidth N ≤ scaleBase N)
    (hI : ((ineligibleSingletons N (cofactorScale N) (mixingBase N ^ 110)).card : ℝ) ≤
      (N : ℝ) / (scaleBase N : ℝ) ^ 2004) :
    (2 * shortWidth N + 1 : ℝ) * (ineligibleSingletons N (cofactorScale N) (mixingBase N ^ 110)).card ≤
      3 * N / (scaleBase N : ℝ) ^ 2002 := by
  have hS1 : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast one_le_scaleBase N
  have hWR : (shortWidth N : ℝ) ≤ scaleBase N := by exact_mod_cast hW
  have hcoef : (2 * shortWidth N + 1 : ℝ) ≤ 3 * scaleBase N := by linarith
  calc
    _ ≤ (3 * scaleBase N : ℝ) * ((N : ℝ) / (scaleBase N : ℝ) ^ 2004) :=
      mul_le_mul hcoef hI (Nat.cast_nonneg _) (by positivity)
    _ = 3 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2003) := by
      rw [show 2004 = 2003 + 1 from rfl]
      have h := scale_quotient_succ_mul N 2003
      calc
        _ = 3 * (((N : ℝ) / (scaleBase N : ℝ) ^ (2003 + 1)) * scaleBase N) := by ring
        _ = _ := by rw [h]
    _ ≤ 3 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2002) :=
      mul_le_mul_of_nonneg_left (scale_quotient_mono N (by decide : 2002 ≤ 2003)) (by norm_num)
    _ = _ := by ring

lemma short_square_error_bound {N : ℕ} (hW : shortWidth N ≤ scaleBase N) :
    (8 * shortWidth N + 4 : ℝ) * N / (squareScale N + 1) ≤
      12 * N / (scaleBase N : ℝ) ^ 2002 := by
  have hS1 : (1 : ℝ) ≤ scaleBase N := by exact_mod_cast one_le_scaleBase N
  have hSpos : (0 : ℝ) < scaleBase N := by linarith
  have hWR : (shortWidth N : ℝ) ≤ scaleBase N := by exact_mod_cast hW
  have hcoef : (8 * shortWidth N + 4 : ℝ) ≤ 12 * scaleBase N := by linarith
  calc
    _ ≤ (12 * scaleBase N : ℝ) * N / (squareScale N + 1) := by gcongr
    _ ≤ (12 * scaleBase N : ℝ) * N / (scaleBase N : ℝ) ^ 3000 := by
      apply div_le_div_of_nonneg_left (by positivity) (pow_pos hSpos 3000)
      simp only [squareScale, Nat.cast_pow]
      linarith
    _ = 12 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2999) := by
      rw [show 3000 = 2999 + 1 from rfl]
      have h := scale_quotient_succ_mul N 2999
      calc
        _ = 12 * (((N : ℝ) / (scaleBase N : ℝ) ^ (2999 + 1)) * scaleBase N) := by ring
        _ = _ := by rw [h]
    _ ≤ 12 * ((N : ℝ) / (scaleBase N : ℝ) ^ 2002) :=
      mul_le_mul_of_nonneg_left (scale_quotient_mono N (by decide : 2002 ≤ 2999)) (by norm_num)
    _ = _ := by ring

theorem exists_eventually_shortExcess_relative_bound : ∃ K : ℝ, 0 < K ∧ ∀ᶠ N : ℕ in atTop,
    ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ) ≤
      (19 / (scaleBase N : ℝ) + K * neighborErrorFactor N) * (singletonBadUpTo N).card := by
  obtain ⟨K, hK, E, hbound⟩ := exists_eventually_shortExcess_scale_bound
  refine ⟨K, hK, ?_⟩
  filter_upwards [hbound, eventually_initial_short_error_bound E,
    eventually_logarithmicCeiling_pow_le_scaleBase 20, eventually_ineligibleSingletons_parameter_bound,
    eventually_singletonBadUpTo_scale_lower] with N hcount hinit hW hI hA
  have hthin := short_ineligible_error_bound hW hI
  have hsquare := short_square_error_bound hW
  have hsum : ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ) ≤
      19 * N / (scaleBase N : ℝ) ^ 2002 + K * neighborErrorFactor N * (singletonBadUpTo N).card := by
    simp only [mul_div_assoc] at hcount hinit hthin hsquare ⊢
    linarith
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  have hnorm : (N : ℝ) / (scaleBase N : ℝ) ^ 2002 ≤ (singletonBadUpTo N).card / (scaleBase N : ℝ) := by
    apply (le_div_iff₀ hSpos).mpr
    exact (scale_quotient_succ_mul N 2001).le.trans hA
  calc
    _ ≤ _ := hsum
    _ ≤ 19 * ((singletonBadUpTo N).card / (scaleBase N : ℝ)) +
        K * neighborErrorFactor N * (singletonBadUpTo N).card := by
      have hm := mul_le_mul_of_nonneg_left hnorm (by norm_num : (0 : ℝ) ≤ 19)
      simpa only [mul_div_assoc] using add_le_add hm
        (le_refl (K * neighborErrorFactor N * (singletonBadUpTo N).card))
    _ = _ := by ring

theorem eventually_singletonBadUpTo_card_pos : ∀ᶠ N : ℕ in atTop,
    (0 : ℝ) < (singletonBadUpTo N).card := by
  filter_upwards [eventually_singletonBadUpTo_scale_lower, eventually_ge_atTop 1] with N hA hN
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hSpos : (0 : ℝ) < scaleBase N := by exact_mod_cast
    (lt_of_lt_of_le Nat.zero_lt_one (one_le_scaleBase N))
  exact (div_pos hNpos (pow_pos hSpos 2001)).trans_le hA

theorem shortExcess_isLittleO_singletonCount :
    (fun N : ℕ => ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ)) =o[atTop]
      (fun N : ℕ => ((singletonBadUpTo N).card : ℝ)) := by
  obtain ⟨K, hK, hbound⟩ := exists_eventually_shortExcess_relative_bound
  have hzero : Tendsto (fun N : ℕ => 19 / (scaleBase N : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop (tendsto_natCast_atTop_atTop.comp scaleBase_tendsto_atTop)
  have hmajor := hzero.add (neighborErrorFactor_tendsto_zero.const_mul K)
  simp only [mul_zero, add_zero] at hmajor
  have hrange : ∀ᶠ N : ℕ in atTop,
      0 ≤ ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ) / (singletonBadUpTo N).card ∧
      ((shortExcessPointsUpTo N (shortWidth N)).card : ℝ) / (singletonBadUpTo N).card ≤
        19 / (scaleBase N : ℝ) + K * neighborErrorFactor N := by
    filter_upwards [hbound, eventually_singletonBadUpTo_card_pos] with N hN hA
    exact ⟨div_nonneg (Nat.cast_nonneg _) hA.le, (div_le_iff₀ hA).mpr hN⟩
  apply Asymptotics.isLittleO_of_tendsto'
  · filter_upwards [eventually_singletonBadUpTo_card_pos] with N hN
    exact fun h => (hN.ne' h).elim
  · exact squeeze_zero' (hrange.mono fun _ h => h.1) (hrange.mono fun _ h => h.2) hmajor

end Erdos380
