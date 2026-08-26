import ErdosProblems.Erdos421.RoughCutoffTransfer
import ErdosProblems.Erdos421.CofactorCutoffTransfer
import ErdosProblems.Erdos421.TransferSieveAccuracy
import ErdosProblems.Erdos421.RoundedEulerError

/-! # The actual intermediate-cutoff windows have arbitrarily small integral error -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem intermediate_windows_l1 {σ e : ℝ} (hσ : 0 < σ) (he : 0 < e) (he' : e < 9 / 10) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ δ₁ δ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₁ → δ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ δ₂ → δ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) δ₁ y -
          logarithmicRoughWindow (3 * X) (intermediatePrimeCutoff X) δ₂ y|) ≤ σ / Real.log X ∧
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        |logarithmicPrimeCofactorWindow
            (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X))
            (3 * X) (intermediatePrimeCutoff X) δ₁ y -
          logarithmicPrimeCofactorWindow
            (sievePrimes (intermediatePrimeCutoff X) (outerPrimeCutoff X))
            (3 * X) (intermediatePrimeCutoff X) δ₂ y|) ≤ σ / Real.log X := by
  obtain ⟨ε, β, hε, hε1, hβ, hβd, hεβ, hlevel⟩ := exists_transfer_sieve_accuracy
    (by norm_num : (0 : ℝ) < 1 / 1000) (by positivity : 0 < σ / 504)
  obtain ⟨Lr, hLr, hrough⟩ := logarithmicRoughWindow_transferred_l1 hβ
    (by norm_num : (79 / 400 : ℝ) < 1 / 5) he he' hε hε1 (by positivity : 0 < σ / 8)
  obtain ⟨Lc, hLc, hcofactor⟩ := logarithmicPrimeCofactorWindow_transferred_l1
    (by decide : 0 < (6 : ℕ)) hβ (by norm_num : (79 / 400 : ℝ) < 1 / 5)
    he he' hε hε1 (by positivity : 0 < σ / 8)
  refine ⟨max Lr Lc, hLr.trans (le_max_left _ _), ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 1 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hrough, hcofactor, eventually_small_cutoff_order hβ (by linarith),
    eventually_intermediate_cutoff_bound, eventually_outer_cutoff_bound,
    eventually_convolved_sieve_support hβ hβd, eventually_intermediate_power_dominates,
    eventually_rounded_sieve_log_level hβ (by norm_num : (0 : ℝ) < 1 / 1000),
    eventually_outer_prime_reciprocal_bound, hloglarge, eventually_ge_atTop 2]
    with X hrX hcX hWZ hZbound hQbound hsupport hpower hloglevel hrecip hlog1 hX
  have hXone : (1 : ℝ) < X := by exact_mod_cast (show 1 < X by omega)
  have hXp : (0 : ℝ) < X := by linarith
  have hlogp := Real.log_pos hXone
  have hshort : 16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤
      (Real.log X) ^ (-max Lr Lc) := by
    rcases le_total Lr Lc with h | h
    · simpa only [max_eq_right h] using hcX.1
    · simpa only [max_eq_left h] using hrX.1
  refine ⟨hshort, ?_⟩
  intro δ₁ δ₂ hδ₁lo hδ₁hi hδ₂lo hδ₂hi
  have hscaleR := Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (le_max_left Lr Lc))
  have hscaleC := Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg (le_max_right Lr Lc))
  let W := smallPrimeCutoff X β
  let D := roundedPowerCutoff X (1 / 1000)
  let Z := intermediatePrimeCutoff X
  let Q := outerPrimeCutoff X
  let P := sievePrimes Z Q
  change 3 * X < Z ^ 6 at hpower
  have hD : 0 < D := roundedPowerCutoff_pos hXp
  have hQ : 0 < Q := (outerPrimeCutoff_bounds hXone.le).1
  have hZ : 0 < Z := roundedPowerCutoff_pos hXp
  have hWpow : (X : ℝ) ^ β ≤ (W - 1 : ℕ) := (smallPrimeCutoff_bounds hXone.le hβ.le).1
  have hQB : Q ≤ 3 * X := by
    have hb : (Q : ℝ) ≤ X := hQbound.trans
      (Real.rpow_le_self_of_one_le hXone.le (by norm_num))
    have hn : Q ≤ X := by exact_mod_cast hb
    omega
  have hsX : Q * (W * D ^ 2) ≤ X := by
    exact_mod_cast hsupport.trans
      (Real.rpow_le_self_of_one_le hXone.le (by norm_num : (21 / 40 : ℝ) ≤ 1))
  have hsZ : Q * (W * D ^ 2) < Z ^ 6 := by omega
  have hsW : ((W * D ^ 2 : ℕ) : ℝ) ≤ (X : ℝ) ^ (21 / 40 : ℝ) := by
    apply le_trans _ hsupport
    exact_mod_cast (Nat.le_mul_of_pos_left (W * D ^ 2) hQ)
  have hlevelW : 16 * Real.exp 1 + 33 + Real.log (32 / ε) ≤ Real.log D / Real.log W :=
    hlevel.trans hloglevel
  have hP : ∀ p ∈ P, p.Prime ∧ Z ≤ p ∧ p ≤ Q := by
    intro p hp
    obtain ⟨hpI, hpp⟩ := Finset.mem_filter.mp hp
    obtain ⟨hpZ, hpQ⟩ := Finset.mem_Ico.mp hpI
    exact ⟨hpp, hpZ, hpQ.le⟩
  have hr := hrX.2 D W Z (3 * X) hD hWZ le_rfl (by omega) hWpow hZbound hsW hlevelW
    δ₁ δ₂ hδ₁lo (hδ₁hi.trans hscaleR) hδ₂lo (hδ₂hi.trans hscaleR)
  have hc := hcX.2 Q D W Z (3 * X) Z hQ hD hWZ le_rfl (by omega) hQB hZ hpower hsZ
    hWpow hZbound hsupport hlevelW P hP
    δ₁ δ₂ hδ₁lo (hδ₁hi.trans hscaleC) hδ₂lo (hδ₂hi.trans hscaleC)
  have hmain : ε * roughEulerProduct W ≤ (σ / 504) / Real.log X :=
    (smallPrimeCutoff_euler_error hXone hβ hε.le).trans
      (div_le_div_of_nonneg_right hεβ hlogp.le)
  have hmainC : ε * (∑ p ∈ P, (p : ℝ)⁻¹) * roughEulerProduct W ≤
      42 * ((σ / 504) / Real.log X) := by
    calc
      _ = (∑ p ∈ P, (p : ℝ)⁻¹) * (ε * roughEulerProduct W) := by ring
      _ ≤ _ := mul_le_mul hrecip hmain (mul_nonneg hε.le (roughEulerProduct_pos W).le)
        (by norm_num : (0 : ℝ) ≤ 42)
  constructor
  · apply hr.trans
    calc
      _ ≤ 6 * ((σ / 504) / Real.log X) + 4 * (σ / 8) / Real.log X :=
        add_le_add (mul_le_mul_of_nonneg_left hmain (by norm_num)) le_rfl
      _ ≤ _ := by field_simp; nlinarith
  · apply hc.trans
    calc
      _ ≤ 6 * (42 * ((σ / 504) / Real.log X)) + 4 * (σ / 8) / Real.log X :=
        add_le_add (mul_le_mul_of_nonneg_left hmainC (by norm_num)) le_rfl
      _ = _ := by ring

end Erdos421
