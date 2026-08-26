import ErdosProblems.Erdos421.ComparableFactorBands
import ErdosProblems.Erdos421.BoundedPrimeCofactorVariance

/-! # A single pair of window lengths for all nearby product scales -/

namespace Erdos421

open MeasureTheory Filter Topology
open scoped SchwartzMap

theorem prime_cofactor_comparable_variance (ψ : 𝓢(ℝ, ℂ)) {β θ e A ε C : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) (hC : 0 < C) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ M H J : ℕ, 0 < M → 0 < H → J ≤ H →
      (X : ℝ) / 4 ≤ (M * H : ℕ) → (M * H : ℕ) ≤ 3 * (X : ℝ) →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ θ →
      ∀ (S : Finset ℕ) (a : ℕ → ℂ), (∀ n ∈ S, M ≤ n ∧ n ≤ 2 * M) →
      (∀ n ∈ S, ‖a n‖ ≤ C) → S.card ≤ M →
      ∀ σ ρ₁ ρ₂ : ℝ, 1 ≤ σ →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y : ℝ, ‖scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ ψ ρ₁ y -
        scaledProductWindow S (primeBlockSupport H J) a (fun _ ↦ 1) σ ψ ρ₂ y‖ ^ 2) ≤
          ε / (Real.log X) ^ A := by
  obtain ⟨B, hB, hmean⟩ := prime_cofactor_bounded_variance ψ
    (by positivity : 0 < β / 2) he he' (by linarith : 0 ≤ A + 1) (by norm_num : (0 : ℝ) < 1) hC
  obtain ⟨T₀, hT₀⟩ := eventually_atTop.mp hmean
  let L := max (B + 1) 2
  have hL : 2 ≤ L := le_max_right _ _
  have hBL : B + 1 ≤ L := le_max_left _ _
  have hloglarge : ∀ᶠ X : ℕ in atTop,
      max (max (2 * Real.log 4) (Real.log 3)) (max 1 ((2 : ℝ) ^ B)) ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  refine ⟨L, hL, ?_⟩
  filter_upwards [eventually_ge_atTop (4 * T₀ + 4), hloglarge,
    eventually_comparable_factor_band hβ hθ,
    constant_short_window_below_log_scale (by positivity : 0 < 16 * Real.pi)
      (by linarith : 0 < 9 / 10 - e) L,
    constant_inverse_log_saving ((2 : ℝ) ^ (A + 1)) A hε] with X hX hlog hband hshort hsave
  refine ⟨hshort, ?_⟩
  intro M H J hM hH hJ hXT hTX hHlo hHhi S a hS ha hcard σ ρ₁ ρ₂ hσ
    hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast (by omega : 0 < X)
  have hTp : (0 : ℝ) < (M * H : ℕ) := by exact_mod_cast Nat.mul_pos hM hH
  have hTlarge : T₀ ≤ M * H := by
    have hXreal : 4 * (T₀ : ℝ) + 4 ≤ X := by exact_mod_cast hX
    have hTreal : (T₀ : ℝ) ≤ (M * H : ℕ) := by linarith
    exact_mod_cast hTreal
  have hlog1 : 1 ≤ Real.log X := (le_max_left _ _).trans ((le_max_right _ _).trans hlog)
  have hlog2 : (2 : ℝ) ^ B ≤ Real.log X :=
    (le_max_right _ _).trans ((le_max_right _ _).trans hlog)
  have hlog4 : 2 * Real.log 4 ≤ Real.log X :=
    (le_max_left _ _).trans ((le_max_left _ _).trans hlog)
  have hlog3 : Real.log 3 ≤ Real.log X :=
    (le_max_right _ _).trans ((le_max_left _ _).trans hlog)
  have hlogs := comparable_log_bounds hXp hXT hTX hlog4 hlog3
  have hLX : 0 < Real.log X := by linarith
  have hLT : 0 < Real.log (M * H : ℕ) := by linarith [hlogs.1]
  obtain ⟨hHlo', hHhi'⟩ := hband (M * H : ℕ) H hXT hTX hHlo hHhi
  have hmin : 4 * Real.pi / ((M * H : ℕ) : ℝ) ^ (9 / 10 - e) ≤
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) :=
    comparable_short_window_lower hXp hTp (by linarith) (by linarith) (by linarith)
  have hmax : (Real.log X) ^ (-L) ≤ (Real.log (M * H : ℕ)) ^ (-B) := by
    apply (Real.rpow_le_rpow_of_exponent_le hlog1 (neg_le_neg hBL)).trans
    exact comparable_inverse_log_window hLX hLT hB.le hlogs.2 hlog2
  have hb := (hT₀ (M * H) hTlarge).2 M H J hM hH
    (Nat.le_mul_of_pos_right M hH) (Nat.le_mul_of_pos_left H hM) hJ rfl
    hHlo' hHhi' S a hS ha hcard σ ρ₁ ρ₂ hσ
    (hmin.trans hρ₁lo) (hρ₁hi.trans hmax) (hmin.trans hρ₂lo) (hρ₂hi.trans hmax)
  apply hb.trans
  calc
    _ ≤ (2 : ℝ) ^ (A + 1) / (Real.log X) ^ (A + 1) :=
      comparable_inverse_log_power hLX hLT (by linarith) hlogs.1
    _ = (2 : ℝ) ^ (A + 1) * (Real.log X) ^ (-A - 1) := by
      rw [show -A - 1 = -(A + 1) by ring, Real.rpow_neg hLX.le, div_eq_mul_inv]
    _ ≤ _ := hsave

end Erdos421
