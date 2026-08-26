import ErdosProblems.Erdos421.ComparableProductVariance
import ErdosProblems.Erdos421.ActiveProductEnergy

/-! # Arbitrary finite cofactor supports in the prime-block window comparison -/

namespace Erdos421

open MeasureTheory Filter Topology

theorem inverse_log_window_le_support_width {x L : ℝ} (hx : 2 ≤ x) (hL : 2 ≤ L) :
    x ^ (-L) ≤ Real.log (3 / 2) := by
  have hxp : 0 < x := by linarith
  have hp : x ^ (-L) ≤ x ^ (-2 : ℝ) :=
    Real.rpow_le_rpow_of_exponent_le (by linarith) (by linarith)
  have hquarter : x ^ (-2 : ℝ) ≤ 1 / 4 := by
    rw [Real.rpow_neg hxp.le, Real.rpow_two]
    exact (inv_le_comm₀ (by positivity) (by norm_num : (0 : ℝ) < 1 / 4)).mpr
      (by norm_num; nlinarith)
  have hlog := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 3 / 2)
  norm_num at hlog
  exact hp.trans (hquarter.trans (by linarith))

theorem prime_cofactor_full_window_variance {β θ e A ε C : ℝ}
    (hβ : 0 < β) (hθ : θ < 1 / 5) (he : 0 < e) (he' : e < 9 / 10)
    (hA : 0 ≤ A) (hε : 0 < ε) (hC : 0 < C) :
    ∃ L : ℝ, 2 ≤ L ∧ ∀ᶠ X : ℕ in atTop,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ (Real.log X) ^ (-L) ∧
      ∀ H J B : ℕ, 0 < H → J ≤ H →
      (X : ℝ) ^ β ≤ H → (H : ℝ) ≤ (X : ℝ) ^ θ →
      ∀ a : ℕ → ℂ, (∀ n ∈ Finset.Icc 1 B, ‖a n‖ ≤ C) →
      ∀ ρ₁ ρ₂ : ℝ,
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₁ → ρ₁ ≤ (Real.log X) ^ (-L) →
      16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) ≤ ρ₂ → ρ₂ ≤ (Real.log X) ^ (-L) →
      (∫ y in Real.log (X : ℝ)..Real.log (2 * X : ℝ),
        ‖scaledProductWindow (Finset.Icc 1 B) (primeBlockSupport H J) a (fun _ ↦ 1)
            1 oneSidedSchwartzWindow ρ₁ y -
          scaledProductWindow (Finset.Icc 1 B) (primeBlockSupport H J) a (fun _ ↦ 1)
            1 oneSidedSchwartzWindow ρ₂ y‖ ^ 2) ≤ ε / (Real.log X) ^ A := by
  obtain ⟨L, hL, hmean⟩ := prime_cofactor_comparable_variance oneSidedSchwartzWindow
    hβ hθ he he' hA (by positivity : 0 < ε / 16) hC
  refine ⟨L, hL, ?_⟩
  have hloglarge : ∀ᶠ X : ℕ in atTop, 2 ≤ Real.log X :=
    (Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop _
  filter_upwards [hmean, hloglarge, eventually_ge_atTop 1] with X hmeanX hlog hX
  refine ⟨hmeanX.1, ?_⟩
  intro H J B hH hJ hHlo hHhi a ha ρ₁ ρ₂ hρ₁lo hρ₁hi hρ₂lo hρ₂hi
  have hXp : (0 : ℝ) < X := by exact_mod_cast hX
  have hLX : 0 < Real.log X := by linarith
  have hshort : 0 < 16 * Real.pi / (X : ℝ) ^ (9 / 10 - e) := by positivity
  have hρ₁ : 0 < ρ₁ := hshort.trans_le hρ₁lo
  have hρ₂ : 0 < ρ₂ := hshort.trans_le hρ₂lo
  have hwidth := inverse_log_window_le_support_width hlog hL
  have htiles : ∀ j ∈ activeProductScales B H (X : ℝ), (∫ y : ℝ,
      ‖scaledProductWindow (dyadicCofactorSupport B j) (primeBlockSupport H J) a (fun _ ↦ 1)
          1 oneSidedSchwartzWindow ρ₁ y -
        scaledProductWindow (dyadicCofactorSupport B j) (primeBlockSupport H J) a (fun _ ↦ 1)
          1 oneSidedSchwartzWindow ρ₂ y‖ ^ 2) ≤ ε / 16 / (Real.log X) ^ A := by
    intro j hj
    have hjscale := activeProductScales_bounds hj
    apply hmeanX.2 (2 ^ j) H J (pow_pos (by decide : 0 < (2 : ℕ)) j) hH hJ
      hjscale.2.1.le hjscale.2.2.le hHlo hHhi (dyadicCofactorSupport B j) a
    · intro n hn
      exact ⟨(dyadicCofactorSupport_bounds B j hn).1, (dyadicCofactorSupport_bounds B j hn).2.1⟩
    · intro n hn
      exact ha n (Finset.mem_Icc.mpr ⟨dyadicCofactorSupport_pos B j hn,
        (dyadicCofactorSupport_bounds B j hn).2.2⟩)
    · exact dyadicCofactorSupport_card_le B j
    · norm_num
    · exact hρ₁lo
    · exact hρ₁hi
    · exact hρ₂lo
    · exact hρ₂hi
  have hb := scaledProductWindow_active_energy_le (primeBlockSupport H J) a (fun _ ↦ 1)
    B.lt_two_pow_self hH (primeBlockSupport_bounds hJ) hXp hρ₁ hρ₂
    (hρ₁hi.trans hwidth) (hρ₂hi.trans hwidth) (by positivity) htiles
  apply hb.trans_eq
  ring

end Erdos421
