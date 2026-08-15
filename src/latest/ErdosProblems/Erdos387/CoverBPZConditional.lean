/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/

import ErdosProblems.Erdos387.CoverBPZPrelude

/-!
# Conditional completion of the public BNPZ cover

Every theorem here is proved.  The sole unsolved analytic dependency is an
explicit argument `hSW : ShiftedSiegelWalfiszLower`; no declaration in this
module postulates that proposition.
-/

open scoped BigOperators
open Real Classical
open Erdos387.ANT Erdos387

namespace Erdos387.CoverBPZ

open Finset

theorem wideCoverBuildData_exists
    (hSW : ShiftedSiegelWalfiszLower) (B : ℕ) (hB : 3 ≤ B) :
    ∀ K : ℕ, ∃ k : ℕ, K ≤ k ∧ 3 ≤ k ∧ Nonempty (WideCoverBuildData B k) := by
  intro K
  classical
  obtain ⟨Y₀, h_buffer_supply⟩ := buffer_prime_supply B
  obtain ⟨k₀, h_dom_all⟩ := third_half_square_product_dominates_HX B
  set Aq : ℕ := M_B B + 15 with hAq_set_def
  set Csw : ℕ := 2000 * (B + 1) * (Aq + 1) + 2000 with hCsw_set_def
  obtain ⟨Xsw, hSW_axiom⟩ := hSW Csw
  obtain ⟨Scale⟩ := exists_scaffold_scale_bounds B K Y₀ k₀ Xsw
  let X : ℕ := Scale.X
  have hX_def : X = Scale.X := rfl
  have hX_ge_K : K ≤ X := Scale.X_ge_K
  have hX_ge_SW : Xsw ≤ X := Scale.X_ge_SW
  have hX_ge_100 : 100 ≤ X := Scale.X_ge_100
  have h_consts_le_log4 :
      max B (max Y₀ (max k₀ (max K (B * 2 ^ (21 * B + 1))))) ≤
        (Nat.log 2 X + 1) ^ 4 := Scale.consts_le_log4
  have h_polylog_dom :
      1000000 * (B + 1) *
        (Nat.log 2 X + 1) ^
          (3000 * (B + 1) * (M_B B + 20) + 3000) ≤ X :=
    Scale.polylog_dominates_bad
  let L : ℕ := Nat.log 2 X + 1
  have hL_def : L = Nat.log 2 X + 1 := rfl
  have hX_pos : 0 < X := by omega
  have hL_ge_7 : 7 ≤ L := by
    have h_log_ge : 6 ≤ Nat.log 2 X := by
      have h64_le : 2 ^ 6 ≤ X := by
        have h_calc : 2 ^ 6 = 64 := by norm_num
        omega
      exact Nat.le_log_of_pow_le (by norm_num : 1 < 2) h64_le
    simp [hL_def]; omega
  have hL_ge_2 : 2 ≤ L := by omega
  have hL_pos : 0 < L := by omega
  have hB_le_L4 : B ≤ L ^ 4 :=
    (le_max_left _ _).trans h_consts_le_log4
  have hY₀_le_L4 : Y₀ ≤ L ^ 4 :=
    ((le_max_left _ _).trans (le_max_right _ _)).trans h_consts_le_log4
  have hk₀_le_L4 : k₀ ≤ L ^ 4 :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      (le_max_right _ _))).trans h_consts_le_log4
  have hK_le_L4 : K ≤ L ^ 4 :=
    ((le_max_left _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans h_consts_le_log4
  have hHXconst_le_L4 : B * 2 ^ (21 * B + 1) ≤ L ^ 4 :=
    ((le_max_right _ _).trans ((le_max_right _ _).trans
      ((le_max_right _ _).trans (le_max_right _ _)))).trans h_consts_le_log4
  have hAq_ge_5 : 5 ≤ Aq := by
    show 5 ≤ M_B B + 15
    omega
  let Qscale : ℕ := L ^ Aq
  have hQscale_pos : 0 < Qscale := Nat.pow_pos hL_pos
  have hQscale_ne_zero : Qscale ≠ 0 := Nat.pos_iff_ne_zero.mp hQscale_pos
  obtain ⟨q, hq_prime, hq_gt, hq_le_2Q⟩ :=
    Nat.bertrand Qscale hQscale_ne_zero
  have hq_ge_Qscale : Qscale ≤ q := le_of_lt hq_gt
  have hq_le_2Lpow : q ≤ 2 * L ^ Aq := hq_le_2Q
  have hq_pos : 0 < q := hq_prime.pos
  have hq_ge_2 : 2 ≤ q := hq_prime.two_le
  have hL_le_Qscale : L ≤ Qscale := by
    show L ≤ L ^ Aq
    calc L = L ^ 1 := (pow_one _).symm
      _ ≤ L ^ Aq := Nat.pow_le_pow_right hL_pos (by omega)
  have hL_le_q : L ≤ q := hL_le_Qscale.trans hq_ge_Qscale
  have hL4_le_Qscale : L ^ 4 ≤ Qscale :=
    Nat.pow_le_pow_right hL_pos (by omega)
  have hL4_le_q : L ^ 4 ≤ q := hL4_le_Qscale.trans hq_ge_Qscale
  have hq_ge_B : B ≤ q := hB_le_L4.trans hL4_le_q
  have hq_ge_Y₀ : Y₀ ≤ q := hY₀_le_L4.trans hL4_le_q
  have hq_ge_k0 : k₀ ≤ q := hk₀_le_L4.trans hL4_le_q
  let Y : ℕ := q ^ 20
  have hY_eq : Y = q ^ 20 := rfl
  have hY_ge_Y₀ : Y₀ ≤ Y := by
    show Y₀ ≤ q ^ 20
    calc Y₀ ≤ q := hq_ge_Y₀
      _ = q ^ 1 := (pow_one _).symm
      _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_pos (by omega)
  have hY_pos : 2 ≤ Y := by
    show 2 ≤ q ^ 20
    calc 2 ≤ q := hq_ge_2
      _ = q ^ 1 := (pow_one _).symm
      _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_pos (by omega)
  have hq_pow20_le_Y : q ^ 20 ≤ Y := le_refl _
  have hY_lt_q_pow21 : Y < q ^ 21 := by
    show q ^ 20 < q ^ 21
    rw [pow_succ]
    nlinarith [Nat.pow_pos hq_pos (n := 20), hq_prime.one_lt]
  have hM_B : M_B B = B * (20 + 1) := by unfold M_B; ring
  have hD_card_le_MB : (smallDeficientSet B Y q).card ≤ M_B B :=
    D_Y_card_le_via_M_B hq_prime.one_lt hY_lt_q_pow21 hM_B
  have h_many : (smallDeficientSet B Y q).card ≤
      ((Finset.Ioc (Y * Y) (2 * Y * Y)).filter Nat.Prime).card :=
    hD_card_le_MB.trans (h_buffer_supply Y hY_ge_Y₀)
  obtain ⟨bSub, hbSub_inj, hbSub_prime, hbSub_range⟩ := exists_buffer_primes h_many
  let bTotal : ℕ → ℕ := fun d =>
    if hd : d ∈ smallDeficientSet B Y q then bSub ⟨d, hd⟩ else 1
  have hbTotal_eq : ∀ d (hd : d ∈ smallDeficientSet B Y q),
      bTotal d = bSub ⟨d, hd⟩ := by
    intro d hd; dsimp [bTotal]; rw [dif_pos hd]
  have hbTotal_prime : ∀ d ∈ smallDeficientSet B Y q, (bTotal d).Prime := by
    intro d hd; rw [hbTotal_eq d hd]; exact hbSub_prime _
  have hbTotal_range :
      ∀ d ∈ smallDeficientSet B Y q, Y * Y < bTotal d ∧ bTotal d ≤ 2 * Y * Y := by
    intro d hd
    rw [hbTotal_eq d hd]
    exact hbSub_range _
  let W : ℕ := W_product q B Y bTotal
  have hW_pos : 0 < W :=
    W_product_pos hq_pos (fun d hd => (hbTotal_prime d hd).pos)
  have hq_dvd_W : q ∣ W := Q_dvd_W q B Y bTotal
  have hW_ge_q : q ≤ W := Nat.le_of_dvd hW_pos hq_dvd_W
  have hW_ge_2 : 2 ≤ W := hq_ge_2.trans hW_ge_q
  have hD_card_le_21B : (smallDeficientSet B Y q).card ≤ 21 * B := by
    have h1 := hD_card_le_MB; rw [hM_B] at h1; omega
  have hW_poly : W ≤ L ^ Csw :=
    wcbd_W_poly_bound bTotal hAq_ge_5 hCsw_set_def hD_card_le_21B hq_le_2Lpow hL_ge_2
      (fun d hd => (hbTotal_range d hd).2)
  have hY_poly : Y ≤ L ^ Csw :=
    wcbd_Y_poly_bound hAq_ge_5 hCsw_set_def hq_le_2Lpow hL_ge_2
  have hbTotal_in_range_data :
      ∀ d ∈ smallDeficientSet B Y q,
        ∃ bd_val : ℕ, bTotal d = bd_val ∧ Y * Y < bd_val ∧ bd_val ≤ 2 * Y * Y := by
    intro d hd
    refine ⟨bSub ⟨d, hd⟩, ?_, ?_, ?_⟩
    · exact hbTotal_eq d hd
    · exact (hbSub_range ⟨d, hd⟩).1
    · exact (hbSub_range ⟨d, hd⟩).2
  have h_bTotal_le_q41 : ∀ d ∈ smallDeficientSet B Y q, bTotal d ≤ q ^ 41 :=
    bTotal_d_le_q41 hq_prime hY_eq bTotal hbTotal_in_range_data
  have hW_le_qpow : W ≤ q ^ (861 * B + 1) :=
    W_product_le_q_pow hq_prime hq_prime.two_le bTotal h_bTotal_le_q41 hM_B hD_card_le_MB
  have hbTotal_inj_smallDef :
      Set.InjOn bTotal (smallDeficientSet B Y q) := by
    intro x hx y hy hxy
    rw [hbTotal_eq x hx, hbTotal_eq y hy] at hxy
    exact Subtype.mk_eq_mk.mp (hbSub_inj hxy)
  have hbTotal_ne_q : ∀ d ∈ smallDeficientSet B Y q, bTotal d ≠ q := by
    intro d hd h_eq
    have hbt_eq := hbTotal_eq d hd
    rw [h_eq] at hbt_eq
    have hbgt : Y * Y < bSub ⟨d, hd⟩ := (hbSub_range ⟨d, hd⟩).1
    have hq_le_Y : q ≤ Y := by
      calc q = q ^ 1 := (pow_one _).symm
        _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_prime.pos (by omega)
        _ ≤ Y := hq_pow20_le_Y
    have hY_le_YY : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by have := hY_pos; omega)
    omega
  have hq_ge_3 : 3 ≤ q := by omega
  have hY_lt_W : Y < W :=
    wcbd_Y_lt_W bTotal hB hq_prime hq_ge_B hq_ge_3 hY_pos hq_pow20_le_Y hW_pos
      (fun d hd => buffer_dvd_W q B Y bTotal d hd) hbTotal_range
  have hY_div_W : Y / W = 0 := Nat.div_eq_of_lt hY_lt_W
  have hU_card_at : ∀ Z : ℕ, B * 2 ^ (21 * B + 1) ≤ (Nat.log 2 Z + 1) ^ 4 →
      2 ≤ Z → (residualSet B Z Y q bTotal).card ≤ H_X (M_B B) Z :=
    fun Z h_const_le_log_pow hZ_ge_2 =>
      wcbd_residual_card_bound hq_prime hbTotal_prime
        hbTotal_inj_smallDef hbTotal_ne_q hD_card_le_21B
        h_const_le_log_pow hZ_ge_2
  set Ω : Finset ℕ := (Finset.Icc X (2 * X)).filter (W ∣ ·) with hΩ_def
  set Ubig := residualSet B (2 * X) Y q bTotal with hUbig_def
  have hHX_const_le_log4_2X :
      B * 2 ^ (21 * B + 1) ≤ (Nat.log 2 (2 * X) + 1) ^ 4 := by
    have h_log_2X : Nat.log 2 (2 * X) = Nat.log 2 X + 1 := by
      rw [show 2 * X = X * 2 from by ring]
      exact Nat.log_mul_base (by norm_num) (by omega)
    have h_eq : Nat.log 2 (2 * X) + 1 = L + 1 := by simp [hL_def, h_log_2X]
    rw [h_eq]
    calc B * 2 ^ (21 * B + 1)
        ≤ L ^ 4 := hHXconst_le_L4
      _ ≤ (L + 1) ^ 4 := Nat.pow_le_pow_left (by omega) _
  have hUbig_card : Ubig.card ≤ H_X (M_B B) (2 * X) := by
    rw [hUbig_def]
    exact hU_card_at (2 * X) hHX_const_le_log4_2X (by omega)
  have hcop : ∀ h ∈ ShiftSet Y q, Nat.Coprime h W := by
    intro h hh
    have hY_pos1 : 1 ≤ Y := by omega
    have hh_filter := Finset.mem_filter.mp hh
    obtain ⟨hh_ico, hh_mod_q⟩ := hh_filter
    rw [Finset.mem_Ico] at hh_ico
    exact coprime_h_W_product hq_prime hbTotal_prime hbTotal_range hY_pos1
      hh_ico.2 hh_mod_q
  have hY_big : 8 * q ≤ Y := by
    show 8 * q ≤ q ^ 20
    have h8 : (8 : ℕ) ≤ q ^ 3 := by
      calc (8 : ℕ) = 2 ^ 3 := by norm_num
        _ ≤ q ^ 3 := Nat.pow_le_pow_left hq_ge_2 _
    have h_step : 8 * q ≤ q ^ 3 * q := Nat.mul_le_mul_right q h8
    have h_eq : q ^ 3 * q = q ^ 4 := by rw [← pow_succ]
    have h_4_le_20 : q ^ 4 ≤ q ^ 20 :=
      Nat.pow_le_pow_right hq_pos (by omega)
    omega
  have hShiftSet_lower : Y / (4 * q) ≤ (ShiftSet Y q).card :=
    ShiftSet_card_lower hq_ge_2 hY_big
  have hq_le_L_pow_Aq1 : q ≤ L ^ (Aq + 1) := by
    have hstep : L * L ^ Aq = L ^ (Aq + 1) := by
      rw [pow_succ]; ring
    calc q ≤ 2 * L ^ Aq := hq_le_2Lpow
      _ ≤ L * L ^ Aq := Nat.mul_le_mul_right _ hL_ge_2
      _ = L ^ (Aq + 1) := hstep
  set E_big : ℕ := 3000 * (B + 1) * (M_B B + 20) + 3000 with hE_big_def
  have hX_ge_LE : 1000000 * (B + 1) * L ^ E_big ≤ X := h_polylog_dom
  have hX_ge_LE_loose : L ^ E_big ≤ X := by
    have h1 : L ^ E_big ≤ 1000000 * (B + 1) * L ^ E_big := by
      have : 1 ≤ 1000000 * (B + 1) := by omega
      calc L ^ E_big = 1 * L ^ E_big := (one_mul _).symm
        _ ≤ 1000000 * (B + 1) * L ^ E_big :=
          Nat.mul_le_mul_right _ this
    exact h1.trans hX_ge_LE
  have hCsw_le_E_big : Csw ≤ E_big := by
    show 2000 * (B + 1) * (Aq + 1) + 2000 ≤ 3000 * (B + 1) * (M_B B + 20) + 3000
    have hAq1 : Aq + 1 = 21 * B + 16 := by
      show M_B B + 15 + 1 = 21 * B + 16
      have hM : M_B B = 21 * B := by unfold M_B; ring
      omega
    have hM : M_B B + 20 = 21 * B + 20 := by unfold M_B; ring
    rw [hM]
    exact wcbd_Csw_le_E_big B Aq hAq1
  have hLCsw_le_X : L ^ Csw ≤ X :=
    (Nat.pow_le_pow_right hL_pos hCsw_le_E_big).trans hX_ge_LE_loose
  have hY_le_X : Y ≤ X := hY_poly.trans hLCsw_le_X
  have hW_le_X : W ≤ X := hW_poly.trans hLCsw_le_X
  have hHX_bound : H_X (M_B B) (2 * X) ≤ 16 * L ^ (21 * B + 9) :=
    wcbd_HX_2X_bound hL_def hX_ge_100 hHXconst_le_L4 (by omega)
  have hCsw1_le_E_big : Csw + 1 ≤ E_big := by
    show 2000 * (B + 1) * (Aq + 1) + 2000 + 1 ≤ 3000 * (B + 1) * (M_B B + 20) + 3000
    have hAq1 : Aq + 1 = 21 * B + 16 := by
      show M_B B + 15 + 1 = 21 * B + 16
      have hM : M_B B = 21 * B := by unfold M_B; ring
      omega
    have hM : M_B B + 20 = 21 * B + 20 := by unfold M_B; ring
    rw [hM]
    exact wcbd_Csw_succ_le_E_big B Aq hAq1
  have hAq_eq_main : Aq = 21 * B + 15 := by
    show M_B B + 15 = 21 * B + 15
    have hM : M_B B = 21 * B := by unfold M_B; ring
    omega
  have h_HX_bound :
      4 * H_X (M_B B) (2 * X) *
          (((Finset.Icc X (2 * X)).filter (W ∣ ·)).card) ≤
        (ShiftSet Y q).card * (X / (8 * W * L)) :=
    wcbd_supply_HX_bound hL_pos hL_ge_2 hL_ge_7 hW_pos hW_le_X hW_poly
      hHX_bound hX_ge_LE hCsw1_le_E_big hAq_eq_main hq_ge_Qscale
      hq_le_L_pow_Aq1 hq_pow20_le_Y hShiftSet_lower
  have hSupply :
      4 * H_X (M_B B) (2 * X) * Ω.card ≤
        ∑ k ∈ Ω, (CandidatePrimes k Y q).card := by
    have hSW :
        ∀ Q a h : ℕ, 2 ≤ Q → Q ≤ (Nat.log 2 X + 1) ^ Csw →
            h ≤ (Nat.log 2 X + 1) ^ Csw → Nat.Coprime a Q →
            ((Finset.Ioc (X - h) (2 * X - h)).filter
              (fun p => p.Prime ∧ p % Q = a % Q)).card
              ≥ X / (8 * Q * (Nat.log 2 X + 1)) := by
      intro Q a h hQ_ge_2 hQ_le hh_le hcop_aQ
      exact hSW_axiom X Q a h hX_ge_SW hQ_ge_2 hQ_le hh_le hcop_aQ
    exact prime_supply_sum_lower_from_SW (B := B) (X := X) (Y := Y)
      (q := q) (W := W) (Csw := Csw) (b := bTotal)
      hq_prime hq_ge_2 hY_eq hW_pos hW_le_X hY_le_X
      hW_poly hY_poly hY_big hq_dvd_W hbTotal_prime hbTotal_range
      hcop hSW h_HX_bound
  have hBadSmall :
      Ubig.card * (Y / W + 2) * Y +
        H_X (M_B B) (2 * X) * Ω.card <
      4 * H_X (M_B B) (2 * X) * Ω.card := by
    have hAq_def : Aq = 21 * B + 15 := by
      show M_B B + 15 = 21 * B + 15
      have hMB : M_B B = 21 * B := by unfold M_B; ring
      omega
    have hB_ge_1 : 1 ≤ B := by omega
    have hX_step :
        (2 * q ^ 20 + 1) * W ≤
          1000000 * (B + 1) *
            L ^ (3000 * (B + 1) * (M_B B + 20) + 3000) :=
      wcbd_X_ge_step_direct hB_ge_1 hAq_def hL_ge_2 hq_le_2Lpow hW_le_qpow
    have hX_step' : (2 * q ^ 20 + 1) * W ≤ X := hX_step.trans h_polylog_dom
    have hX_step_Y : (2 * Y + 1) * W ≤ X := by
      rw [hY_eq]; exact hX_step'
    have hHX_pos : 0 < H_X (M_B B) (2 * X) :=
      H_X_pos _ _ (by omega)
    rw [hUbig_def]
    exact wcbd_bad_mass_strict_lt (B := B) (X := X) (Y := Y) (q := q) (W := W)
      bTotal hW_pos hY_lt_W hX_step_Y
      (by rw [← hUbig_def]; exact hUbig_card) hHX_pos
  obtain ⟨k, hkX, hk2X, hW_dvd_k, hCand_big, hnotBad⟩ :=
    exists_good_k_for_scaffold_final
      (B := B) (X := X) (Y := Y) (q := q) (W := W) (b := bTotal)
      hW_pos hUbig_card hSupply hBadSmall
  have hkK : K ≤ k := hX_ge_K.trans hkX
  have hk10 : 10 ≤ k := by
    have : 10 ≤ X := by omega
    exact this.trans hkX
  have hMB_eq : M_B B = 21 * B := by unfold M_B; ring
  have hE_big_eq_main : E_big = 3000 * (B + 1) * (21 * B + 20) + 3000 := by
    show 3000 * (B + 1) * (M_B B + 20) + 3000 = _
    rw [hMB_eq]
  have hY_sq_small_X : 6 * Y * Y ≤ X := by
    show 6 * q ^ 20 * q ^ 20 ≤ X
    exact wcbd_6YY_le_X hL_pos hL_ge_2 hX_ge_LE_loose hAq_eq_main
      hE_big_eq_main hq_le_L_pow_Aq1
  have hY_sq_small_k : 6 * Y * Y ≤ k := hY_sq_small_X.trans hkX
  have hY_le_half : 2 * Y ≤ k := by
    have h_2Y_le_2YY : 2 * Y ≤ 2 * Y * Y := by
      calc 2 * Y = 2 * Y * 1 := by ring
        _ ≤ 2 * Y * Y := Nat.mul_le_mul_left _ (by omega)
    have h_2YY_le_6YY : 2 * Y * Y ≤ 6 * Y * Y := by
      apply Nat.mul_le_mul_right; omega
    omega
  have hE_big_ge_5 : 5 ≤ E_big := by
    show 5 ≤ 3000 * (B + 1) * (M_B B + 20) + 3000
    omega
  have hk_ge_4m : 4 * B + 4 ≤ k :=
    (wcbd_4Bp4_le_X hL_pos hL_ge_2 hL_ge_7 hB_le_L4 hX_ge_LE_loose
      hE_big_ge_5).trans hkX
  have h2q_le_X : 2 * q ≤ X :=
    wcbd_2q_le_X hL_pos hL_ge_2 hq_le_2Lpow hAq_eq_main hE_big_eq_main
      hX_ge_LE_loose
  have hq_le_k_half : q ≤ k / 2 := by
    have h2qk : 2 * q ≤ k := h2q_le_X.trans hkX
    rw [Nat.le_div_iff_mul_le (by norm_num)]; omega
  have h4_le_E_big : 4 ≤ E_big := by
    show 4 ≤ 3000 * (B + 1) * (M_B B + 20) + 3000
    omega
  have hk_ge_k₀ : k₀ ≤ k := by
    have h2 : L ^ 4 ≤ L ^ E_big := Nat.pow_le_pow_right hL_pos h4_le_E_big
    exact ((hk₀_le_L4.trans h2).trans hX_ge_LE_loose).trans hkX
  have hq_dvd_k : q ∣ k := hq_dvd_W.trans hW_dvd_k
  have hk3 : 3 ≤ k := by omega
  have hbSub_dvd_k : ∀ d, bSub d ∣ k := by
    intro d
    have hd : d.val ∈ smallDeficientSet B Y q := d.property
    have hbt_eq : bTotal d.val = bSub d := hbTotal_eq d.val hd
    have h_dvd_W : bTotal d.val ∣ W := buffer_dvd_W q B Y bTotal d.val hd
    rw [hbt_eq] at h_dvd_W
    exact h_dvd_W.trans hW_dvd_k
  let bd : BufferData k Y :=
    BufferData.ofSubtypeMap (smallDeficientSet_subset B Y q) bSub
      hbSub_prime hbSub_range hbSub_dvd_k hbSub_inj
  have hbd_D_eq : bd.D = smallDeficientSet B Y q := rfl
  have hbTotal_eq_bd_total :
      ∀ d ∈ smallDeficientSet B Y q, bd.total d = bTotal d := by
    intro d hd
    have hd' : d ∈ bd.D := by rwa [hbd_D_eq]
    show bd.total d = bTotal d
    rw [bd.total_of_mem hd', hbTotal_eq d hd]
    rfl
  have hbTotal_inj_on : Set.InjOn bd.total bd.D := by
    intro x hx y hy hxy
    rw [hbd_D_eq] at hx hy
    rw [hbTotal_eq_bd_total x hx, hbTotal_eq_bd_total y hy] at hxy
    rw [hbTotal_eq x hx, hbTotal_eq y hy] at hxy
    have : (⟨x, hx⟩ : {d // d ∈ smallDeficientSet B Y q}) = ⟨y, hy⟩ :=
      hbSub_inj hxy
    exact Subtype.mk_eq_mk.mp this
  have hU_no_small_bdTotal : ∀ t, t ∈ residualSet B k Y q bd.total → Y < t :=
    residualSet_no_small_total (B := B) (X := k) bd (by have := hY_pos; omega)
      hbd_D_eq hbTotal_inj_on
  have hHX_const_le_log4_k : B * 2 ^ (21 * B + 1) ≤ (Nat.log 2 k + 1) ^ 4 := by
    have hk_ge : X ≤ k := hkX
    have h1 : Nat.log 2 X ≤ Nat.log 2 k := Nat.log_mono_right hk_ge
    have h2 : L ^ 4 ≤ (Nat.log 2 k + 1) ^ 4 :=
      Nat.pow_le_pow_left (by simp [hL_def]; omega) _
    exact hHXconst_le_L4.trans h2
  have hU_card_bdTotal :
      (residualSet B k Y q bd.total).card ≤ H_X (M_B B) k := by
    have hres_eq :
        residualSet B k Y q bd.total = residualSet B k Y q bTotal :=
      residualSet_ext_of_agree_on_D
        (fun d hd => hbTotal_eq_bd_total d hd)
    rw [hres_eq]
    exact hU_card_at k hHX_const_le_log4_k (by omega)
  have hCand_PNT :
      H_X (M_B B) k ≤ (CandidatePrimes k Y q).card := by
    have hHX : H_X (M_B B) k ≤ H_X (M_B B) (2 * X) :=
      H_X_monotone_in_X (M_B := M_B B) hk2X
    exact hHX.trans hCand_big
  have hEndpoint : ∀ t, t ∈ residualSet B k Y q bd.total → t ≤ k → t ≤ k - Y := by
    intro t htU htk
    have hres_eq :
        residualSet B k Y q bd.total = residualSet B k Y q bTotal :=
      residualSet_ext_of_agree_on_D
        (fun d hd => hbTotal_eq_bd_total d hd)
    have htU_bTotal : t ∈ residualSet B k Y q bTotal := by rwa [hres_eq] at htU
    have htU_big : t ∈ Ubig := by
      rw [hUbig_def]
      exact residualSet_mono_X hk2X htU_bTotal
    by_contra hgt
    push_neg at hgt
    apply hnotBad
    unfold BadK
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨hkX, hk2X⟩, hW_dvd_k, ?_⟩
    exact ⟨t, htU_big, hgt, htk⟩
  have hT_subset :
      (residualSet B k Y q bd.total).filter (fun t => t ≤ k) ⊆
        Finset.Ioc Y (k - Y) := by
    intro t ht
    rw [Finset.mem_filter] at ht
    obtain ⟨htU, htk⟩ := ht
    rw [Finset.mem_Ioc]
    exact ⟨hU_no_small_bdTotal t htU, hEndpoint t htU htk⟩
  have hC_subset :
      CandidatePrimes k Y q ⊆
        (Finset.Ioc (k - Y / 2) k).filter (fun p => p.Prime ∧ p % q = 1) :=
    CandidatePrimes_subset_filter k Y q
  have hT_card_le :
      ((residualSet B k Y q bd.total).filter (fun t => t ≤ k)).card ≤
        (CandidatePrimes k Y q).card := by
    calc ((residualSet B k Y q bd.total).filter (fun t => t ≤ k)).card
        ≤ (residualSet B k Y q bd.total).card :=
          Finset.card_le_card (Finset.filter_subset _ _)
      _ ≤ H_X (M_B B) k := hU_card_bdTotal
      _ ≤ (CandidatePrimes k Y q).card := hCand_PNT
  obtain ⟨smq, hsmq_T_eq⟩ :=
    exists_scaffoldMatchingQ_of_card_le hT_subset hC_subset hT_card_le
  have hq_le_Y_total : q ≤ Y := by
    calc q = q ^ 1 := (pow_one _).symm
      _ ≤ q ^ 20 := Nat.pow_le_pow_right hq_prime.pos (by omega)
      _ ≤ Y := hq_pow20_le_Y
  have hq_le_YY : q ≤ Y * Y := by
    have hY_le_YY : Y ≤ Y * Y := Nat.le_mul_of_pos_left _ (by omega)
    omega
  have h_2YY_Y_le_k : 2 * Y * Y + Y ≤ k := by
    have h_4YY : Y ≤ 4 * Y * Y := by
      calc Y = Y * 1 := by ring
        _ ≤ Y * (4 * Y) := Nat.mul_le_mul_left Y (by omega)
        _ = 4 * Y * Y := by ring
    have h_2YY_plus_Y : 2 * Y * Y + Y ≤ 6 * Y * Y := by linarith
    omega
  have hbuf_neq_q : ∀ d : bd.D, bd.buffer d ≠ q :=
    wcbd_buf_neq_q bd hq_le_YY
  have hscaf_neq_q : ∀ t : smq.T, smq.scaffold t ≠ q :=
    wcbd_scaffold_neq_q smq hq_le_Y_total hY_le_half
  have hscaf_neq_buffer : ∀ t : smq.T, ∀ d : bd.D,
      smq.scaffold t ≠ bd.buffer d :=
    wcbd_scaffold_neq_buffer bd smq h_2YY_Y_le_k
  have hDY_card_succ_le_HX : bd.D.card + 1 ≤ H_X (M_B B) k := by
    show (smallDeficientSet B Y q).card + 1 ≤ H_X (M_B B) k
    exact D_Y_card_succ_le_H_X hq_prime.one_lt hY_lt_q_pow21 hM_B (by omega)
  have hscaf_card_le_HX : smq.T.card ≤ H_X (M_B B) k := by
    rw [hsmq_T_eq]
    exact (Finset.card_le_card (Finset.filter_subset _ _)).trans hU_card_bdTotal
  let core : WideCoverBuildCore B k :=
    { X := k
      Y := Y
      Y_pos := hY_pos
      Y_le_half := hY_le_half
      Y_sq_small := hY_sq_small_k
      q := q
      q_prime := hq_prime
      m_le_q := hq_ge_B
      q_dvd_k := hq_dvd_k
      q_pow20_le_Y := hq_pow20_le_Y
      Y_lt_q_pow21 := hY_lt_q_pow21
      k_ge_4m := hk_ge_4m
      q_le_k_half := hq_le_k_half
      bd := bd
      smq := smq
      scaffold_neq_q := hscaf_neq_q
      buffer_neq_q := hbuf_neq_q
      scaffold_neq_buffer := hscaf_neq_buffer
      DY_card_succ_le_HX := hDY_card_succ_le_HX
      scaffold_card_le_HX := hscaf_card_le_HX }
  have h_dom : k ^ (2 * H_X (M_B B) core.X + 1) <
      ∏ p ∈ (Finset.Ioc (k / 3) (k / 2)).filter Nat.Prime, p ^ 2 := by
    have h := h_dom_all k hk_ge_k₀
    show k ^ (2 * H_X (M_B B) k + 1) < _
    simpa [ThirdHalfPrimes] using h
  have hZ := core.Z_gt_B_j_from_dominance hk10 h_dom
  have hB_le_buffer : ∀ d : bd.D, B ≤ bd.buffer d := by
    intro d
    have hbgt := (bd.buffer_in_range d).1
    omega
  have hB_le_scaffold : ∀ t : smq.T, B ≤ smq.scaffold t := by
    intro t
    have h_scaf_lo := (smq.scaffold_in_range t).1
    have hB_le_Y : B ≤ Y := hq_ge_B.trans hq_le_Y_total
    omega
  have hzero_lt_B : ∀ p, p.Prime → p < B →
      combinedResidue q bd smq.toScaffoldMatching p = 0 :=
    wcbd_combinedResidue_zero_lt_B bd smq hq_ge_B hB_le_buffer hB_le_scaffold
  have hk_le_2X : k ≤ 2 * core.X := by show k ≤ 2 * k; omega
  have hD_eq_core : core.bd.D = smallDeficientSet B Y q := rfl
  have hcore_smq_T_eq :
      core.smq.T =
        (residualSet B core.X core.Y core.q core.bd.total).filter
          (fun t => t ≤ k) := by
    show smq.T = _
    exact hsmq_T_eq
  have hb_prime_on :
      ∀ d ∈ smallDeficientSet B Y q, (bd.total d).Prime := fun d hd => by
    rw [hbTotal_eq_bd_total d hd]; exact hbTotal_prime d hd
  have hb_ne_q_on :
      ∀ d ∈ smallDeficientSet B Y q, bd.total d ≠ q := fun d hd => by
    rw [hbTotal_eq_bd_total d hd]; exact hbTotal_ne_q d hd
  have hb_inj_smallDef :
      Set.InjOn bd.total (smallDeficientSet B Y q) := fun x hx y hy hxy => by
    have hx' : x ∈ bd.D := by rwa [hbd_D_eq]
    have hy' : y ∈ bd.D := by rwa [hbd_D_eq]
    exact hbTotal_inj_on hx' hy' hxy
  have h_img_eq_core :
      core.bufferImage = (smallDeficientSet B Y q).image bd.total := by
    show bd.D.attach.image bd.buffer = (smallDeficientSet B Y q).image bd.total
    rw [bufferImage_eq_image_total bd, hbd_D_eq]
  have h_zSet_aux :
      ∀ j, 1 ≤ j → j ≤ k →
        zSet j core.q core.bufferImage ∣ j ∧
        0 < zSet j core.q core.bufferImage ∧
        ∀ p, p.Prime → p ∣ zSet j core.q core.bufferImage →
          p ≠ core.q ∧ p ∉ core.bufferImage := by
    intro j hj_pos _
    have hcoreq : core.q = q := rfl
    rw [h_img_eq_core, hcoreq]
    exact wcbd_zSet_aux_for_total hq_prime bd.total hb_prime_on
      hb_inj_smallDef hb_ne_q_on j hj_pos
  have h_zSet_eq_total :
      ∀ j, 1 ≤ j → j ≤ k →
        zSet j core.q core.bufferImage =
        zSet j core.q ((smallDeficientSet B core.Y core.q).image core.bd.total) := by
    intro j _ _
    rw [h_img_eq_core]
  have hCov :=
    WideCoverBuildCore.outerB_ge_B_i_from_matching_local hk3 core hD_eq_core
      hcore_smq_T_eq hk_le_2X h_zSet_aux h_zSet_eq_total
  exact ⟨k, hkK, hk3, ⟨core.toData hZ hzero_lt_B hCov⟩⟩

noncomputable def gFromWide {B k : ℕ}
    (wcbd : WideCoverBuildData B k) (i : Fin k) : ℕ :=
  outerB k wcbd.a (k - i.val)

theorem gFromWide_pos {B k : ℕ} (wcbd : WideCoverBuildData B k) (i : Fin k) :
    0 < gFromWide wcbd i := by
  unfold gFromWide
  exact outerB_pos_of_a wcbd.a (k - i.val)
    (by omega) (by omega)

theorem gFromWide_dvd_term_int {B k : ℕ} (wcbd : WideCoverBuildData B k)
    (R n : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k wcbd.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hn_nonneg : 0 ≤ n) (hn_ge_k : k ≤ n.toNat) (i : Fin k) :
    (gFromWide wcbd i : ℤ) ∣ n - (i.val : ℤ) := by
  have hi_lt_k : i.val < k := i.isLt
  have hnat : outerB k wcbd.a (k - i.val) ∣
      n.toNat - i.val :=
    outerB_dvd_term_of_progression_wide wcbd.a wcbd.a_lt_p R n hRloc h_n_mod
      hn_nonneg hn_ge_k i.val hi_lt_k
  have hi_le_n : i.val ≤ n.toNat := by omega
  have hcast : ((n.toNat - i.val : ℕ) : ℤ) = n - (i.val : ℤ) := by
    rw [Nat.cast_sub hi_le_n, Int.toNat_of_nonneg hn_nonneg]
  have hz : (gFromWide wcbd i : ℤ) ∣ ((n.toNat - i.val : ℕ) : ℤ) := by
    show (outerB k wcbd.a (k - i.val) : ℤ) ∣ _
    exact_mod_cast hnat
  rwa [hcast] at hz

theorem quotient_no_prime_le_k_from_wide {B : ℕ} (k : ℕ) (hk3 : 3 ≤ k)
    (wcbd : WideCoverBuildData B k)
    (cov : WideCoverData B k) (hcov_a : cov.a = wcbd.a)
    (hNE : IsNonExcessWide cov) (hSafe : LevelSafe cov.a k B)
    (R n : ℤ)
    (hRloc : ∀ p ∈ primeSet k,
      R ≡ localResidue k cov.a p [ZMOD
        (localMod k p : ℤ)])
    (h_n_mod : (Nk_formula k : ℤ) ∣ n - R)
    (hn_nonneg : 0 ≤ n) (hn_ge_k : k ≤ n.toNat) (i : Fin k) :
    ∀ p : ℕ, p.Prime → p ≤ k →
      ¬ p ∣ (n.toNat - i.val) / gFromWide wcbd i := by
  intro p hp hpk hp_dvd
  have hi_lt_k : i.val < k := i.isLt
  have hq := quotient_has_no_prime_le_k_wide cov hk3 hNE hSafe R n hRloc
    h_n_mod hn_nonneg hn_ge_k i.val hi_lt_k p hp hpk
  apply hq
  have hnum : n.toNat - k + (k - i.val) = n.toNat - i.val := by omega
  have hden : outerB k cov.a (k - i.val)
      = gFromWide wcbd i := by
    unfold gFromWide; rw [hcov_a]
  rwa [hnum, hden]

structure BPZSection6Input (B K : ℕ) where
  k : ℕ
  hkK : K ≤ k
  hk3 : 3 ≤ k
  α : ℤ
  g : Fin k → ℕ
  g_pos : ∀ i : Fin k, 0 < g i
  g_ge_B : ∀ i : Fin k, B ≤ g i
  g_prod_factorial : (∏ i : Fin k, g i) = k.factorial
  progression :
    ∀ n : ℤ, (k : ℤ) < n →
      (Nk_formula k : ℤ) ∣ n - α →
        (∀ i : Fin k, (g i : ℤ) ∣ n - (i.val : ℤ)) ∧
        (∀ p : ℕ, p.Prime → p ≤ k →
          ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ)) ∧
        (∀ i : Fin k, ∀ p : ℕ, p.Prime → p ≤ k →
          ¬ p ∣ (n.toNat - i.val) / g i)

theorem outerB_eq_innerB_of_scaffoldExcess_empty {k : ℕ} (a : ℕ → ℕ) (j : ℕ)
    (h_empty : scaffoldExcess k a j = ∅) :
    outerB k a j =
      innerB k a j := by
  have h_eq := innerB_eq_outerB_mul_scaffold k a j
  rw [h_empty, Finset.prod_empty, mul_one] at h_eq
  exact h_eq.symm

theorem prod_outerB_eq_prod_innerB_of_scaffoldExcess_empty
    {k : ℕ} (a : ℕ → ℕ)
    (h_empty : ∀ j ∈ Finset.Icc 1 k,
      scaffoldExcess k a j = ∅) :
    (∏ j : Fin k, outerB k a (j.val + 1)) =
    (∏ j : Fin k, innerB k a (j.val + 1)) := by
  apply Finset.prod_congr rfl
  intro j _
  apply outerB_eq_innerB_of_scaffoldExcess_empty
  apply h_empty
  rw [Finset.mem_Icc]
  exact ⟨Nat.succ_pos _, j.isLt⟩

theorem excessPrimesSet_empty_of_nonExcessWide {B k : ℕ} (cov : WideCoverData B k)
    (hNE : IsNonExcessWide cov) :
    excessPrimesSet k cov.a = ∅ := by
  rw [Finset.eq_empty_iff_forall_notMem]
  intro p hp
  rw [mem_excessPrimesSet] at hp
  obtain ⟨hp_prime, hp_pos, hpk, hap_ne, hk2lt, hap_pos, hp_ap_le⟩ := hp
  have hap_lt_p : cov.a p < p := cov.a_lt_p p hp_prime
  have hp_in : p ∈ scaffoldExcess k cov.a
      (p + cov.a p) :=
    excess_in_scaffold k cov.a p
      (by rw [mem_excessPrimesSet]
          exact ⟨hp_prime, hp_pos, hpk, hap_ne, hk2lt, hap_pos, hp_ap_le⟩)
      hap_lt_p
  have h_empty := scaffoldExcess_empty_wide cov hNE (k - (p + cov.a p)) p
  have hk_sub : k - (k - (p + cov.a p)) = p + cov.a p := by omega
  rw [hk_sub] at h_empty
  exact h_empty hp_in

private theorem val_sum_innerB_p_dvd_k_a {k : ℕ} (a : ℕ → ℕ) (hk_pos : 0 < k)
    (ha_lt_p : ∀ p, p.Prime → a p < p)
    (p : ℕ) (hp : p.Prime) (hp_dvd_k : p ∣ k) (hp_le_k : p ≤ k) (ha : a p ≠ 0) :
    ∑ j : Fin k, exponent k a (j.val + 1) p =
      padicValNat p k.factorial := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hap_lt_p : a p < p := ha_lt_p p hp
  have hap_pos : 1 ≤ a p := by omega
  rw [sum_exponent_eq_sum_count a p hp hap_pos
    hap_lt_p hp_le_k]
  have h_count_eq : ∀ u ∈ Finset.Icc 1 (alphaP k p),
      ((Finset.univ : Finset (Fin k)).filter
        (fun j => (j.val + 1) % p ^ u =
          liftAtLevel a p u)).card =
        k / p ^ u := by
    intro u hu_mem
    rw [Finset.mem_Icc] at hu_mem
    have hu_pos := hu_mem.1
    have hu_le : u ≤ Nat.log p k := hu_mem.2
    have h_lift_eq : liftAtLevel a p u =
        liftAbove p u (a p) :=
      liftAtLevel_eq_liftAbove a p u ha hu_pos
    rw [h_lift_eq]
    rw [card_Fin_filter_eq_Icc_filter
        (fun x => x % p ^ u = liftAbove p u (a p))]
    exact valuation_sum_non_excess_lift p k hp_dvd_k
      (a p) hap_pos hap_lt_p hk_pos u (Finset.mem_Icc.mpr ⟨hu_pos, hu_le⟩)
  rw [Finset.sum_congr rfl h_count_eq]
  have h_log_lt : Nat.log p k < Nat.log p k + 1 := Nat.lt_succ_self _
  rw [padicValNat_factorial (b := Nat.log p k + 1) h_log_lt]
  apply Finset.sum_bij
    (fun (x : ℕ) (_ : x ∈ Finset.Icc 1 (alphaP k p)) => x)
  · intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_Ico]
    refine ⟨hx.1, ?_⟩
    have : alphaP k p = Nat.log p k := rfl
    omega
  · intros; assumption
  · intro x hx
    rw [Finset.mem_Ico] at hx
    refine ⟨x, ?_, rfl⟩
    rw [Finset.mem_Icc]
    refine ⟨hx.1, ?_⟩
    have : alphaP k p = Nat.log p k := rfl
    omega
  · intros; rfl

private theorem val_sum_innerB_scaffold_a {k : ℕ} (a : ℕ → ℕ) (hk_ge_4 : 4 ≤ k)
    (ha_lt_p : ∀ p, p.Prime → a p < p)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) (hp_gt : k / 2 < p) (ha : a p ≠ 0) :
    ∑ j : Fin k, exponent k a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k a then 1 else 0) := by
  classical
  have hap_lt_p : a p < p := ha_lt_p p hp
  have h_exp_eq : ∀ j : Fin k, exponent k a (j.val + 1) p =
      (if (j.val + 1) % p = a p then 1 else 0) := fun j =>
    exponent_eq_indicator_at_one a (j.val + 1) p
      hp hpk hp_gt hk_ge_4 ha
  rw [show ∑ j : Fin k, exponent k a (j.val + 1) p =
      ∑ j : Fin k, (if (j.val + 1) % p = a p then 1 else 0) from
    Finset.sum_congr rfl (fun j _ => h_exp_eq j)]
  have hap_pos : 1 ≤ a p := by omega
  have hsum_eq_card :
      ∑ j : Fin k, (if (j.val + 1) % p = a p then 1 else 0) =
      ((Finset.Icc 1 k).filter (fun x => x % p = a p)).card := by
    rw [Finset.card_filter]
    rw [show (Finset.Icc 1 k) =
        (Finset.univ : Finset (Fin k)).image (fun j : Fin k => j.val + 1) from ?_]
    · rw [Finset.sum_image]
      intros a _ b _ hab
      apply Fin.ext
      show a.val = b.val
      simp at hab; omega
    · ext x
      simp only [Finset.mem_image, Finset.mem_univ, true_and, Finset.mem_Icc]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨⟨x - 1, by omega⟩, by simp; omega⟩
      · rintro ⟨j, rfl⟩
        exact ⟨Nat.succ_pos _, j.isLt⟩
  rw [hsum_eq_card]
  rw [count_residue_large_prime k p (a p) hp.pos
    hp_gt hpk hap_pos hap_lt_p]
  rw [padicValNat_factorial_eq_one_of_gt_half hp hpk hp_gt]
  by_cases hexcess : p ∈ excessPrimesSet k a
  · rw [if_pos hexcess]
    rw [if_pos]
    have hex := (mem_excessPrimesSet.mp hexcess).2.2.2.2.2.2
    omega
  · rw [if_neg hexcess]
    rw [if_neg]
    intro h_ap_pk
    apply hexcess
    rw [mem_excessPrimesSet]
    refine ⟨hp, hp.pos, hpk, ha, hp_gt, hap_pos, ?_⟩
    omega

private theorem val_sum_innerB_wide {B k : ℕ} (cov : WideCoverData B k)
    (p : ℕ) (hp : p.Prime) (hpk : p ≤ k) :
    ∑ j : Fin k, exponent k cov.a (j.val + 1) p =
      padicValNat p k.factorial +
        (if p ∈ excessPrimesSet k cov.a then 1 else 0) := by
  have hk_pos : 0 < k := by have := cov.k_ge_4m; omega
  have hk_ge_4 : 4 ≤ k := by have := cov.k_ge_4m; omega
  by_cases ha : cov.a p = 0
  · rw [if_neg (p_not_in_excess_of_a_zero ha)]
    rw [Nat.add_zero]
    have heq : ∀ j : Fin k,
        exponent k cov.a (j.val + 1) p =
        padicValNat p (j.val + 1) := by
      intro j
      unfold exponent
      rw [if_pos ha]
    simp_rw [heq]
    exact sum_padicValNat_succ_eq_factorial k p hp
  · by_cases hp_gt : k / 2 < p
    · exact val_sum_innerB_scaffold_a cov.a hk_ge_4 cov.a_lt_p p hp hpk hp_gt ha
    · push_neg at hp_gt
      have hp_dvd : p ∣ k := by
        rcases cov.scaffold p hp ha with h | ⟨h1, _, _⟩
        · exact h
        · omega
      rw [show (if p ∈ excessPrimesSet k cov.a
            then (1 : ℕ) else 0) = 0 from ?_]
      · rw [Nat.add_zero]
        exact val_sum_innerB_p_dvd_k_a cov.a hk_pos cov.a_lt_p p hp hp_dvd hpk ha
      · rw [if_neg]
        intro hex
        rw [mem_excessPrimesSet] at hex
        omega

private theorem prod_innerB_eq_factorial_mul_excess_a {k : ℕ} (a : ℕ → ℕ)
    (h_val_sum : ∀ p : ℕ, p.Prime → p ≤ k →
      ∑ j : Fin k, exponent k a (j.val + 1) p =
        padicValNat p k.factorial +
          (if p ∈ excessPrimesSet k a then 1 else 0)) :
    ∏ j : Fin k, innerB k a (j.val + 1) =
      k.factorial * ∏ p ∈ excessPrimesSet k a, p := by
  classical
  have h_inner_pos : 0 < ∏ j : Fin k,
      innerB k a (j.val + 1) :=
    Finset.prod_pos (fun j _ => innerB_pos k a (j.val + 1))
  have h_excess_pos : 0 < ∏ p ∈ excessPrimesSet k a, p :=
    Finset.prod_pos (fun p hp =>
      (mem_excessPrimesSet.mp hp).1.pos)
  have h_rhs_pos : 0 < k.factorial *
      ∏ p ∈ excessPrimesSet k a, p :=
    Nat.mul_pos (Nat.factorial_pos k) h_excess_pos
  apply Nat.eq_of_factorization_eq h_inner_pos.ne' h_rhs_pos.ne'
  intro p
  by_cases hp_prime : p.Prime
  · by_cases hpk : p ≤ k
    · rw [factorization_prod_innerB_eq_sum_exponent k a p
        hp_prime hpk]
      rw [Nat.factorization_mul (Nat.factorial_pos k).ne' h_excess_pos.ne']
      rw [Finsupp.add_apply]
      rw [Nat.factorization_def _ hp_prime]
      rw [factorization_prod_excessPrimesSet k a p hp_prime]
      exact h_val_sum p hp_prime hpk
    · push_neg at hpk
      have h_LHS_0 : (∏ j : Fin k,
          innerB k a (j.val + 1)).factorization p = 0 := by
        rw [Nat.factorization_eq_zero_iff]
        right; left; intro hdvd
        exact absurd
          (prod_innerB_is_k_smooth k a p hp_prime hdvd)
          (by omega)
      have h_RHS_0 : (k.factorial *
          ∏ q ∈ excessPrimesSet k a, q).factorization p = 0 := by
        rw [Nat.factorization_mul (Nat.factorial_pos k).ne' h_excess_pos.ne']
        rw [Finsupp.add_apply]
        rw [Nat.factorization_def _ hp_prime]
        rw [factorization_prod_excessPrimesSet k a p hp_prime]
        rw [padicValNat_factorial_eq_zero_of_lt hp_prime hpk]
        rw [if_neg (fun h_excess =>
          absurd (excessPrimesSet_le_k h_excess) (by omega))]
      rw [h_LHS_0, h_RHS_0]
  · rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime]
    rw [Nat.factorization_eq_zero_of_not_prime _ hp_prime]

theorem prod_outerB_eq_factorial_wide {B k : ℕ} (cov : WideCoverData B k)
    (hNE : IsNonExcessWide cov) :
    ∏ j : Fin k, outerB k cov.a (j.val + 1) = k.factorial := by
  have h_excess_empty : excessPrimesSet k cov.a = ∅ :=
    excessPrimesSet_empty_of_nonExcessWide cov hNE
  have h_inner_eq : ∏ j : Fin k, innerB k cov.a (j.val + 1)
      = k.factorial := by
    have h := prod_innerB_eq_factorial_mul_excess_a cov.a (val_sum_innerB_wide cov)
    rw [h_excess_empty, Finset.prod_empty, Nat.mul_one] at h
    exact h
  rw [← h_inner_eq]
  apply Finset.prod_congr rfl
  intro j _
  have h_se_empty : scaffoldExcess k cov.a (j.val + 1)
      = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro p
    have h := scaffoldExcess_empty_wide cov hNE (k - (j.val + 1)) p
    have h_eq : k - (k - (j.val + 1)) = j.val + 1 := by have := j.isLt; omega
    rw [h_eq] at h
    exact h
  exact outerB_eq_innerB_of_scaffoldExcess_empty cov.a (j.val + 1) h_se_empty

theorem gFromWide_ge_B {B k : ℕ} (wcbd : WideCoverBuildData B k) (i : Fin k) :
    B ≤ gFromWide wcbd i := wcbd.outerB_ge_B_i i

theorem gFromWide_prod_factorial {B k : ℕ} (wcbd : WideCoverBuildData B k) :
    (∏ i : Fin k, gFromWide wcbd i) = k.factorial := by
  classical
  let cov : WideCoverData B k := wcbd.toWide
  have hcov_a : cov.a = wcbd.a := rfl
  have hNE : IsNonExcessWide cov := by
    intro p hp _ _ hnz
    rw [hcov_a] at hnz ⊢
    exact wcbd.non_excess p hnz
  have h_prod := prod_outerB_eq_factorial_wide cov hNE
  rw [hcov_a] at h_prod
  rw [← h_prod]
  symm
  apply Finset.prod_nbij
    (fun (j : Fin k) => (⟨k - 1 - j.val, by have := j.isLt; omega⟩ : Fin k))
  · intros; exact Finset.mem_univ _
  · intro a _ b _ hab
    apply Fin.ext
    have ha := a.isLt
    have hb := b.isLt
    have : k - 1 - a.val = k - 1 - b.val := Fin.val_eq_of_eq hab
    omega
  · intro i _
    refine ⟨⟨k - 1 - i.val, by have := i.isLt; omega⟩, Finset.mem_univ _, ?_⟩
    apply Fin.ext
    have hi := i.isLt
    show k - 1 - (k - 1 - i.val) = i.val
    omega
  · intro j _
    show outerB k wcbd.a (j.val + 1) =
      gFromWide wcbd ⟨k - 1 - j.val, by have := j.isLt; omega⟩
    unfold gFromWide
    congr 1
    have := j.isLt
    show j.val + 1 = k - (k - 1 - j.val)
    omega

structure BPZSection6InputRefined (B K : ℕ) extends BPZSection6Input B K where
  M : ℕ
  γ : ℤ
  M_pos : 0 < M
  Nk_dvd_M : Nk_formula k ∣ M
  primes_dvd_M : ∀ q : ℕ, q.Prime → k < q → q < 2 * k → q ∣ M
  refined :
    ∀ n : ℤ, (k : ℤ) < n → (M : ℤ) ∣ n - γ →
      (∀ p : ℕ, p.Prime → p < 2 * k →
        ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ)) ∧
      (∀ i j : Fin k, i ≠ j →
        Nat.Coprime ((n.toNat - i.val) / g i) ((n.toNat - j.val) / g j))

theorem fixed_B_cover_section6_input
    (hSW : ShiftedSiegelWalfiszLower) (B K : ℕ) (hB : 3 ≤ B) :
    ∃ S : BPZSection6Input B K, True := by
  obtain ⟨k, hkK, hk3, ⟨wcbd⟩⟩ := wideCoverBuildData_exists hSW B hB K
  let cov : WideCoverData B k := wcbd.toWide
  have hcov_a : cov.a = wcbd.a := rfl
  obtain ⟨R, hRloc⟩ :=
    exists_R_local_modEq_of_a k cov.a
  have hNE : IsNonExcessWide cov := by
    intro p hp _ _ hnz
    rw [hcov_a] at hnz ⊢
    exact wcbd.non_excess p hnz
  have hSafe : LevelSafe cov.a k B := LevelSafe_of_wide cov
  refine ⟨{
    k := k
    hkK := hkK
    hk3 := hk3
    α := R
    g := gFromWide wcbd
    g_pos := gFromWide_pos wcbd
    g_ge_B := gFromWide_ge_B wcbd
    g_prod_factorial := gFromWide_prod_factorial wcbd
    progression := ?_ }, trivial⟩
  intro n hn_gt h_n_mod
  have hn_nonneg : 0 ≤ n := by linarith
  have hn_toNat : (n.toNat : ℤ) = n := Int.toNat_of_nonneg hn_nonneg
  have hn_ge_k : k ≤ n.toNat := by
    have : (k : ℤ) ≤ (n.toNat : ℤ) := by rw [hn_toNat]; linarith
    exact_mod_cast this
  refine ⟨?_, ?_, ?_⟩
  · intro i
    exact gFromWide_dvd_term_int wcbd R n
      (by intro p hp; have := hRloc p hp; rw [hcov_a] at this; exact this)
      h_n_mod hn_nonneg hn_ge_k i
  · exact clause1_holds_for_nonexcess_wide hB k hk3 cov hNE hSafe R hRloc n hn_gt h_n_mod
  · intro i p hp hpk
    exact quotient_no_prime_le_k_from_wide k hk3 wcbd cov hcov_a hNE hSafe
      R n hRloc h_n_mod hn_nonneg hn_ge_k i p hp hpk

theorem fixed_B_cover
    (hSW : ShiftedSiegelWalfiszLower) (B K : ℕ) (hB : 3 ≤ B) :
    ∃ k : ℕ, K ≤ k ∧ 3 ≤ k ∧
      ∃ α_k : ℤ,
        ∀ n : ℤ, (k : ℤ) < n → (Nk_formula k : ℤ) ∣ n - α_k →
          (∀ p : ℕ, p.Prime → p ≤ k → ¬ (p : ℤ) ∣ ((n.toNat).choose k : ℤ)) ∧
          (∀ i : ℕ, i < k → ∃ p : ℕ, p.Prime ∧ B ≤ p ∧ (p : ℤ) ∣ n - (i : ℤ)) := by
  obtain ⟨k, hkK, hk3, ⟨wcbd⟩⟩ := wideCoverBuildData_exists hSW B hB K
  let cov : WideCoverData B k := wcbd.toWide
  have hcov_a : cov.a = wcbd.a := rfl
  obtain ⟨R, hRloc⟩ :=
    exists_R_local_modEq_of_a k cov.a
  have hNE : IsNonExcessWide cov := by
    intro p hp _ _ hnz
    rw [hcov_a] at hnz ⊢
    exact wcbd.non_excess p hnz
  have hSafe : LevelSafe cov.a k B := LevelSafe_of_wide cov
  refine ⟨k, hkK, hk3, R, ?_⟩
  intro n hn_gt h_n_mod
  refine ⟨?_, ?_⟩
  · exact clause1_holds_for_nonexcess_wide hB k hk3 cov hNE hSafe R hRloc n hn_gt h_n_mod
  · exact clause2_holds_from_Z_gt_Bj_wide hB k hk3 cov hNE hSafe wcbd.Z_gt_B_j R hRloc
      n hn_gt h_n_mod


end Erdos387.CoverBPZ
