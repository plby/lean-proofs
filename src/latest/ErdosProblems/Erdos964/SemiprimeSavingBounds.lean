import ErdosProblems.Erdos964.SemiprimeBlockEnvelopes

/-!
# A common saving parameter for the scalar semiprime errors

At scale `L`, products are bounded by `L²`. A parameter `s` with
`s² ≤ M`, `T s ≤ L`, and `s ≤ D` makes every algebraic error at most
`L²/s`, before the explicit logarithmic factors are restored.
-/

namespace Erdos964

open scoped BigOperators
open BoundedGaps.Maynard

theorem semiprime_scalar_saving_bounds (L M U D T s : ℝ)
    (hL : 1 ≤ L) (hM : 1 ≤ M) (hU : 0 ≤ U) (_hT : 0 ≤ T)
    (hML : M ≤ L) (hMU : M * U ≤ L ^ 2)
    (hs : 1 ≤ s) (hsM : s ^ 2 ≤ M) (hTs : T * s ≤ L) (hsD : s ≤ D) :
    M * U / D ≤ L ^ 2 / s ∧
    M * Real.sqrt U ≤ L ^ 2 / s ∧
    U * Real.sqrt M ≤ L ^ 2 / s ∧
    T * Real.sqrt M * Real.sqrt U ≤ L ^ 2 / s ∧
    U ≤ L ^ 2 / s ∧
    (T / M) * Real.sqrt U ≤ L ^ 2 / s := by
  have hLpos : 0 < L := lt_of_lt_of_le zero_lt_one hL
  have hMpos : 0 < M := lt_of_lt_of_le zero_lt_one hM
  have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hs
  have hDpos : 0 < D := hspos.trans_le hsD
  have hsroot : s ≤ Real.sqrt M := Real.le_sqrt_of_sq_le hsM
  have hsleM : s ≤ M := by nlinarith
  have hrootprod : Real.sqrt M * Real.sqrt U ≤ L := by
    calc
      _ = Real.sqrt (M * U) := (Real.sqrt_mul hMpos.le U).symm
      _ ≤ Real.sqrt (L ^ 2) := Real.sqrt_le_sqrt hMU
      _ = L := Real.sqrt_sq hLpos.le
  have hUle : U ≤ L ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hM hU
    linarith
  have hrootU : Real.sqrt U ≤ L := Real.sqrt_le_iff.mpr ⟨hLpos.le, hUle⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (div_le_div_of_nonneg_right hMU hDpos.le).trans
      (div_le_div_of_nonneg_left (sq_nonneg L) hspos hsD)
  · apply (le_div_iff₀ hspos).mpr
    calc
      _ = M * (s * Real.sqrt U) := by ring
      _ ≤ M * (Real.sqrt M * Real.sqrt U) := by gcongr
      _ ≤ M * L := mul_le_mul_of_nonneg_left hrootprod hMpos.le
      _ ≤ L ^ 2 := by nlinarith
  · apply (le_div_iff₀ hspos).mpr
    calc
      _ = U * (s * Real.sqrt M) := by ring
      _ ≤ U * (Real.sqrt M * Real.sqrt M) := by gcongr
      _ = M * U := by rw [Real.mul_self_sqrt hMpos.le]; ring
      _ ≤ _ := hMU
  · apply (le_div_iff₀ hspos).mpr
    calc
      _ = (T * s) * (Real.sqrt M * Real.sqrt U) := by ring
      _ ≤ L * L := by gcongr
      _ = _ := by ring
  · apply (le_div_iff₀ hspos).mpr
    calc
      U * s ≤ U * M := mul_le_mul_of_nonneg_left hsleM hU
      _ = M * U := mul_comm _ _
      _ ≤ _ := hMU
  · apply (le_div_iff₀ hspos).mpr
    calc
      _ = (T * s) * Real.sqrt U / M := by ring
      _ ≤ L * L / M := by gcongr
      _ ≤ L ^ 2 := by simpa only [sq] using div_le_self (sq_nonneg L) hM

theorem semiprime_block_log_bounds (L M U T : ℕ)
    (hL : 4 ≤ L) (hM : 0 < M) (hU : 0 < U) (hT : 0 < T) (hTL : T ≤ L)
    (hMU : (M : ℝ) * U ≤ (L : ℝ) ^ 2) :
    4 * (1 + Real.log (T : ℝ)) ≤ 8 * Real.log (L : ℝ) ∧
    ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤ 4 * Real.log (L : ℝ) ∧
    Real.log (2 * (U : ℝ)) ≤ 3 * Real.log (L : ℝ) ∧
    Real.log (2 * (((M + M) * U : ℕ) : ℝ)) ≤ 4 * Real.log (L : ℝ) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast (show 0 < L by omega)
  have hTpos : (0 : ℝ) < T := by exact_mod_cast hT
  have hUpos : (0 : ℝ) < U := by exact_mod_cast hU
  have hMone : (1 : ℝ) ≤ M := by exact_mod_cast hM
  have hlogL : 1 ≤ Real.log (L : ℝ) := one_le_log_natCast hL
  have hlogTL : Real.log (T : ℝ) ≤ Real.log (L : ℝ) :=
    Real.log_le_log hTpos (by exact_mod_cast hTL)
  have hlogTwo : Real.log 2 ≤ Real.log (L : ℝ) :=
    Real.log_le_log (by norm_num) (by exact_mod_cast (show 2 ≤ L by omega))
  have hlogTwoHalf : (1 / 2 : ℝ) ≤ Real.log 2 := by
    have h := Real.one_sub_inv_le_log_of_pos (by norm_num : (0 : ℝ) < 2)
    norm_num at h ⊢
    linarith
  have hUbound : (U : ℝ) ≤ (L : ℝ) ^ 2 := by
    have h := mul_le_mul_of_nonneg_right hMone hUpos.le
    linarith
  have htwoT : Real.log (2 * (T : ℝ)) ≤ 2 * Real.log (L : ℝ) := by
    rw [Real.log_mul (by norm_num) hTpos.ne']
    linarith
  have htwoU : Real.log (2 * (U : ℝ)) ≤ 3 * Real.log (L : ℝ) := by
    calc
      _ ≤ Real.log (2 * (L : ℝ) ^ 2) := Real.log_le_log (by positivity) (by gcongr)
      _ = Real.log 2 + 2 * Real.log (L : ℝ) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hLpos.ne'), Real.log_pow]
        norm_num
      _ ≤ _ := by linarith
  refine ⟨by linarith, ?_, htwoU, ?_⟩
  · have hcount : ((Nat.log 2 T + 1 : ℕ) : ℝ) ≤ Real.log (2 * (T : ℝ)) / Real.log 2 := by
      simpa only [dyadicExponentRange, Finset.card_range] using card_dyadicExponentRange_le_log hT
    apply hcount.trans
    apply (div_le_iff₀ (Real.log_pos (by norm_num : (1 : ℝ) < 2))).mpr
    nlinarith
  · calc
      _ ≤ Real.log (4 * (L : ℝ) ^ 2) := by
        apply Real.log_le_log
        · positivity
        · push_cast
          nlinarith
      _ = 2 * Real.log 2 + 2 * Real.log (L : ℝ) := by
        rw [Real.log_mul (by norm_num) (pow_ne_zero 2 hLpos.ne'), Real.log_pow,
          show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
        norm_num
      _ ≤ _ := by linarith

theorem dyadicSemiprimeEnvelopes_le_saving (L M U D T : ℕ) (s : ℝ)
    (hL : 4 ≤ L) (hM : 0 < M) (hU : 0 < U) (hT : 0 < T)
    (hML : M ≤ L) (hTL : T ≤ L) (hMU : (M : ℝ) * U ≤ (L : ℝ) ^ 2)
    (hs : 1 ≤ s) (hsM : s ^ 2 ≤ M) (hTs : (T : ℝ) * s ≤ L) (hsD : s ≤ D) :
    dyadicSemiprimeLargeEnvelope M U D T ≤
      160 * akbaryHambrookC3 * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s) ∧
    dyadicSemiprimeCorrectionEnvelope M U T ≤
      (1 + 108 * akbaryHambrookC3) * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s) := by
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 1 ≤ Real.log (L : ℝ) := one_le_log_natCast hL
  have hlogU0 : 0 ≤ Real.log (2 * (U : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using Real.log_natCast_nonneg (2 * U)
  have hlogK0 : 0 ≤ Real.log (2 * (((M + M) * U : ℕ) : ℝ)) := by
    simpa only [Nat.cast_mul, Nat.cast_ofNat] using
      Real.log_natCast_nonneg (2 * ((M + M) * U))
  have hH : 0 ≤ (L : ℝ) ^ 2 / s := by positivity
  obtain ⟨b₁, b₂, b₃, b₄, b₅, b₆⟩ := semiprime_scalar_saving_bounds
    (L : ℝ) M U D T s (by exact_mod_cast (show 1 ≤ L by omega))
    (by exact_mod_cast hM) (Nat.cast_nonneg _) (Nat.cast_nonneg _)
    (by exact_mod_cast hML) hMU hs hsM hTs hsD
  obtain ⟨_, hj, hlogU, hlogK⟩ := semiprime_block_log_bounds L M U T hL hM hU hT hTL hMU
  have hcore :
      (2 / (D : ℝ)) * (M : ℝ) * U +
        2 * (M : ℝ) * Real.sqrt (U : ℝ) + 2 * (U : ℝ) * Real.sqrt (M : ℝ) +
        4 * T * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ) ≤ 10 * ((L : ℝ) ^ 2 / s) := by
    calc
      _ = 2 * ((M : ℝ) * U / D) + 2 * ((M : ℝ) * Real.sqrt (U : ℝ)) +
          2 * ((U : ℝ) * Real.sqrt (M : ℝ)) +
          4 * ((T : ℝ) * Real.sqrt (M : ℝ) * Real.sqrt (U : ℝ)) := by ring
      _ ≤ _ := by linarith
  have hecore : (Real.sqrt (U : ℝ) + 2 * ((T : ℝ) / M)) * Real.sqrt (U : ℝ) ≤
      3 * ((L : ℝ) ^ 2 / s) := by
    rw [add_mul, Real.mul_self_sqrt (Nat.cast_nonneg U)]
    linarith
  constructor
  · unfold dyadicSemiprimeLargeEnvelope
    calc
      _ ≤ (4 * Real.log (L : ℝ)) * akbaryHambrookC3 *
          (10 * ((L : ℝ) ^ 2 / s)) * (4 * Real.log (L : ℝ)) := by gcongr
      _ = _ := by ring
  · unfold dyadicSemiprimeCorrectionEnvelope
    calc
      _ = (U : ℝ) + ((Nat.log 2 T + 1 : ℕ) : ℝ) *
          (3 * akbaryHambrookC3 *
            ((Real.sqrt (U : ℝ) + 2 * ((T : ℝ) / M)) * Real.sqrt (U : ℝ)) *
              Real.log (2 * (U : ℝ))) := by ring
      _ ≤ ((L : ℝ) ^ 2 / s) + (4 * Real.log (L : ℝ)) *
          (3 * akbaryHambrookC3 * (3 * ((L : ℝ) ^ 2 / s)) *
            (3 * Real.log (L : ℝ))) := by gcongr
      _ ≤ _ := by
        have hlogSq : 1 ≤ (Real.log (L : ℝ)) ^ 2 := by nlinarith
        have h := mul_le_mul_of_nonneg_right hlogSq hH
        nlinarith

noncomputable def semiprimeSavingConstant (C : ℝ) : ℝ :=
  8 * (C + 1 + 268 * akbaryHambrookC3)

theorem dyadicSemiprimeFullEnvelope_le_saving (C : ℝ) (B L M U D T : ℕ) (s : ℝ)
    (hC : 0 ≤ C) (hL : 4 ≤ L) (hM : 0 < M) (hU : 0 < U) (hT : 0 < T)
    (hML : M ≤ L) (hTL : T ≤ L) (hMU : (M : ℝ) * U ≤ (L : ℝ) ^ 2)
    (hs : 1 ≤ s) (hsM : s ^ 2 ≤ M) (hTs : (T : ℝ) * s ≤ L) (hsD : s ≤ D)
    (hDlog : (D : ℝ) ≤ (Real.log (L : ℝ)) ^ B) (hslog : s ≤ (Real.log (L : ℝ)) ^ B) :
    (4 * (1 + Real.log (T : ℝ))) *
      (C * (D : ℝ) * (M : ℝ) * U / (Real.log (L : ℝ)) ^ (2 * B) +
        dyadicSemiprimeLargeEnvelope M U D T + dyadicSemiprimeCorrectionEnvelope M U T) ≤
      semiprimeSavingConstant C * (Real.log (L : ℝ)) ^ 3 * ((L : ℝ) ^ 2 / s) := by
  have hc3 := akbaryHambrookC3_pos.le
  have hlog : 1 ≤ Real.log (L : ℝ) := one_le_log_natCast hL
  have hlogpos : 0 < Real.log (L : ℝ) := by linarith
  have hspos : 0 < s := by linarith
  have hH : 0 ≤ (L : ℝ) ^ 2 / s := by positivity
  have hpowpos : 0 < (Real.log (L : ℝ)) ^ B := pow_pos hlogpos B
  have hsmall : C * (D : ℝ) * (M : ℝ) * U / (Real.log (L : ℝ)) ^ (2 * B) ≤
      C * ((L : ℝ) ^ 2 / s) := by
    have hden : (Real.log (L : ℝ)) ^ (2 * B) =
        (Real.log (L : ℝ)) ^ B * (Real.log (L : ℝ)) ^ B := by rw [two_mul, pow_add]
    calc
      _ = C * ((D : ℝ) * ((M : ℝ) * U) /
          ((Real.log (L : ℝ)) ^ B * (Real.log (L : ℝ)) ^ B)) := by rw [hden]; ring
      _ ≤ C * (((Real.log (L : ℝ)) ^ B * (L : ℝ) ^ 2) /
          ((Real.log (L : ℝ)) ^ B * (Real.log (L : ℝ)) ^ B)) := by gcongr
      _ = C * ((L : ℝ) ^ 2 / (Real.log (L : ℝ)) ^ B) := by field_simp
      _ ≤ _ := mul_le_mul_of_nonneg_left
        (div_le_div_of_nonneg_left (sq_nonneg _) hspos hslog) hC
  obtain ⟨hlarge, hcorrection⟩ := dyadicSemiprimeEnvelopes_le_saving
    L M U D T s hL hM hU hT hML hTL hMU hs hsM hTs hsD
  have hinside : C * (D : ℝ) * (M : ℝ) * U / (Real.log (L : ℝ)) ^ (2 * B) +
      dyadicSemiprimeLargeEnvelope M U D T + dyadicSemiprimeCorrectionEnvelope M U T ≤
      (C + 1 + 268 * akbaryHambrookC3) * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s) := by
    have hlogSq : 1 ≤ (Real.log (L : ℝ)) ^ 2 := by nlinarith
    have hCscale : C * ((L : ℝ) ^ 2 / s) ≤
        C * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s) := by
      have h := mul_le_mul_of_nonneg_left hlogSq hC
      have h' := mul_le_mul_of_nonneg_right h hH
      simpa only [mul_one] using h'
    linarith
  have hW := (semiprime_block_log_bounds L M U T hL hM hU hT hTL hMU).1
  calc
    _ ≤ (4 * (1 + Real.log (T : ℝ))) *
        ((C + 1 + 268 * akbaryHambrookC3) * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s)) :=
      mul_le_mul_of_nonneg_left hinside (by have := Real.log_natCast_nonneg T; positivity)
    _ ≤ (8 * Real.log (L : ℝ)) *
        ((C + 1 + 268 * akbaryHambrookC3) * (Real.log (L : ℝ)) ^ 2 * ((L : ℝ) ^ 2 / s)) :=
      mul_le_mul_of_nonneg_right hW (by positivity)
    _ = _ := by unfold semiprimeSavingConstant; ring

end Erdos964
