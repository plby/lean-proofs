import ErdosProblems.Erdos694.Core

namespace Erdos694

open Filter Asymptotics Topology
open scoped BigOperators Nat

/-! ### Helper lemmas for `collision_at_height` -/

/-- Mertens product, lifted along `ℕ → ℝ` (in terms of `primeEulerProdNat`). -/
private lemma mertens_product_nat :
    Tendsto
      (fun Y : ℕ =>
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)))
      atTop (𝓝 1) := by
  have h_yT_to_inf : Tendsto (fun Y : ℕ => ((Y : ℕ) : ℝ)) atTop atTop :=
    tendsto_natCast_atTop_atTop
  have h := _root_.mertens_product.comp h_yT_to_inf
  have h_eq : ∀ᶠ Y : ℕ in atTop,
      (∏ p ∈ Finset.filter Nat.Prime (Finset.Icc 1 ⌊((Y : ℕ) : ℝ)⌋₊),
            ((p : ℝ) / (p - 1))) /
          (Real.exp Real.eulerMascheroniConstant * Real.log ((Y : ℕ) : ℝ)) =
        (primeEulerProdNat Y) /
          (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
    filter_upwards with Y
    have hfloor : ⌊((Y : ℕ) : ℝ)⌋₊ = Y := Nat.floor_natCast Y
    rw [hfloor]
    rfl
  exact h.congr' h_eq

/-- `LowerConstruction.P` tends to infinity as `Y → ∞`. -/
private lemma lc_P_atTop : Tendsto (fun Y : ℕ => LowerConstruction.P Y) atTop atTop := by
  apply Filter.tendsto_atTop_atTop.mpr
  intro M
  obtain ⟨p, hpM, hp_prime⟩ := Nat.exists_infinite_primes M
  refine ⟨p, fun Y hY => ?_⟩
  -- For Y ≥ p, P Y = primorial Y ≥ primorial p ≥ p ≥ M.
  rw [LowerConstruction.P_eq_primorial]
  -- primorial is monotone in Y.
  have h_mono : primorial p ≤ primorial Y := by
    unfold primorial
    refine Finset.prod_le_prod_of_subset_of_one_le' ?_ ?_
    · intro q hq
      rw [Finset.mem_filter] at hq ⊢
      refine ⟨?_, hq.2⟩
      have hq_lt : q < p + 1 := Finset.mem_range.mp hq.1
      exact Finset.mem_range.mpr (by omega)
    · intros q hq _
      rw [Finset.mem_filter] at hq
      exact hq.2.one_le
  -- p ≤ primorial p (since p ∈ filter Prime (range (p+1))).
  have h_p_le : p ≤ primorial p := by
    unfold primorial
    have hp_mem : p ∈ Finset.filter Nat.Prime (Finset.range (p + 1)) := by
      rw [Finset.mem_filter]
      exact ⟨Finset.mem_range.mpr (Nat.lt_succ_self p), hp_prime⟩
    have h_prod_singleton : p = ∏ x ∈ ({p} : Finset ℕ), id x := by simp
    calc p = ∏ x ∈ ({p} : Finset ℕ), id x := h_prod_singleton
      _ ≤ ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), id x := by
          refine Finset.prod_le_prod_of_subset_of_one_le'
            (Finset.singleton_subset_iff.mpr hp_mem) ?_
          intros q hq _
          rw [Finset.mem_filter] at hq
          exact hq.2.one_le
      _ = ∏ x ∈ Finset.filter Nat.Prime (Finset.range (p + 1)), x := by
          simp
  linarith

/-- Size bound for the construction: `n ≤ exp((2 log C + (4L+1) log 4 + 1) · Y)`. -/
private lemma collision_size_bound (Y U ℓ : ℕ) (C : ℝ) (L : ℕ)
    (hC : 1 ≤ C) (hL : 1 ≤ L)
    (hℓ_prime : Nat.Prime ℓ) (hU_pos : 0 < U) (hU_lt_ℓ : U < ℓ)
    (hAU : LowerConstruction.A Y * U = ℓ - 1)
    (hℓ_le : (ℓ : ℝ) ≤ C * ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ^ L)
    (hY1 : 1 ≤ Y) :
    (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
      Real.exp ((2 * Real.log C + (4 * L + 1) * Real.log 4 + 1) * Y) := by
  classical
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hℓ_pos : 0 < ℓ := hℓ_prime.pos
  have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
  have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
  -- Step 1: φ(ℓ Q) ≤ A Y · ℓ².
  have h_n_le : Nat.totient (ℓ * LowerConstruction.Q Y U) ≤
      LowerConstruction.A Y * (ℓ * ℓ) :=
    LowerConstruction.collision_n_le_A_mul_ell_sq Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
  have h_n_le_R :
      (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ) ≤
        (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := by
    have h0 := (Nat.cast_le (α := ℝ)).mpr h_n_le
    push_cast at h0
    linarith [h0]
  -- Step 2: A Y ≤ 4^Y, P Y ≤ 4^Y, in ℝ.
  have hA_le4 : (LowerConstruction.A Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.A_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_le4 : (LowerConstruction.P Y : ℝ) ≤ (4 : ℝ) ^ Y := by
    have := LowerConstruction.P_le_four_pow Y
    have h := (Nat.cast_le (α := ℝ)).mpr this
    push_cast at h
    exact h
  have hP_nn : (0 : ℝ) ≤ (LowerConstruction.P Y : ℝ) := by exact_mod_cast Nat.zero_le _
  have h4_pow_pos : (0 : ℝ) < (4 : ℝ) ^ Y := by positivity
  -- A Y * P Y ≤ 4^(2Y).
  have hAP_le : ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) ≤
      (4 : ℝ) ^ (2 * Y) := by
    push_cast
    calc (LowerConstruction.A Y : ℝ) * (LowerConstruction.P Y : ℝ)
        ≤ (4 : ℝ) ^ Y * (4 : ℝ) ^ Y :=
          mul_le_mul hA_le4 hP_le4 hP_nn (by positivity)
      _ = (4 : ℝ) ^ (Y + Y) := by rw [pow_add]
      _ = (4 : ℝ) ^ (2 * Y) := by ring_nf
  have hAP_nn : (0 : ℝ) ≤ ((LowerConstruction.A Y * LowerConstruction.P Y : ℕ) : ℝ) := by
    exact_mod_cast Nat.zero_le _
  -- ℓ ≤ C · 4^(2LY).
  have hℓ_le2 : (ℓ : ℝ) ≤ C * ((4 : ℝ) ^ (2 * Y)) ^ L := by
    apply hℓ_le.trans
    apply mul_le_mul_of_nonneg_left _ (by linarith : (0:ℝ) ≤ C)
    exact pow_le_pow_left₀ hAP_nn hAP_le L
  have h4_pow_id : ((4 : ℝ) ^ (2 * Y)) ^ L = (4 : ℝ) ^ (2 * Y * L) := by
    rw [← pow_mul]
  rw [h4_pow_id] at hℓ_le2
  have hℓ_nn : (0 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast Nat.zero_le _
  -- ℓ² ≤ C² · 4^(4YL).
  have hℓ_sq_le : (ℓ : ℝ) * (ℓ : ℝ) ≤ C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
    have h_step : (ℓ : ℝ) * (ℓ : ℝ) ≤
        (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) :=
      mul_le_mul hℓ_le2 hℓ_le2 hℓ_nn (by positivity)
    have h_eq : (C * (4 : ℝ) ^ (2 * Y * L)) * (C * (4 : ℝ) ^ (2 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ (4 * Y * L) := by
      rw [show (4 * Y * L) = (2 * Y * L) + (2 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq ▸ h_step]
  -- A Y · ℓ² ≤ C² · 4^((4L+1)Y).
  have h_total : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
      C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
    have hsq_nn : (0 : ℝ) ≤ (ℓ : ℝ) * (ℓ : ℝ) := mul_nonneg hℓ_nn hℓ_nn
    have h_step1 : (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) ≤
        (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) := by
      exact mul_le_mul hA_le4 hℓ_sq_le hsq_nn (by positivity)
    have h_eq2 : (4 : ℝ) ^ Y * (C ^ 2 * (4 : ℝ) ^ (4 * Y * L)) =
        C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := by
      rw [show ((4 * L + 1) * Y) = Y + (4 * Y * L) by ring, pow_add]
      ring
    linarith [h_eq2 ▸ h_step1]
  -- Now bound C² · 4^((4L+1)Y) ≤ exp(K·Y).
  have hC_pos : 0 < C := by linarith
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have h_C2_pos : 0 < C ^ 2 := pow_pos hC_pos 2
  have h_4pow_pos : (0 : ℝ) < (4 : ℝ) ^ ((4 * L + 1) * Y) := by positivity
  have h_lhs_pos : (0 : ℝ) < C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) :=
    mul_pos h_C2_pos h_4pow_pos
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hY_R : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
  have hY_nn : (0 : ℝ) ≤ (Y : ℝ) := by linarith
  have h_log_lhs : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) =
      2 * Real.log C + ((4 * L + 1) * Y : ℕ) * Real.log 4 := by
    rw [Real.log_mul h_C2_pos.ne' h_4pow_pos.ne', Real.log_pow, Real.log_pow]
    push_cast
    ring
  have h_KY_ge_log : Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y)) ≤ K * Y := by
    rw [h_log_lhs, hK_def]
    push_cast
    -- Want: 2 log C + (4L+1) Y log 4 ≤ (2 log C + (4L+1) log 4 + 1) * Y.
    nlinarith [hlogC_nn, hY_R, hlog4_pos, hL_pos_R,
      mul_nonneg hlogC_nn (by linarith : (0:ℝ) ≤ (Y:ℝ) - 1)]
  -- Combine.
  calc (Nat.totient (ℓ * LowerConstruction.Q Y U) : ℝ)
      ≤ (LowerConstruction.A Y : ℝ) * ((ℓ : ℝ) * (ℓ : ℝ)) := h_n_le_R
    _ ≤ C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y) := h_total
    _ = Real.exp (Real.log (C ^ 2 * (4 : ℝ) ^ ((4 * L + 1) * Y))) :=
        (Real.exp_log h_lhs_pos).symm
    _ ≤ Real.exp (K * Y) := Real.exp_le_exp.mpr h_KY_ge_log

/-- **Auxiliary height theorem — analytic combination of Mertens + a Linnik
hypothesis.**

This theorem is the height-form version of the lower-bound construction. It
takes a Linnik-style prime-existence hypothesis as an *explicit argument*;
the closed theorem itself has no extra axiom dependencies.

Concretely: given absolute constants `C, L ≥ 1` and a Linnik-form input
(existence of a prime `ℓ` with `M ∣ ℓ - 1` and polynomial bound `ℓ ≤ C · M^L`
for every `M ≥ 1`), there exists `K > 0` such that for every sufficiently large
`Y`, the explicit construction `a := ℓ · Q_Y(U)`, `b := P_Y · U · Q_Y(U)` (with
`U := (ℓ - 1) / A_Y` and `ℓ` the Linnik prime for `M = A_Y · P_Y`) yields a
totient collision with the right ratio and `n ≤ exp(K · Y)`.

The proof packages the analytic combination (Mertens product asymptotic on
`(P_Y / A_Y) · ((ℓ-1)/ℓ)`, plus the size bound `A_Y ≤ 4^Y` and
`ℓ ≤ C · (A_Y P_Y)^L ≤ C · 16^(LY)`) into a single height-level statement,
the unconditional lower bound now uses the separate dyadic-prime route.

Trust boundary: standard Lean axioms only; the Linnik input is taken
as an explicit hypothesis rather than from the shared declaration. -/
theorem collision_at_height :
    ∀ (C : ℝ) (L : ℕ), 1 ≤ C → 1 ≤ L →
      (∀ M : ℕ, 1 ≤ M →
        ∃ ℓ : ℕ, Nat.Prime ℓ ∧ M ∣ ℓ - 1 ∧ (ℓ : ℝ) ≤ C * (M : ℝ) ^ L) →
      ∀ ε : ℝ, 0 < ε →
        ∃ K : ℝ, 0 < K ∧
          ∀ᶠ Y : ℕ in atTop,
            ∃ a b n : ℕ,
              1 ≤ a ∧ 1 ≤ b ∧ 1 ≤ n ∧
              Nat.totient a = n ∧ Nat.totient b = n ∧
              (b : ℝ) / a ≥
                (Real.exp Real.eulerMascheroniConstant - ε) * Real.log Y ∧
              (n : ℝ) ≤ Real.exp (K * Y) := by
  intro C L hC hL hLinnik ε hε
  classical
  -- Set K := 2 log C + (4L+1) log 4 + 1.
  set K : ℝ := 2 * Real.log C + (4 * L + 1) * Real.log 4 + 1 with hK_def
  have hlog4_pos : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have hlogC_nn : 0 ≤ Real.log C := Real.log_nonneg hC
  have hL_pos_R : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
  have hK_pos : 0 < K := by
    have h2 : 0 < (4 * (L : ℝ) + 1) * Real.log 4 :=
      mul_pos (by linarith) hlog4_pos
    linarith
  refine ⟨K, hK_pos, ?_⟩
  set γc : ℝ := Real.exp Real.eulerMascheroniConstant with hγc_def
  have hγc_pos : 0 < γc := Real.exp_pos _
  -- Helper: build the collision triple with size bound.
  -- The construction is the same in both cases; only the ratio bound differs.
  -- For each Y ≥ 1, given the Linnik input, we extract (ℓ, U) and pack the triple.
  -- We prove the conclusion in two cases on γc vs ε.
  by_cases hcase : γc ≤ ε
  · -- Easy case: (γc - ε) log Y ≤ 0, any nonneg ratio works.
    filter_upwards [Filter.eventually_ge_atTop 1] with Y hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]
      exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]
        exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- ratio nonneg ≥ (γc - ε) log Y (which is ≤ 0).
      have hℓQ_pos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      have hℓQR_pos : (0 : ℝ) < ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast hℓQ_pos
      have hPUQR_nn : (0 : ℝ) ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        by exact_mod_cast Nat.zero_le _
      have h_ratio_nn :
          0 ≤ ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
              ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) :=
        div_nonneg hPUQR_nn hℓQR_pos.le
      have hYR_nn : (0 : ℝ) ≤ Real.log (Y : ℝ) := by
        have : (1 : ℝ) ≤ (Y : ℝ) := by exact_mod_cast hY1
        exact Real.log_nonneg this
      have h_rhs_nonpos : (γc - ε) * Real.log (Y : ℝ) ≤ 0 :=
        mul_nonpos_of_nonpos_of_nonneg (by linarith) hYR_nn
      linarith
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1
  · -- Main case: γc > ε. Use Mertens to get the ratio bound.
    push Not at hcase
    have hγc_eps_pos : 0 < γc - ε := by linarith
    have hε2_pos : 0 < ε / 2 := by linarith
    have hγc_eps2_pos : 0 < γc - ε / 2 := by linarith
    -- From Mertens: primeEulerProdNat Y ≥ (γc - ε/2) log Y eventually.
    -- Strategy: ratio (ppN / γc·logY) → 1, so eventually ratio ≥ (γc - ε/2) / γc.
    have h_thresh1_lt : (γc - ε / 2) / γc < 1 := by
      rw [div_lt_one hγc_pos]
      linarith
    have h_mertens_ge :
        ∀ᶠ Y : ℕ in atTop,
          (γc - ε / 2) / γc ≤
            (primeEulerProdNat Y) /
              (Real.exp Real.eulerMascheroniConstant * Real.log (Y : ℝ)) := by
      -- ratio → 1 > (γc - ε/2) / γc, so eventually ratio ≥ (γc - ε/2)/γc.
      have h_lt : (γc - ε / 2) / γc < 1 := h_thresh1_lt
      exact mertens_product_nat.eventually_const_le h_lt
    have h_logY_pos : ∀ᶠ Y : ℕ in atTop, 0 < Real.log (Y : ℝ) := by
      filter_upwards [Filter.eventually_ge_atTop 2] with Y hY2
      have : (1 : ℝ) < (Y : ℝ) := by exact_mod_cast hY2
      exact Real.log_pos this
    have h_prime_ge : ∀ᶠ Y : ℕ in atTop,
        (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
      filter_upwards [h_mertens_ge, h_logY_pos] with Y hmer hlogY
      have hγc_logY_pos : 0 < γc * Real.log (Y : ℝ) := mul_pos hγc_pos hlogY
      -- hmer: (γc - ε/2)/γc ≤ ppN/(γc·logY).
      -- Multiply both sides by γc·logY > 0.
      have h1 := mul_le_mul_of_nonneg_right hmer hγc_logY_pos.le
      have h_lhs_eq : (γc - ε / 2) / γc * (γc * Real.log (Y : ℝ)) =
          (γc - ε / 2) * Real.log (Y : ℝ) := by
        field_simp
      have h_rhs_eq :
          primeEulerProdNat Y / (γc * Real.log (Y : ℝ)) *
            (γc * Real.log (Y : ℝ)) = primeEulerProdNat Y := by
        field_simp
      -- combine
      have : (γc - ε / 2) * Real.log (Y : ℝ) ≤ primeEulerProdNat Y := by
        rw [← h_lhs_eq, ← h_rhs_eq]
        exact h1
      exact this
    -- Now bound (ℓ-1)/ℓ ≥ rat := (γc - ε)/(γc - ε/2). For this we need ℓ ≥ M₀.
    set rat : ℝ := (γc - ε) / (γc - ε / 2) with hrat_def
    have hrat_lt_one : rat < 1 := by
      rw [hrat_def, div_lt_one hγc_eps2_pos]
      linarith
    have hrat_pos : 0 < rat := div_pos hγc_eps_pos hγc_eps2_pos
    have h1mr_pos : 0 < 1 - rat := by linarith
    set M₀ : ℕ := ⌈(1 - rat)⁻¹⌉₊ + 1 with hM₀_def
    -- For ℓ ≥ M₀, (ℓ-1)/ℓ ≥ rat.
    have h_ratio_bound : ∀ ℓ : ℕ, M₀ ≤ ℓ →
        rat ≤ ((ℓ - 1 : ℕ) : ℝ) / (ℓ : ℝ) := by
      intro ℓ hℓM₀
      have hℓ_pos : 0 < ℓ := by
        rw [hM₀_def] at hℓM₀
        omega
      have hℓ_one : 1 ≤ ℓ := hℓ_pos
      have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]
        push_cast
        ring
      rw [hℓm1_cast, le_div_iff₀ hℓR_pos]
      -- Want rat * ℓ ≤ ℓ - 1, i.e., (1 - rat) * ℓ ≥ 1.
      have h_ge_inv : (1 - rat)⁻¹ ≤ (ℓ : ℝ) := by
        have h1 : ((⌈(1 - rat)⁻¹⌉₊ : ℕ) : ℝ) ≤ (ℓ : ℝ) := by
          have : ⌈(1 - rat)⁻¹⌉₊ ≤ ℓ := by
            rw [hM₀_def] at hℓM₀
            omega
          exact_mod_cast this
        exact (Nat.le_ceil _).trans h1
      have h_one_le : 1 ≤ (1 - rat) * (ℓ : ℝ) := by
        have h1 : (1 - rat)⁻¹ * (1 - rat) = 1 := inv_mul_cancel₀ h1mr_pos.ne'
        have h2 : (1 - rat)⁻¹ * (1 - rat) ≤ (ℓ : ℝ) * (1 - rat) :=
          mul_le_mul_of_nonneg_right h_ge_inv h1mr_pos.le
        rw [h1] at h2
        linarith
      linarith
    -- For Y large, the Linnik prime ℓ ≥ A·P + 1 ≥ P + 1 ≥ M₀.
    -- Since P Y → ∞, we get P Y ≥ M₀ eventually.
    have h_P_ge_M₀ : ∀ᶠ Y : ℕ in atTop, M₀ ≤ LowerConstruction.P Y :=
      lc_P_atTop.eventually_ge_atTop M₀
    -- Combine all eventual conditions.
    filter_upwards [h_prime_ge, h_logY_pos, h_P_ge_M₀, Filter.eventually_ge_atTop 1]
      with Y hPrime hLogY hPM₀ hY1
    have hAP_pos : 1 ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
      Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (LowerConstruction.A_pos Y).ne' (LowerConstruction.P_pos Y).ne')
    obtain ⟨ℓ, hℓ_prime, hℓ_dvd, hℓ_le⟩ :=
      hLinnik (LowerConstruction.A Y * LowerConstruction.P Y) hAP_pos
    have hℓ_pos : 0 < ℓ := hℓ_prime.pos
    have hℓ_two : 2 ≤ ℓ := hℓ_prime.two_le
    have hA_dvd : LowerConstruction.A Y ∣ ℓ - 1 :=
      dvd_trans ⟨LowerConstruction.P Y, rfl⟩ hℓ_dvd
    have hA_pos : 0 < LowerConstruction.A Y := LowerConstruction.A_pos Y
    have hP_pos : 0 < LowerConstruction.P Y := LowerConstruction.P_pos Y
    -- ℓ ≥ A·P + 1: from A·P ∣ ℓ - 1 and ℓ - 1 ≥ 1.
    have hAP_dvd_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ ℓ - 1 := hℓ_dvd
    have hℓm1_pos : 1 ≤ ℓ - 1 := by omega
    have hAP_le_lm1 : LowerConstruction.A Y * LowerConstruction.P Y ≤ ℓ - 1 :=
      Nat.le_of_dvd (by omega) hAP_dvd_lm1
    have hP_le_lm1 : LowerConstruction.P Y ≤ ℓ - 1 := by
      have h1 : LowerConstruction.P Y ≤ LowerConstruction.A Y * LowerConstruction.P Y :=
        Nat.le_mul_of_pos_left _ hA_pos
      linarith
    have hM₀_le_ℓ : M₀ ≤ ℓ := by
      have : M₀ ≤ LowerConstruction.P Y := hPM₀
      omega
    set U : ℕ := (ℓ - 1) / LowerConstruction.A Y with hU_def
    have hAU : LowerConstruction.A Y * U = ℓ - 1 := by
      rw [hU_def]
      exact Nat.mul_div_cancel' hA_dvd
    have hP_dvd_U : LowerConstruction.P Y ∣ U := by
      have h1 : LowerConstruction.A Y * LowerConstruction.P Y ∣ LowerConstruction.A Y * U := by
        rw [hAU]
        exact hℓ_dvd
      exact (Nat.mul_dvd_mul_iff_left hA_pos).mp h1
    have hU_pos : 0 < U := Nat.pos_of_ne_zero fun h => by
      have hℓm1_zero : ℓ - 1 = 0 := by rw [← hAU, h, Nat.mul_zero]
      have hℓ_le_one : ℓ ≤ 1 := by omega
      exact (Nat.lt_irrefl 1) (lt_of_lt_of_le hℓ_prime.one_lt hℓ_le_one)
    have hU_lt_ℓ : U < ℓ := by
      have hA_ge_1 : 1 ≤ LowerConstruction.A Y := hA_pos
      have h1 : U ≤ LowerConstruction.A Y * U := Nat.le_mul_of_pos_left _ hA_ge_1
      omega
    refine ⟨ℓ * LowerConstruction.Q Y U, LowerConstruction.P Y * U * LowerConstruction.Q Y U,
        Nat.totient (ℓ * LowerConstruction.Q Y U),
        ?_, ?_, ?_, rfl, ?_, ?_, ?_⟩
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero hℓ_prime.ne_zero (LowerConstruction.Q_pos Y U).ne')
    · exact Nat.one_le_iff_ne_zero.mpr
        (mul_ne_zero (mul_ne_zero hP_pos.ne' hU_pos.ne') (LowerConstruction.Q_pos Y U).ne')
    · have hpos : 0 < ℓ * LowerConstruction.Q Y U :=
        Nat.mul_pos hℓ_pos (LowerConstruction.Q_pos Y U)
      exact Nat.one_le_iff_ne_zero.mpr (Nat.totient_pos.mpr hpos).ne'
    · exact (LowerConstruction.totient_a_eq_totient_b Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU).symm
    · -- The main ratio bound: b/a ≥ (γc - ε) log Y.
      -- b/a = primeEulerProdNat Y · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat = (γc - ε) log Y.
      have h_ratio_eq :
          ((LowerConstruction.P Y * U * LowerConstruction.Q Y U : ℕ) : ℝ) /
            ((ℓ * LowerConstruction.Q Y U : ℕ) : ℝ) =
              primeEulerProdNat Y * ((ℓ - 1 : ℝ) / ℓ) :=
        LowerConstruction.collision_ratio Y U ℓ hℓ_prime hU_pos hU_lt_ℓ hAU
      rw [ge_iff_le, h_ratio_eq]
      -- Cast (ℓ - 1 : ℕ) = (ℓ : ℝ) - 1.
      have hℓ_one : 1 ≤ ℓ := hℓ_prime.one_le
      have hℓm1_cast : ((ℓ - 1 : ℕ) : ℝ) = (ℓ : ℝ) - 1 := by
        rw [Nat.cast_sub hℓ_one]
        push_cast
        ring
      have h_rat_le : rat ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        rw [← hℓm1_cast]
        exact h_ratio_bound ℓ hM₀_le_ℓ
      -- primeEulerProdNat Y ≥ (γc - ε/2) log Y > 0.
      have hPpN_pos : 0 ≤ primeEulerProdNat Y := by
        have h1 : (γc - ε / 2) * Real.log (Y : ℝ) ≥ 0 :=
          mul_nonneg hγc_eps2_pos.le hLogY.le
        linarith [hPrime]
      have h_prod_lb :
          (γc - ε) * Real.log (Y : ℝ) ≤
            ((γc - ε / 2) * Real.log (Y : ℝ)) * rat := by
        -- (γc - ε/2) * rat = γc - ε.
        have h_prod_eq : (γc - ε / 2) * rat = γc - ε := by
          rw [hrat_def, mul_div_assoc']
          rw [mul_div_cancel_left₀ _ hγc_eps2_pos.ne']
        rw [show ((γc - ε / 2) * Real.log (Y : ℝ)) * rat =
            ((γc - ε / 2) * rat) * Real.log (Y : ℝ) by ring]
        rw [h_prod_eq]
      -- Combine: ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat ≥ (γc - ε) log Y.
      have h_ratio_lb :
          (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
        have hℓR_pos : 0 < (ℓ : ℝ) := by exact_mod_cast hℓ_pos
        -- ppN · (ℓ-1)/ℓ ≥ (γc - ε/2) log Y · rat:
        -- Use: ppN ≥ (γc - ε/2) log Y ≥ 0, (ℓ-1)/ℓ ≥ rat ≥ 0.
        have h1 : 0 ≤ ((γc - ε / 2) * Real.log (Y : ℝ)) := mul_nonneg hγc_eps2_pos.le hLogY.le
        have h2 : 0 ≤ rat := hrat_pos.le
        have h3 : 0 ≤ ((ℓ : ℝ) - 1) / (ℓ : ℝ) := by
          have : (1 : ℝ) ≤ (ℓ : ℝ) := by exact_mod_cast hℓ_one
          have h_lm1_nn : 0 ≤ (ℓ : ℝ) - 1 := by linarith
          exact div_nonneg h_lm1_nn hℓR_pos.le
        have h_first : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * rat :=
          mul_le_mul_of_nonneg_right hPrime h2
        have h_second : primeEulerProdNat Y * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          mul_le_mul_of_nonneg_left h_rat_le hPpN_pos
        have : (γc - ε / 2) * Real.log (Y : ℝ) * rat ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) :=
          le_trans h_first h_second
        rw [show primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) by ring]
        exact this
      -- Goal currently: (γc - ε) * log Y ≤ ppN * ((ℓ - 1) / ℓ).
      -- ((ℓ : ℝ) - 1)/(ℓ : ℝ) is what shows up after the rewrite.
      have h_combined :
          (γc - ε) * Real.log (Y : ℝ) ≤
            primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
        calc (γc - ε) * Real.log (Y : ℝ)
            ≤ (γc - ε / 2) * Real.log (Y : ℝ) * rat := h_prod_lb
          _ ≤ primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by
              have : primeEulerProdNat Y * ((ℓ : ℝ) - 1) / (ℓ : ℝ) =
                  primeEulerProdNat Y * (((ℓ : ℝ) - 1) / (ℓ : ℝ)) := by ring
              linarith [this ▸ h_ratio_lb]
      exact h_combined
    · exact collision_size_bound Y U ℓ C L hC hL hℓ_prime hU_pos hU_lt_ℓ hAU hℓ_le hY1


end Erdos694
