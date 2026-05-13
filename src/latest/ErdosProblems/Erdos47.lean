/- leanprover/lean4:v4.29.1  mathlib v4.29.1 -/
import UnitFractions.Definitions
import UnitFractions.FinalResults

namespace Erdos47

open UnitFractions
open Filter Finset Real
open scoped ArithmeticFunction.omega BigOperators

theorem unit_fractions_upper_log_density :
    ∃ C : ℝ, 0 < C ∧ ∀ᶠ N : ℕ in atTop, ∀ A : Finset ℕ, A ⊆ Icc 1 N →
      C * ((log (log (log N)) / log (log N)) * log N) ≤ rec_sum A →
        ∃ S ⊆ A, rec_sum S = 1 := by
  classical
  obtain ⟨C₁, h0C₁, hdiv⟩ := harmonic_filter_div
  obtain ⟨C₂, h0C₂, hreg⟩ := harmonic_filter_reg
  obtain ⟨C₃, h0C₃, hsmooth⟩ := harmonic_filter_smooth
  obtain ⟨C₁', hdivth⟩ := Filter.eventually_atTop.mp hdiv
  obtain ⟨C₂', hregth⟩ := Filter.eventually_atTop.mp hreg
  obtain ⟨C₃', hsmoothth⟩ := Filter.eventually_atTop.mp hsmooth
  let C : ℝ := 2 + 2 * C₃ + C₁ + C₂ + 2
  have h0C : 0 < C := by positivity
  obtain ⟨C₀, hcor⟩ := Filter.eventually_atTop.mp corollary_one
  obtain ⟨Cinc, hinc⟩ := this_fun_increasing
  refine ⟨C, h0C, ?_⟩
  filter_upwards
      [ eventually_gt_atTop 1
      , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (1 : ℝ))
      , (tendsto_log_atTop.comp tendsto_log_log_coe_at_top).eventually
          (eventually_ge_atTop (1 : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (C₀ : ℝ))
      , eventually_ge_atTop C₁'
      , eventually_ge_atTop C₂'
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (C₃' : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (Cinc : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_gt_atTop (1 : ℝ))
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          (eventually_ge_atTop (exp (exp (1 : ℝ))))
      , the_last_large_N C₃ h0C₃
      , (this_function_big_tends_to.comp tendsto_natCast_atTop_atTop).eventually
          harmonic_sum_bound_two' ] with
    N hN h0logN h0loglogN_ev h1loglogN_ev h1log3N_ev hlargeN hdivth' hregth' hsmoothth' hincth
      hlargeN₂ hlargeN₃ hlargeN₄ hharmonic
  have h0loglogN : 0 < log (log N) := by
    simpa using h0loglogN_ev
  have h1loglogN : 1 < log (log N) := by
    simpa using h1loglogN_ev
  have h1log3N : 1 ≤ log (log (log N)) := by
    simpa [Function.comp] using h1log3N_ev
  let ε : ℝ := log (log (log N)) / log (log N)
  let ε' : ℝ := 1 / log (log N)
  have h0ε : 0 < ε := by
    refine div_pos ?_ h0loglogN
    exact Real.log_pos h1loglogN
  have h01ε : 0 < 1 / ε := by
    exact one_div_pos.mpr h0ε
  have hε1 : ε < 1 := by
    rw [div_lt_one h0loglogN]
    exact log_lt_self h0loglogN
  intro A hAN hrecA
  let A' := A.filter fun n : ℕ => (N : ℝ) ^ ε ≤ n
  have hrecA' : (2 + 2 * C₃ + C₁ + C₂) * ε * log N ≤ rec_sum A' := by
    have hAtemp : A' ∪ (A \ A') = A := by
      exact Finset.union_sdiff_of_subset (Finset.filter_subset _ _)
    by_contra h
    rw [not_le] at h
    have hotherrec : (rec_sum (A \ A') : ℝ) ≤ 2 * ε * log N := by
      rw [rec_sum]
      push_cast
      calc
        Finset.sum (A \ A') (fun n => (1 : ℝ) / n)
            ≤ Finset.sum (range (⌈(N : ℝ) ^ ε⌉₊)) (fun n => (1 : ℝ) / n) := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
          · intro n hn
            rw [mem_range]
            rw [Finset.mem_sdiff, Finset.mem_filter, not_and, not_le] at hn
            rw [Nat.lt_ceil]
            exact hn.2 hn.1
          · intro n hn1 hn2
            exact one_div_nonneg.mpr (Nat.cast_nonneg n)
        _ ≤ 2 * ε * log N := by
          rw [mul_assoc, ← Real.log_rpow]
          · exact hharmonic
          · exact_mod_cast lt_trans zero_lt_one hN
    have hbad : (rec_sum A : ℝ) < C * (ε * log N) := by
      have hsum : (rec_sum A : ℝ) ≤ rec_sum A' + rec_sum (A \ A') := by
        simpa [hAtemp] using (rec_sum_union (A := A') (B := A \ A'))
      have hsumlt : rec_sum A' + rec_sum (A \ A') < C * (ε * log N) := by
        have hsumlt' := add_lt_add_of_lt_of_le h hotherrec
        dsimp [C] at hsumlt' ⊢
        nlinarith
      exact lt_of_le_of_lt hsum hsumlt
    exact not_lt_of_ge hrecA hbad
  clear hharmonic
  let Y := A'.filter fun n =>
    n ≠ 0 ∧ ¬ (((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ (3 / 2) * log (log N))
  let X := A'.filter fun n =>
    ¬ ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ ((d : ℝ) ≤ log N ^ ((1 : ℝ) / 1000))
  have hA'Icc : A' ⊆ Icc ⌈(N : ℝ) ^ ε⌉₊ N := by
    intro n hn
    rw [mem_Icc]
    rw [mem_filter] at hn
    have hn' := hAN hn.1
    rw [mem_Icc] at hn'
    refine ⟨?_, hn'.2⟩
    rw [Nat.ceil_le]
    exact hn.2
  have hrecX : (rec_sum X : ℝ) ≤ C₁ * ε' * log N := by
    rw [rec_sum]
    push_cast
    rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div, ← mul_div_assoc]
    refine le_trans ?_ (hdivth N hdivth')
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.filter_subset_filter _ hA'Icc
      · intro n hn1 hn2
        exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hε₁ : ε' ≤ ε := by
    have hmul := mul_le_mul_of_nonneg_right h1log3N (inv_nonneg.mpr h0loglogN.le)
    simpa [ε', ε, div_eq_mul_inv, one_mul] using hmul
  have hrecX' : (rec_sum X : ℝ) ≤ C₁ * ε * log N := by
    refine le_trans hrecX ?_
    have hmulε : ε' * log N ≤ ε * log N := mul_le_mul_of_nonneg_right hε₁ h0logN.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hmulε h0C₁.le
  have hrecY : (rec_sum Y : ℝ) ≤ C₂ * ε' * log N := by
    rw [rec_sum]
    push_cast
    rw [mul_assoc, mul_comm ε', ← div_eq_mul_one_div, ← mul_div_assoc]
    refine le_trans ?_ (hregth N hregth')
    · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
      · exact Finset.filter_subset_filter _ hA'Icc
      · intro n hn1 hn2
        exact one_div_nonneg.mpr (Nat.cast_nonneg n)
  have hrecY' : (rec_sum Y : ℝ) ≤ C₂ * ε * log N := by
    refine le_trans hrecY ?_
    have hmulε : ε' * log N ≤ ε * log N := mul_le_mul_of_nonneg_right hε₁ h0logN.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using mul_le_mul_of_nonneg_left hmulε h0C₂.le
  let A'' := A' \ (X ∪ Y)
  have hrecA'' : (2 + 2 * C₃) * ε * log N ≤ rec_sum A'' := by
    refine le_trans ?_ rec_sum_sdiff
    rw [le_sub_iff_add_le]
    have hXY : (rec_sum (X ∪ Y) : ℝ) ≤ (C₁ + C₂) * ε * log N := by
      refine le_trans rec_sum_union ?_
      linarith
    linarith
  let δ : ℝ := 1 - 1 / log (log N)
  have h0δ : 0 < δ := by
    have htmp : 1 / log (log N) < 1 := by
      simpa [one_div] using (one_div_lt_one_div h0loglogN zero_lt_one).2 h1loglogN
    linarith
  have hδ1 : δ ≤ 1 := by
    refine sub_le_self _ ?_
    rw [one_div_nonneg]
    exact le_of_lt h0loglogN
  let Nf := fun i : ℕ => (N : ℝ) ^ (δ ^ i)
  let Af := fun i : ℕ => Ioc ⌊Nf (i + 1)⌋₊ ⌊Nf i⌋₊ ∩ A''
  let Nf' := fun i : ℕ => ⌊Nf i⌋₊
  let ε'' : ℝ := 1 / (log (log N)) ^ 2
  have hgoodi : ∃ i : ℕ, 2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N ≤ rec_sum (Af i) := by
    by_contra h
    let I := range (⌈log (1 / ε) * (2 * log (log N))⌉₊)
    have hIA : A'' = I.biUnion (fun i => Af i) := by
      rw [← Finset.biUnion_inter]
      refine Eq.symm ?_
      rw [Finset.inter_eq_right]
      intro n hn
      have hcover := bUnion_range_Ioc ⌈log (1 / ε) * (2 * log (log N))⌉₊ Nf'
      refine hcover ?_
      rw [mem_Ioc]
      rw [Finset.mem_sdiff, Finset.mem_filter] at hn
      refine ⟨?_, ?_⟩
      · rw [Nat.floor_lt]
        · refine lt_of_lt_of_le ?_ hn.1.2
          refine Real.rpow_lt_rpow_of_exponent_lt ?_ ?_
          · exact_mod_cast hN
          · have hceil :
                δ ^ ⌈log (1 / ε) * (2 * log (log N))⌉₊ ≤
                  δ ^ (log (1 / ε) * (2 * log (log N))) := by
              rw [← Real.rpow_natCast]
              refine Real.rpow_le_rpow_of_exponent_ge h0δ hδ1 ?_
              exact Nat.le_ceil _
            refine lt_of_le_of_lt hceil ?_
            have h1divε : 1 < 1 / ε := by
              rw [lt_div_iff₀ h0ε]
              simpa using hε1
            have hlogδ : log δ ≤ -(1 / log (log N)) := by
              have htmp := Real.log_le_sub_one_of_pos h0δ
              simpa [δ, sub_eq_add_neg, add_assoc, add_left_comm, add_comm] using htmp
            have hmul :
                (log (1 / ε) * (2 * log (log N))) * log δ ≤ -2 * log (1 / ε) := by
              have hfac_nonneg : 0 ≤ log (1 / ε) * (2 * log (log N)) := by
                exact mul_nonneg (le_of_lt (Real.log_pos h1divε)) (by positivity)
              calc
                (log (1 / ε) * (2 * log (log N))) * log δ
                    ≤ (log (1 / ε) * (2 * log (log N))) * (-(1 / log (log N))) := by
                      exact mul_le_mul_of_nonneg_left hlogδ hfac_nonneg
                _ = -2 * log (1 / ε) := by
                  have hL : log (log N) ≠ 0 := h0loglogN.ne'
                  field_simp [hL]
            calc
              δ ^ (log (1 / ε) * (2 * log (log N)))
                  = Real.exp ((log (1 / ε) * (2 * log (log N))) * log δ) := by
                    rw [Real.rpow_def_of_pos h0δ, mul_comm]
              _ ≤ Real.exp (-2 * log (1 / ε)) := by
                    gcongr
              _ < Real.exp (-(log (1 / ε))) := by
                    refine Real.exp_lt_exp.mpr ?_
                    have hpos : 0 < log (1 / ε) := Real.log_pos h1divε
                    linarith
              _ = ε := by
                    rw [show -(log (1 / ε)) = log ε by
                      rw [← Real.log_inv, one_div, inv_inv]]
                    rw [Real.exp_log h0ε]
        · exact Real.rpow_nonneg (Nat.cast_nonneg N) _
      · have hnntemp := hAN hn.1.1
        rw [mem_Icc] at hnntemp
        have htemp : Nf' 0 = N := by
          dsimp [Nf', Nf]
          rw [pow_zero, Real.rpow_one, Nat.floor_natCast]
        rw [htemp]
        exact hnntemp.2
    rw [not_exists] at h
    rw [← not_lt] at hrecA''
    refine hrecA'' ?_
    rw [hIA]
    have hUnion :
        (rec_sum (I.biUnion fun i => Af i) : ℝ) ≤
          Finset.sum I (fun i => (rec_sum (Af i) : ℝ)) := by
      simpa using (rec_sum_bUnion (I := I) (f := Af))
    refine lt_of_le_of_lt hUnion ?_
    have hsum_card :
        Finset.sum I (fun i => (rec_sum (Af i) : ℝ)) ≤
          I.card • (2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N) := by
      refine Finset.sum_le_card_nsmul I (fun i => (rec_sum (Af i) : ℝ))
        (2 * (log N) ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N) ?_
      intro x hx
      specialize h x
      rw [not_le] at h
      exact le_of_lt h
    refine lt_of_le_of_lt hsum_card ?_
    rw [Finset.card_range, one_div_div, nsmul_eq_mul]
    exact hlargeN₄.2
  rcases hgoodi with ⟨i, hi⟩
  let A₀ := Af i
  let N₀ := ⌊Nf i⌋₊
  have hNN₀ : (N : ℝ) ^ ε ≤ N₀ := by
    by_contra h
    have hA0empty : Af i = ∅ := by
      rw [Finset.eq_empty_iff_forall_notMem]
      intro n hn
      rw [Finset.mem_inter, Finset.mem_sdiff, Finset.mem_filter, Finset.mem_Ioc] at hn
      have hn_le : (n : ℝ) ≤ N₀ := by exact_mod_cast hn.1.2
      exact h (le_trans hn.2.1.2 hn_le)
    rw [hA0empty, ← not_lt, rec_sum_empty] at hi
    have : 0 < 2 * log N ^ ((1 : ℝ) / 500) + C₃ * ε'' * log N := by
      refine add_pos ?_ ?_
      · refine mul_pos ?_ ?_
        · norm_num
        · exact Real.rpow_pos_of_pos h0logN _
      · refine mul_pos ?_ h0logN
        refine mul_pos h0C₃ ?_
        rw [one_div_pos]
        exact sq_pos_of_pos h0loglogN
    linarith
  have h1N₀' : 1 ≤ Nf i := by
    refine one_le_rpow ?_ ?_
    · exact_mod_cast le_of_lt hN
    · exact pow_nonneg h0δ.le _
  have h1N₀ : 1 ≤ N₀ := by
    rw [← Nat.cast_le (α := ℝ)]
    refine le_trans ?_ hNN₀
    exact_mod_cast le_of_lt hlargeN₂
  have hN₀large₂ : 0 < log N₀ := by
    refine Real.log_pos ?_
    refine lt_of_lt_of_le ?_ hNN₀
    exact hlargeN₂
  have hN₀large : 1 ≤ log (log N₀) := by
    rw [← Real.exp_le_exp, Real.exp_log, ← Real.exp_le_exp, Real.exp_log]
    · refine le_trans ?_ hNN₀
      exact hlargeN₃
    · exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀
    · exact hN₀large₂
  have hN₀N : (N₀ : ℝ) ≤ N := by
    rw [← Real.rpow_one N]
    refine le_trans (Nat.floor_le (by positivity)) ?_
    refine Real.rpow_le_rpow_of_exponent_le ?_ ?_
    · exact_mod_cast le_of_lt hN
    · exact pow_le_one₀ h0δ.le hδ1
  have hlogNN₀' : (3 / 2 : ℝ) * log (log N) ≤ 2 * log (log N₀) := by
    have hstep : (log N) ^ (3 / 4 : ℝ) ≤ log N₀ := by
      have hNpos : (0 : ℝ) < N := by exact_mod_cast lt_trans zero_lt_one hN
      have hpow_pos : 0 < (N : ℝ) ^ ε := Real.rpow_pos_of_pos hNpos _
      have hlogpow_le : log ((N : ℝ) ^ ε) ≤ log N₀ := Real.log_le_log hpow_pos hNN₀
      have hlogpow_eq : log ((N : ℝ) ^ ε) = ε * log N := by
        rw [Real.log_rpow hNpos]
      calc
        (log N) ^ (3 / 4 : ℝ) ≤ log N * ε := by
          simpa [ε, mul_comm, mul_left_comm, mul_assoc] using hlargeN₄.1
        _ = log ((N : ℝ) ^ ε) := by rw [hlogpow_eq, mul_comm]
        _ ≤ log N₀ := hlogpow_le
    have haux : (3 / 4 : ℝ) * log (log N) ≤ log (log N₀) := by
      have hlog_step : log ((log N) ^ (3 / 4 : ℝ)) ≤ log (log N₀) := by
        exact Real.log_le_log (Real.rpow_pos_of_pos h0logN _) hstep
      simpa [Real.log_rpow h0logN, mul_comm] using hlog_step
    nlinarith
  have hlogNN₀ : log N ≤ (log N₀) ^ (2 : ℝ) := by
    have htmp : log (log N) ≤ (3 / 2 : ℝ) * log (log N) := by
      have hmul := mul_le_mul_of_nonneg_right (show (1 : ℝ) ≤ 3 / 2 by norm_num) h0loglogN.le
      simpa using hmul
    have hlog_eq : log ((log N₀) ^ (2 : ℝ)) = 2 * log (log N₀) := by
      rw [Real.log_rpow hN₀large₂]
    have hlog : log (log N) ≤ log ((log N₀) ^ (2 : ℝ)) := by
      rw [hlog_eq]
      exact le_trans htmp hlogNN₀'
    have hpow_pos : 0 < (log N₀) ^ (2 : ℝ) := by positivity
    exact (Real.log_le_log_iff h0logN hpow_pos).mp hlog
  let M := (N₀ : ℝ) ^ ((1 : ℝ) - 8 / log (log N₀))
  let Z := A₀.filter fun n => ∃ q : ℕ, IsPrimePow q ∧ M < q ∧ q ∣ n
  let A₁ := A₀ \ Z
  have hloc : log N₀ / (log (log N₀)) ^ 2 ≤ ε'' * log N := by
    rw [mul_comm, ← div_eq_mul_one_div]
    refine hinc N₀ N ⟨?_, ?_⟩
    · exact le_trans hincth hNN₀
    · exact_mod_cast hN₀N
  have hA₀large : ∀ n ∈ A₀, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n := by
    intro n hn
    have hmem : n ∈ Ioc ⌊Nf (i + 1)⌋₊ ⌊Nf i⌋₊ := (Finset.mem_inter.mp hn).1
    have hmem' := Finset.mem_Ioc.mp hmem
    have hmem_lt : Nf (i + 1) < n := by
      exact (Nat.floor_lt (by positivity)).1 hmem'.1
    refine le_trans ?_ (le_of_lt hmem_lt)
    transitivity (Nf i) ^ (1 - (1 : ℝ) / log (log N₀))
    · refine Real.rpow_le_rpow ?_ ?_ ?_
      · exact_mod_cast le_trans zero_le_one h1N₀
      · exact Nat.floor_le (by positivity)
      · have hdiv : (1 : ℝ) / log (log N₀) ≤ 1 := by
          have := one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hN₀large
          simpa using this
        exact sub_nonneg.mpr hdiv
    · have hNfsucc : Nf (i + 1) = (Nf i) ^ δ := by
        dsimp [Nf]
        rw [pow_succ', ← Real.rpow_mul (show 0 ≤ (N : ℝ) by exact_mod_cast Nat.zero_le N)]
        rw [mul_comm]
      rw [hNfsucc]
      refine Real.rpow_le_rpow_of_exponent_le h1N₀' ?_
      rw [sub_le_sub_iff_left]
      have hll : log (log N₀) ≤ log (log N) := by
        exact Real.log_le_log hN₀large₂
          (Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N)
      exact one_div_le_one_div_of_le (lt_of_lt_of_le zero_lt_one hN₀large) hll
  have hA₁large : ∀ n ∈ A₁, (N₀ : ℝ) ^ (1 - (1 : ℝ) / log (log N₀)) ≤ n := by
    intro n hn
    exact hA₀large n (Finset.mem_sdiff.mp hn).1
  have hA₀' : A₀ ⊆ Icc ⌈(N₀ : ℝ) ^ (1 - 1 / log (log N₀))⌉₊ N₀ := by
    intro n hn
    rw [mem_Icc]
    have hn' := hn
    rw [mem_inter, mem_Ioc] at hn
    refine ⟨?_, hn.1.2⟩
    rw [Nat.ceil_le]
    exact hA₀large n hn'
  have hrecZ : (rec_sum Z : ℝ) ≤ C₃ * ε'' * log N := by
    rw [rec_sum]
    push_cast
    transitivity C₃ * log N₀ / (log (log N₀)) ^ 2
    · refine le_trans ?_ (hsmoothth N₀ ?_)
      · refine Finset.sum_le_sum_of_subset_of_nonneg ?_ ?_
        · exact Finset.filter_subset_filter _ hA₀'
        · intro n hn1 hn2
          exact one_div_nonneg.mpr (Nat.cast_nonneg n)
      · have hC₃' : C₃' ≤ N₀ := by
          rw [← Nat.cast_le (α := ℝ)]
          exact le_trans hsmoothth' hNN₀
        exact hC₃'
    · rw [mul_assoc, mul_div_assoc]
      exact mul_le_mul_of_nonneg_left hloc h0C₃.le
  have hrecA₁ : 2 * (log N₀) ^ ((1 : ℝ) / 500) ≤ rec_sum A₁ := by
    transitivity 2 * (log N) ^ ((1 : ℝ) / 500)
    · have hpow : (log N₀) ^ ((1 : ℝ) / 500) ≤ (log N) ^ ((1 : ℝ) / 500) := by
        refine Real.rpow_le_rpow ?_ ?_ ?_
        · exact Real.log_nonneg (by exact_mod_cast h1N₀)
        · exact Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N
        · norm_num1
      have hmul := mul_le_mul_of_nonneg_left hpow (show (0 : ℝ) ≤ 2 by norm_num)
      simpa [mul_comm, mul_left_comm, mul_assoc] using hmul
    · refine le_trans ?_ rec_sum_sdiff
      rw [le_sub_iff_add_le]
      refine le_trans ?_ hi
      rw [add_le_add_iff_left]
      exact hrecZ
  have hN₀ : C₀ ≤ N₀ := by
    rw [← Nat.cast_le (α := ℝ)]
    exact le_trans hlargeN hNN₀
  have hA₁N₀ : A₁ ⊆ range (N₀ + 1) := by
    intro n hn
    rw [mem_range, Nat.lt_succ_iff]
    have hn' : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    exact (Finset.mem_Ioc.mp (Finset.mem_inter.mp hn').1).2
  have hA₁div : ∀ n ∈ A₁, ∃ p : ℕ, p ∣ n ∧ 4 ≤ p ∧ (p : ℝ) ≤ log N₀ ^ (1 / 500 : ℝ) := by
    intro n hn
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
    have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
    have hn_not_union : n ∉ X ∪ Y := (Finset.mem_sdiff.mp hnA'').2
    have hn_notX : n ∉ X := fun hx => hn_not_union (Finset.mem_union.mpr (Or.inl hx))
    have hxdiv : ∃ d : ℕ, d ∣ n ∧ 4 ≤ d ∧ (d : ℝ) ≤ log N ^ ((1 : ℝ) / 1000) := by
      by_contra hxdiv
      exact hn_notX (by
        rw [mem_filter]
        exact ⟨hnA', hxdiv⟩)
    rcases hxdiv with ⟨d, hd₁, hd₂, hd₃⟩
    refine ⟨d, hd₁, hd₂, le_trans hd₃ ?_⟩
    calc
      log N ^ ((1 : ℝ) / 1000) ≤ ((log N₀) ^ (2 : ℝ)) ^ ((1 : ℝ) / 1000) := by
        exact Real.rpow_le_rpow h0logN.le hlogNN₀ (by norm_num)
      _ = log N₀ ^ ((1 : ℝ) / 500) := by
        rw [← Real.rpow_mul hN₀large₂.le]
        norm_num
  have hA₁smooth : ∀ n ∈ A₁, is_smooth M n := by
    intro n hn
    rw [is_smooth]
    intro q hq₁ hq₂
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hn_notZ : n ∉ Z := (Finset.mem_sdiff.mp hn).2
    rw [← not_lt]
    intro hbad
    exact hn_notZ (by
      rw [mem_filter]
      exact ⟨hnA₀, ⟨q, hq₁, hbad, hq₂⟩⟩)
  have hA₁reg : arith_regular N₀ A₁ := by
    rw [arith_regular]
    intro n hn
    have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hn).1
    have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
    have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
    have hn_not_union : n ∉ X ∪ Y := (Finset.mem_sdiff.mp hnA'').2
    have hn_notY : n ∉ Y := fun hy => hn_not_union (Finset.mem_union.mpr (Or.inr hy))
    have hn_nonzero : n ≠ 0 := by
      have htemp' := hAN (Finset.mem_filter.mp hnA').1
      rw [mem_Icc] at htemp'
      exact Nat.ne_of_gt htemp'.1
    have hn_regN :
        ((99 : ℝ) / 100) * log (log N) ≤ ω n ∧ (ω n : ℝ) ≤ (3 / 2) * log (log N) := by
      by_contra hbad
      exact hn_notY (by
        rw [mem_filter]
        exact ⟨hnA', hn_nonzero, hbad⟩)
    refine ⟨?_, ?_⟩
    · have hll : log (log N₀) ≤ log (log N) := by
        exact Real.log_le_log hN₀large₂
          (Real.log_le_log (by exact_mod_cast lt_of_lt_of_le zero_lt_one h1N₀) hN₀N)
      exact le_trans (mul_le_mul_of_nonneg_left hll (by norm_num)) hn_regN.1
    · exact le_trans hn_regN.2 hlogNN₀'
  specialize hcor N₀ hN₀ A₁ hA₁N₀ hA₁large hrecA₁ hA₁div hA₁smooth hA₁reg
  rcases hcor with ⟨S, hS₁, hS₂⟩
  refine ⟨S, ?_, hS₂⟩
  intro n hn
  have hnA₁ : n ∈ A₁ := hS₁ hn
  have hnA₀ : n ∈ A₀ := (Finset.mem_sdiff.mp hnA₁).1
  have hnA'' : n ∈ A'' := (Finset.mem_inter.mp hnA₀).2
  have hnA' : n ∈ A' := (Finset.mem_sdiff.mp hnA'').1
  exact (Finset.mem_filter.mp hnA').1

theorem erdos47_bloom :
    ∃ C : ℝ, 0 < C ∧ ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  rcases unit_fractions_upper_log_density with ⟨C, h0C, hC⟩
  obtain ⟨N₀, hN₀⟩ := Filter.eventually_atTop.mp hC
  refine ⟨C, h0C, N₀, ?_⟩
  intro N hN A hA hrec
  exact hN₀ N hN A hA (le_of_lt hrec)

theorem erdos47 :
    ∀ δ > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ A : Finset ℕ,
      A ⊆ Finset.Icc 1 N →
      δ * log N < rec_sum A →
      ∃ S ⊆ A, rec_sum S = 1 := by
  intro δ hδ
  rcases erdos47_bloom with ⟨C, hC, N₁, hBloom⟩
  have hδC : 0 < δ / C := div_pos hδ hC
  have haux := Real.isLittleO_log_id_atTop.bound hδC
  have hcompare :
      ∀ᶠ N : ℕ in atTop,
        C * ((log (log (log (N : ℝ))) / log (log (N : ℝ))) * log (N : ℝ)) ≤
          δ * log (N : ℝ) := by
    filter_upwards
      [ tendsto_log_log_coe_at_top.eventually haux
      , tendsto_log_coe_at_top.eventually (eventually_gt_atTop (0 : ℝ))
      , tendsto_log_log_coe_at_top (eventually_gt_atTop (1 : ℝ)) ] with
      N hsmall h0logN h1loglogN
    have h0loglogN : 0 < log (log (N : ℝ)) := lt_trans zero_lt_one h1loglogN
    have h0logloglogN : 0 < log (log (log (N : ℝ))) := Real.log_pos h1loglogN
    have hsmall' : log (log (log (N : ℝ))) ≤ (δ / C) * log (log (N : ℝ)) := by
      have hsmallAbs :
          |log (log (log (N : ℝ)))| ≤ (δ / C) * |log (log (N : ℝ))| := by
        simpa [Function.comp, Real.norm_eq_abs] using hsmall
      rwa [abs_of_pos h0logloglogN, abs_of_pos h0loglogN] at hsmallAbs
    have hdiv : log (log (log (N : ℝ))) / log (log (N : ℝ)) ≤ δ / C := by
      exact (_root_.div_le_iff₀ h0loglogN).2 hsmall'
    have hcoeff :
        C * (log (log (log (N : ℝ))) / log (log (N : ℝ))) ≤ δ := by
      have hmul :
          C * (log (log (log (N : ℝ))) / log (log (N : ℝ))) ≤ δ * (C * C⁻¹) := by
        simpa [div_eq_mul_inv, mul_assoc, mul_left_comm, mul_comm] using
          mul_le_mul_of_nonneg_left hdiv hC.le
      calc
        C * (log (log (log (N : ℝ))) / log (log (N : ℝ))) ≤ δ * (C * C⁻¹) := hmul
        _ = δ := by rw [mul_inv_cancel₀ hC.ne', mul_one]
    have hmain := mul_le_mul_of_nonneg_right hcoeff h0logN.le
    simpa [mul_assoc, mul_left_comm, mul_comm] using hmain
  rw [Filter.eventually_atTop] at hcompare
  rcases hcompare with ⟨N₂, hN₂⟩
  refine ⟨max N₁ N₂, ?_⟩
  intro N hN A hA hsum
  have hN₁' : N₁ ≤ N := le_trans (Nat.le_max_left _ _) hN
  have hN₂' : N₂ ≤ N := le_trans (Nat.le_max_right _ _) hN
  refine hBloom N hN₁' A hA ?_
  exact lt_of_le_of_lt (hN₂ N hN₂') hsum

#print axioms erdos47_bloom
#print axioms erdos47

end Erdos47
