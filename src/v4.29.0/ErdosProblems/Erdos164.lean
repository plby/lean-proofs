import Mathlib

open scoped Topology

noncomputable section

namespace Erdos164

noncomputable def baseFlow (N M : ℕ) : ℝ :=
  if 1 < N then
    if M ∣ N then
      let q := N / M
      if IsPrimePow q then
        ArithmeticFunction.vonMangoldt q / ((N : ℝ) * (Real.log N) ^ 2)
      else
        0
    else
      0
  else
    0

noncomputable def modifiedFlow (N M : ℕ) : ℝ :=
  by
    classical
    exact
      if ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ M = 1 then
        0
      else if ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ M = p ^ (k - 1) then
        baseFlow N M + baseFlow N 1
      else
        baseFlow N M

noncomputable def outflow (W : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' M : ℕ, W N M

noncomputable def inflow (W : ℕ → ℕ → ℝ) (N : ℕ) : ℝ :=
  ∑' K : ℕ, W K N

noncomputable def erdosWeight (n : ℕ) : ℝ :=
  1 / ((n : ℝ) * Real.log n)

theorem outflow_modifiedFlow_eq_erdosWeight {N : ℕ} (hN : 1 < N) :
    outflow modifiedFlow N = erdosWeight N := by
  classical
  have hN0_nat : N ≠ 0 := by
    exact ne_of_gt (lt_trans Nat.zero_lt_one hN)
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0_nat
  have hN_cast : (1 : ℝ) < N := by
    exact_mod_cast hN
  have hlog_pos : 0 < Real.log N := Real.log_pos hN_cast
  have hlog_ne : Real.log N ≠ 0 := hlog_pos.ne'
  have hsupport_modified : ∀ M ∉ N.divisors, modifiedFlow N M = 0 := by
    intro M hM
    have hnotdvd : ¬ M ∣ N := by
      intro hMN
      exact hM (Nat.mem_divisors.mpr ⟨hMN, hN0_nat⟩)
    have hspecial :
        ¬ ∃ p : ℕ, p.Prime ∧ ∃ k : ℕ, 2 ≤ k ∧ N = p ^ k ∧ M = p ^ (k - 1) := by
      rintro ⟨p, hp, k, hk, hNk, hMk⟩
      apply hnotdvd
      rw [hNk, hMk]
      exact pow_dvd_pow p (Nat.sub_le _ _)
    simp [modifiedFlow, baseFlow, hN, hnotdvd, hspecial]
  have hsupport_base : ∀ M ∉ N.divisors, baseFlow N M = 0 := by
    intro M hM
    have hnotdvd : ¬ M ∣ N := by
      intro hMN
      exact hM (Nat.mem_divisors.mpr ⟨hMN, hN0_nat⟩)
    simp [baseFlow, hN, hnotdvd]
  have hrow :
      ∑ M ∈ N.divisors, modifiedFlow N M = ∑ M ∈ N.divisors, baseFlow N M := by
    by_cases hpp : ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k
    · rcases hpp with ⟨p, k, hp, hk, rfl⟩
      let s : Finset ℕ := (p ^ k).divisors
      have hk0 : k ≠ 0 := by omega
      have hpow_ne_zero : p ^ k ≠ 0 := pow_ne_zero k hp.ne_zero
      have h1mem : 1 ∈ s := by
        exact Nat.one_mem_divisors.2 hpow_ne_zero
      have hprev_mem : p ^ (k - 1) ∈ s := by
        refine Nat.mem_divisors.mpr ⟨pow_dvd_pow p (Nat.sub_le _ _), hpow_ne_zero⟩
      have hprev_ne_one : p ^ (k - 1) ≠ 1 := by
        have hk1 : k - 1 ≠ 0 := by omega
        exact (one_lt_pow' hp.one_lt hk1).ne'
      have hprev_mem' : p ^ (k - 1) ∈ s.erase 1 := by
        exact Finset.mem_erase.mpr ⟨hprev_ne_one, hprev_mem⟩
      have hfirst_iff (M : ℕ) :
          (∃ p' k' : ℕ, p'.Prime ∧ 2 ≤ k' ∧ p ^ k = p' ^ k' ∧ M = 1) ↔ M = 1 := by
        constructor
        · rintro ⟨p', k', hp', hk', hpow, hM⟩
          exact hM
        · intro hM
          exact ⟨p, k, hp, hk, rfl, hM⟩
      have hsecond_iff (M : ℕ) :
          (∃ p' k' : ℕ, p'.Prime ∧ 2 ≤ k' ∧ p ^ k = p' ^ k' ∧ M = p' ^ (k' - 1)) ↔
            M = p ^ (k - 1) := by
        constructor
        · rintro ⟨p', k', hp', hk', hpow, hM⟩
          have hk'0 : k' ≠ 0 := by omega
          rcases hp.pow_inj' hp' hk0 hk'0 hpow with ⟨rfl, rfl⟩
          exact hM
        · intro hM
          exact ⟨p, k, hp, hk, rfl, hM⟩
      have hrest :
          ∀ M ∈ (s.erase 1).erase (p ^ (k - 1)),
            modifiedFlow (p ^ k) M = baseFlow (p ^ k) M := by
        intro M hM
        have hMprev : M ≠ p ^ (k - 1) := (Finset.mem_erase.mp hM).1
        have hM1 : M ≠ 1 := (Finset.mem_erase.mp (Finset.mem_of_mem_erase hM)).1
        rw [modifiedFlow]
        split_ifs with hfirst hsecond
        · exact (hM1 ((hfirst_iff M).1 hfirst)).elim
        · exact (hMprev ((hsecond_iff M).1 hsecond)).elim
        · rfl
      have h_at_one : modifiedFlow (p ^ k) 1 = 0 := by
        rw [modifiedFlow]
        split_ifs with hfirst hsecond
        · rfl
        · have hEq : 1 = p ^ (k - 1) := (hsecond_iff 1).1 hsecond
          exact (hprev_ne_one hEq.symm).elim
        · exact (hfirst ⟨p, k, hp, hk, rfl, rfl⟩).elim
      have h_at_prev :
          modifiedFlow (p ^ k) (p ^ (k - 1)) =
            baseFlow (p ^ k) (p ^ (k - 1)) + baseFlow (p ^ k) 1 := by
        rw [modifiedFlow]
        split_ifs with hfirst hsecond
        · exact (hprev_ne_one ((hfirst_iff (p ^ (k - 1))).1 hfirst)).elim
        · rfl
        · exact (hsecond ⟨p, k, hp, hk, rfl, rfl⟩).elim
      have hsplit_modified₁ :
          ∑ M ∈ s, modifiedFlow (p ^ k) M =
            (∑ M ∈ s.erase 1, modifiedFlow (p ^ k) M) + modifiedFlow (p ^ k) 1 := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_sum_diff_singleton_add (f := fun M => modifiedFlow (p ^ k) M) h1mem)
      have hsplit_modified₂ :
          ∑ M ∈ s.erase 1, modifiedFlow (p ^ k) M =
            (∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), modifiedFlow (p ^ k) M) +
              modifiedFlow (p ^ k) (p ^ (k - 1)) := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_sum_diff_singleton_add
            (s := s.erase 1) (f := fun M => modifiedFlow (p ^ k) M) hprev_mem')
      have hsplit_base₁ :
          ∑ M ∈ s, baseFlow (p ^ k) M =
            (∑ M ∈ s.erase 1, baseFlow (p ^ k) M) + baseFlow (p ^ k) 1 := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_sum_diff_singleton_add (f := fun M => baseFlow (p ^ k) M) h1mem)
      have hsplit_base₂ :
          ∑ M ∈ s.erase 1, baseFlow (p ^ k) M =
            (∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), baseFlow (p ^ k) M) +
              baseFlow (p ^ k) (p ^ (k - 1)) := by
        simpa [Finset.sdiff_singleton_eq_erase] using
          (Finset.sum_eq_sum_diff_singleton_add
            (s := s.erase 1) (f := fun M => baseFlow (p ^ k) M) hprev_mem')
      have hrest_sum :
          ∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), modifiedFlow (p ^ k) M =
            ∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), baseFlow (p ^ k) M := by
        apply Finset.sum_congr rfl
        intro M hM
        exact hrest M hM
      calc
        ∑ M ∈ s, modifiedFlow (p ^ k) M
            = (∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), modifiedFlow (p ^ k) M) +
                modifiedFlow (p ^ k) (p ^ (k - 1)) + modifiedFlow (p ^ k) 1 := by
                  rw [hsplit_modified₁, hsplit_modified₂]
        _ = (∑ M ∈ (s.erase 1).erase (p ^ (k - 1)), baseFlow (p ^ k) M) +
                baseFlow (p ^ k) (p ^ (k - 1)) + baseFlow (p ^ k) 1 := by
                  rw [hrest_sum, h_at_prev, h_at_one]
                  ring
        _ = ∑ M ∈ s, baseFlow (p ^ k) M := by
              symm
              rw [hsplit_base₁, hsplit_base₂]
    · apply Finset.sum_congr rfl
      intro M hM
      rw [modifiedFlow]
      split_ifs with hfirst hsecond
      · rcases hfirst with ⟨p, k, hp, hk, hNk, hM1⟩
        exact (hpp ⟨p, k, hp, hk, hNk⟩).elim
      · rcases hsecond with ⟨p, k, hp, hk, hNk, hMp⟩
        exact (hpp ⟨p, k, hp, hk, hNk⟩).elim
      · rfl
  have hbase :
      outflow baseFlow N =
        (∑ d ∈ N.divisors, ArithmeticFunction.vonMangoldt d) /
          ((N : ℝ) * (Real.log N) ^ 2) := by
    rw [outflow, tsum_eq_sum (s := N.divisors) hsupport_base]
    calc
      ∑ M ∈ N.divisors, baseFlow N M
          = ∑ M ∈ N.divisors,
              ArithmeticFunction.vonMangoldt (N / M) / ((N : ℝ) * (Real.log N) ^ 2) := by
                apply Finset.sum_congr rfl
                intro M hM
                have hMN : M ∣ N := Nat.dvd_of_mem_divisors hM
                by_cases hprimepow : IsPrimePow (N / M)
                · simp [baseFlow, hN, hMN, hprimepow]
                · have hvm : ArithmeticFunction.vonMangoldt (N / M) = 0 := by
                    rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
                    exact hprimepow
                  simp [baseFlow, hN, hMN, hprimepow, hvm]
      _ = ∑ d ∈ N.divisors,
            ArithmeticFunction.vonMangoldt d / ((N : ℝ) * (Real.log N) ^ 2) := by
              simpa using
                (Nat.sum_div_divisors N
                  (fun d : ℕ => ArithmeticFunction.vonMangoldt d / ((N : ℝ) * (Real.log N) ^ 2)))
      _ = (∑ d ∈ N.divisors, ArithmeticFunction.vonMangoldt d) /
            ((N : ℝ) * (Real.log N) ^ 2) := by
              rw [Finset.sum_div]
  calc
    outflow modifiedFlow N = ∑ M ∈ N.divisors, modifiedFlow N M := by
      rw [outflow, tsum_eq_sum (s := N.divisors) hsupport_modified]
    _ = ∑ M ∈ N.divisors, baseFlow N M := hrow
    _ = outflow baseFlow N := by
      rw [outflow, tsum_eq_sum (s := N.divisors) hsupport_base]
    _ = (∑ d ∈ N.divisors, ArithmeticFunction.vonMangoldt d) /
          ((N : ℝ) * (Real.log N) ^ 2) := hbase
    _ = Real.log N / ((N : ℝ) * (Real.log N) ^ 2) := by
      rw [ArithmeticFunction.vonMangoldt_sum]
    _ = erdosWeight N := by
      rw [erdosWeight, pow_two]
      field_simp [hN0, hlog_ne]

noncomputable def analyticSeries (s : ℝ) : ℝ :=
  ∑' q : { q : ℕ // 2 ≤ q },
    ArithmeticFunction.vonMangoldt q / Real.rpow ((q : ℕ) : ℝ) s

noncomputable def zetaSeries (s : ℝ) : ℝ :=
  ∑' n : ℕ, 1 / Real.rpow (((n + 1 : ℕ) : ℝ)) s

lemma analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries {s : ℝ} (hs : 1 < s) :
    analyticSeries s = -deriv zetaSeries s / zetaSeries s := by
  have hs' : 1 < (s : ℂ).re := by
    simpa using hs
  let e : ℕ ≃ { q : ℕ // 2 ≤ q } :=
    { toFun := fun n => ⟨n + 2, by omega⟩
      invFun := fun q => q.1 - 2
      left_inv := by
        intro n
        simp
      right_inv := by
        rintro ⟨q, hq⟩
        apply Subtype.ext
        exact Nat.sub_add_cancel hq }
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      zetaSeries =ᶠ[𝓝 s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x}, (isOpen_lt continuous_const continuous_id).mem_nhds hs, ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_deriv : deriv zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  have hzeta_val : zetaSeries s = (LSeries 1 (s : ℂ)).re := by
    simpa using congrArg Complex.re (hzeta_complex hs)
  have hzeta_pos : 0 < zetaSeries s := by
    rw [hzeta_val, LSeries_one_eq_riemannZeta hs']
    exact riemannZeta_re_pos_of_one_lt hs
  have hzeta_ne : zetaSeries s ≠ 0 := hzeta_pos.ne'
  have hanalytic_complex :
      ((analyticSeries s : ℝ) : ℂ) =
        LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
    calc
      ((analyticSeries s : ℝ) : ℂ)
          = ∑' n : ℕ,
              ((ArithmeticFunction.vonMangoldt (n + 2 : ℕ) /
                Real.rpow (((n + 2 : ℕ) : ℝ)) s : ℝ) : ℂ) := by
                  rw [analyticSeries, Complex.ofReal_tsum,
                    ← e.tsum_eq
                      (fun q : { q : ℕ // 2 ≤ q } =>
                        (((ArithmeticFunction.vonMangoldt q : ℝ) /
                          Real.rpow ((q : ℕ) : ℝ) s : ℝ) : ℂ))]
                  simp [e]
      _ = ∑' n : ℕ,
            LSeries.term (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) (n + 2) := by
              refine tsum_congr fun n ↦ ?_
              have hn : (n + 2 : ℕ) ≠ 0 := by omega
              rw [LSeries.term_of_ne_zero hn]
              have hpow :
                  ((((n + 2 : ℕ) : ℝ) ^ s : ℝ) : ℂ) = (↑n + 2 : ℂ) ^ (s : ℂ) := by
                simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 2 : ℕ) : ℝ))) s)
              simpa using
                congrArg
                  (fun z : ℂ => (ArithmeticFunction.vonMangoldt (n + 2 : ℕ) : ℂ) / z) hpow
      _ = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
            symm
            rw [LSeries]
            have hsum :
                LSeriesSummable (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) := by
              simpa using ArithmeticFunction.LSeriesSummable_vonMangoldt hs'
            have htail := hsum.sum_add_tsum_nat_add 2
            have hinit :
                ∑ i ∈ Finset.range 2,
                  LSeries.term
                      (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) i = 0 := by
              rw [Finset.sum_range_succ, Finset.sum_range_one]
              simp [LSeries.term_def, ArithmeticFunction.vonMangoldt_apply_one]
            simpa [hinit] using htail.symm
  have hmain_complex :
      ((analyticSeries s : ℝ) : ℂ) =
        -deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ) := by
    calc
      ((analyticSeries s : ℝ) : ℂ)
          = LSeries (fun n : ℕ => (ArithmeticFunction.vonMangoldt n : ℂ)) (s : ℂ) :=
            hanalytic_complex
      _ = -deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ) := by
            simpa using ArithmeticFunction.LSeries_vonMangoldt_eq hs'
  have hmain_re :
      analyticSeries s = (-deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ)).re := by
    simpa using congrArg Complex.re hmain_complex
  have hquot :
      (-deriv (LSeries 1) (s : ℂ) / LSeries 1 (s : ℂ)).re =
        -deriv zetaSeries s / zetaSeries s := by
    rw [← hzeta_complex hs, Complex.div_re, Complex.normSq_ofReal, Complex.ofReal_re,
      Complex.ofReal_im, Complex.neg_re, hzeta_deriv, mul_zero, zero_div, add_zero]
    field_simp [hzeta_ne]
  exact hmain_re.trans hquot

lemma neg_deriv_zetaSeries_eq_tsum_log_nat_succ_div_rpow {s : ℝ} (hs : 1 < s) :
    -deriv zetaSeries s =
      ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
  have hzeta_complex {x : ℝ} (hx : 1 < x) :
      ((zetaSeries x : ℝ) : ℂ) = LSeries 1 (x : ℂ) := by
    have hx' : 1 < (x : ℂ).re := by
      simpa using hx
    calc
      ((zetaSeries x : ℝ) : ℂ)
          = ∑' n : ℕ, ((1 / Real.rpow (((n + 1 : ℕ) : ℝ)) x : ℝ) : ℂ) := by
              rw [zetaSeries, Complex.ofReal_tsum]
      _ = ∑' n : ℕ, 1 / (n + 1 : ℂ) ^ (x : ℂ) := by
            refine tsum_congr fun n ↦ ?_
            have hpow :
                ((((n + 1 : ℕ) : ℝ) ^ x : ℝ) : ℂ) = (↑n + 1 : ℂ) ^ (x : ℂ) := by
              simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) x)
            simpa using congrArg (fun z : ℂ => (1 : ℂ) / z) hpow
      _ = riemannZeta (x : ℂ) := by
            symm
            exact zeta_eq_tsum_one_div_nat_add_one_cpow hx'
      _ = LSeries 1 (x : ℂ) := by
            symm
            exact LSeries_one_eq_riemannZeta hx'
  have hzeta_event :
      zetaSeries =ᶠ[𝓝 s] fun x : ℝ => (LSeries 1 (x : ℂ)).re := by
    refine Filter.eventuallyEq_iff_exists_mem.mpr ?_
    refine ⟨{x : ℝ | 1 < x}, (isOpen_lt continuous_const continuous_id).mem_nhds hs, ?_⟩
    intro x hx
    simpa using congrArg Complex.re (hzeta_complex hx)
  have habs : LSeries.abscissaOfAbsConv 1 < (s : ℂ).re := by
    rw [LSeries.abscissaOfAbsConv_one, ← EReal.coe_one, EReal.coe_lt_coe_iff]
    simpa using hs
  have hL1_deriv :
      HasDerivAt (fun x : ℝ => (LSeries 1 (x : ℂ)).re) (deriv (LSeries 1) (s : ℂ)).re s := by
    simpa [LSeries_deriv habs] using (LSeries_hasDerivAt (f := 1) habs).real_of_complex
  have hzeta_deriv : deriv zetaSeries s = (deriv (LSeries 1) (s : ℂ)).re := by
    rw [Filter.EventuallyEq.deriv_eq hzeta_event]
    exact hL1_deriv.deriv
  let f : ℕ → ℝ := fun n => (LSeries.term (LSeries.logMul 1) (s : ℂ) n).re
  have hsum_re_eq :
      ∑' n : ℕ, f n = (LSeries (LSeries.logMul 1) (s : ℂ)).re := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).tsum_eq
  have hsum_re :
      Summable f := by
    exact
      (Complex.hasSum_re (Summable.hasSum (LSeriesSummable_logMul_of_lt_re (f := 1) habs))).summable
  have htail_eq :
      ∑' n : ℕ, f (n + 1) = ∑' n : ℕ, f n := by
    have htail := hsum_re.sum_add_tsum_nat_add 1
    simpa [f] using htail
  have hterm_re (n : ℕ) :
      (LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1)).re =
        Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
    have hpow :
        ((((n + 1 : ℕ) : ℂ) ^ (s : ℂ))) = ((((n + 1 : ℕ) : ℝ) ^ s : ℝ) : ℂ) := by
      simpa using (Complex.ofReal_cpow (by positivity : 0 ≤ (((n + 1 : ℕ) : ℝ))) s).symm
    have hterm :
        LSeries.term (LSeries.logMul 1) (s : ℂ) (n + 1) =
          (((Real.log (n + 1) / ((n + 1 : ℝ) ^ s) : ℝ) : ℂ)) := by
      rw [LSeries.term_of_ne_zero (show n + 1 ≠ 0 by omega), LSeries.logMul, hpow]
      have hlog : Complex.log (((n + 1 : ℕ) : ℂ)) = Real.log (n + 1) := by
        simpa using (Complex.natCast_log (n := n + 1)).symm
      rw [hlog]
      simp
    simpa using congrArg Complex.re hterm
  calc
    -deriv zetaSeries s = (-deriv (LSeries 1) (s : ℂ)).re := by
      rw [hzeta_deriv]
      simp
    _ = (LSeries (LSeries.logMul 1) (s : ℂ)).re := by
      rw [LSeries_deriv habs]
      simp
    _ = ∑' n : ℕ, f n := by
      symm
      exact hsum_re_eq
    _ = ∑' n : ℕ, f (n + 1) := by
      exact htail_eq.symm
    _ = ∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s) := by
      refine tsum_congr fun n ↦ ?_
      simpa [f] using hterm_re n

noncomputable def logMesh (m : ℕ) : ℝ :=
  Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))

lemma logMesh_nonneg (m : ℕ) : 0 ≤ logMesh m := by
  unfold logMesh
  apply Real.log_nonneg
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  rw [one_le_div hpos]
  norm_num

lemma log_nat_succ_eq_sum_logMesh (n : ℕ) :
    Real.log ((n : ℝ) + 1) = ∑ m ∈ Finset.range n, logMesh m := by
  unfold logMesh
  calc
    Real.log ((n : ℝ) + 1)
        = Real.log ((n : ℝ) + 1) - Real.log 1 := by simp
    _ = ∑ m ∈ Finset.range n,
          (Real.log (((m + 1 : ℕ) : ℝ) + 1) - Real.log ((m : ℝ) + 1)) := by
          simpa using
            (Finset.sum_range_sub
              (fun m : ℕ => Real.log ((m : ℝ) + 1)) n).symm
    _ = ∑ m ∈ Finset.range n,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          have h1 : 0 < (m : ℝ) + 1 := by positivity
          have h2 : 0 < (m : ℝ) + 2 := by positivity
          rw [Real.log_div h2.ne' h1.ne']
          norm_num [Nat.cast_add]
          ring_nf

lemma convexOn_rpow_of_lt_zero {p : ℝ} (hp : p < 0) :
    ConvexOn ℝ (Set.Ioi 0) (fun x : ℝ => x ^ p) := by
  refine (strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ)) ?_ ?_).convexOn
  · intro x hx
    exact (Real.continuousAt_rpow_const x p (Or.inl hx.ne')).continuousWithinAt
  · intro x hx
    rw [show (deriv^[2] (fun y : ℝ => y ^ p)) x = (deriv^[2] fun y : ℝ => y ^ p) x by rfl]
    rw [Real.iter_deriv_rpow_const p x 2]
    rw [descPochhammer_succ_eval, descPochhammer_succ_eval]
    have hcoeff : 0 < p * (p - 1) := by
      nlinarith
    have hpow : 0 < x ^ (p - 2) := Real.rpow_pos_of_pos hx _
    simpa using mul_pos hcoeff hpow

lemma rpow_neg_le_integral_centered {s : ℝ} (hs : 1 < s) {n : ℕ} (hn : 1 ≤ n) :
    ((n : ℝ) ^ (-s)) ≤
      ∫ x in (n : ℝ) - (1 / 2 : ℝ)..(n : ℝ) + (1 / 2 : ℝ), x ^ (-s) := by
  let a : ℝ := (n : ℝ) - (1 / 2 : ℝ)
  let b : ℝ := (n : ℝ) + (1 / 2 : ℝ)
  have hn_half : (1 / 2 : ℝ) < (n : ℝ) := by
    have hn' : (1 : ℝ) ≤ (n : ℝ) := by
      exact_mod_cast hn
    linarith
  have hab : a ≤ b := by
    dsimp [a, b]
    linarith
  have ha_pos : 0 < a := by
    dsimp [a]
    exact sub_pos.mpr hn_half
  have hab_lt : a < b := by
    dsimp [a, b]
    linarith
  have hconv :
      ConvexOn ℝ (Set.Icc a b) (fun x : ℝ => x ^ (-s)) := by
    refine ⟨convex_Icc a b, ?_⟩
    intro x hx y hy u v hu hv huv
    exact (convexOn_rpow_of_lt_zero (p := -s) (by linarith)).2
      (lt_of_lt_of_le ha_pos hx.1) (lt_of_lt_of_le ha_pos hy.1) hu hv huv
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-s)) (Set.Icc a b) := by
    intro x hx
    have hx_pos : 0 < x := lt_of_lt_of_le ha_pos hx.1
    exact (Real.continuousAt_rpow_const x (-s) (Or.inl hx_pos.ne')).continuousWithinAt
  have h0 : MeasureTheory.volume (Set.uIoc a b) ≠ 0 := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    have hlen : 0 < b - a := sub_pos.mpr hab_lt
    exact (ENNReal.ofReal_pos.mpr hlen).ne'
  have htop : MeasureTheory.volume (Set.uIoc a b) ≠ ⊤ := by
    rw [Set.uIoc_of_le hab, Real.volume_Ioc]
    exact (ENNReal.ofReal_ne_top : ENNReal.ofReal (b - a) ≠ ⊤)
  have huIoc_subset_Icc : Set.uIoc a b ⊆ Set.Icc a b := by
    intro x hx
    rw [Set.uIoc_of_le hab] at hx
    exact Set.mem_Icc_of_Ioc hx
  have hmem :
      ∀ᵐ x ∂MeasureTheory.volume.restrict (Set.uIoc a b), x ∈ Set.Icc a b := by
    rw [MeasureTheory.ae_restrict_iff' measurableSet_uIoc]
    filter_upwards with x hx
    exact huIoc_subset_Icc hx
  have hid_int : MeasureTheory.IntegrableOn (fun x : ℝ => x) (Set.uIoc a b)
      MeasureTheory.volume := by
    exact continuousOn_id.integrableOn_of_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc a b))
      measurableSet_uIoc huIoc_subset_Icc htop
  have hpow_int :
      MeasureTheory.IntegrableOn (fun x : ℝ => x ^ (-s)) (Set.uIoc a b) MeasureTheory.volume := by
    exact hcont.integrableOn_of_subset_isCompact (isCompact_Icc : IsCompact (Set.Icc a b))
      measurableSet_uIoc huIoc_subset_Icc htop
  have hJ :
      ((⨍ x in a..b, x) ^ (-s)) ≤ (⨍ x in a..b, x ^ (-s)) := by
    simpa [a, b] using
      (hconv.map_set_average_le hcont isClosed_Icc h0 htop hmem hid_int hpow_int)
  have havg_id : (⨍ x in a..b, x) = (n : ℝ) := by
    rw [interval_average_eq_div, integral_id]
    dsimp [a, b]
    ring_nf
  have havg_pow : (⨍ x in a..b, x ^ (-s)) = ∫ x in a..b, x ^ (-s) := by
    rw [interval_average_eq_div]
    dsimp [a, b]
    ring_nf
  rw [havg_id] at hJ
  rw [havg_pow] at hJ
  simpa [a, b] using hJ

lemma rpow_neg_le_integral_midpoint_unit
    {s : ℝ} (hs : 1 < s) {k : ℕ} (hk : 2 ≤ k) :
    ((k : ℝ) ^ (-s))
      ≤ ∫ x in ((k : ℝ) - 1 / 2)..((k : ℝ) + 1 / 2), x ^ (-s) := by
  have hk1 : 1 ≤ k := by
    omega
  simpa using rpow_neg_le_integral_centered hs hk1

lemma sum_Ico_rpow_neg_le_midpoint_tail
    {s : ℝ} (hs : 1 < s) (m N : ℕ) :
    (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
      ≤
    (1 / (s - 1)) /
      (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
  classical
  let a : ℕ → ℝ := fun k => (k : ℝ) - 1 / 2
  have hcont : ContinuousOn (fun x : ℝ => x ^ (-s)) (Set.Ioi 0) := by
    refine continuousOn_id.rpow_const ?_
    intro x hx
    exact Or.inl (Set.mem_Ioi.mp hx).ne'
  have hinterval (k : ℕ) (hk : 2 ≤ k) :
      IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume (a k) (a (k + 1)) := by
    have hpos : 0 < a k := by
      dsimp [a]
      have hk' : (2 : ℝ) ≤ k := by exact_mod_cast hk
      linarith
    have hle : a k ≤ a (k + 1) := by
      dsimp [a]
      norm_num [Nat.cast_add]
    refine (hcont.mono ?_).intervalIntegrable
    intro x hx
    have hx' : x ∈ Set.Icc (a k) (a (k + 1)) := by
      simpa [Set.uIcc_of_le hle] using hx
    exact lt_of_lt_of_le hpos hx'.1
  by_cases hMN : m + 2 ≤ N
  · have hsum_le :
        (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
          ≤
        ∑ k ∈ Finset.Ico (m + 2) N,
          ∫ x in a k..a (k + 1), x ^ (-s) := by
      refine Finset.sum_le_sum ?_
      intro k hk
      have hk2 : 2 ≤ k := le_trans (by omega : 2 ≤ m + 2) (Finset.mem_Ico.mp hk).1
      have ha_succ : a (k + 1) = (k : ℝ) + 1 / 2 := by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf
      rw [ha_succ]
      simpa [a] using rpow_neg_le_integral_midpoint_unit (s := s) hs hk2
    have htail_lt : -s < -1 := by linarith
    have hstart_pos' : 0 < ((m : ℝ) + 3 / 2) := by positivity
    have hstart_pos : 0 < a (m + 2) := by
      rw [show a (m + 2) = (m : ℝ) + 3 / 2 by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf]
      exact hstart_pos'
    have hsum_intervals :
        (∑ k ∈ Finset.Ico (m + 2) N,
          ∫ x in a k..a (k + 1), x ^ (-s))
          =
        ∫ x in a (m + 2)..a N, x ^ (-s) := by
      apply intervalIntegral.sum_integral_adjacent_intervals_Ico hMN
      intro k hk
      exact hinterval k (le_trans (by omega : 2 ≤ m + 2) hk.1)
    have hfinite_le_tail :
        ∫ x in a (m + 2)..a N, x ^ (-s)
          ≤ ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := by
      have hNpos : 0 < a N := by
        dsimp [a]
        have hN2 : 2 ≤ N := by omega
        have hN2' : (2 : ℝ) ≤ N := by exact_mod_cast hN2
        linarith
      have hstart_le : a (m + 2) ≤ a N := by
        dsimp [a]
        exact sub_le_sub_right (by exact_mod_cast hMN) (1 / 2 : ℝ)
      have hint :
          IntervalIntegrable (fun x : ℝ => x ^ (-s)) MeasureTheory.volume (a (m + 2)) (a N) := by
        refine (hcont.mono ?_).intervalIntegrable
        intro x hx
        have hx' : x ∈ Set.Icc (a (m + 2)) (a N) := by
          simpa [Set.uIcc_of_le hstart_le] using hx
        exact lt_of_lt_of_le hstart_pos hx'.1
      have htailN :
          0 ≤ ∫ x in Set.Ioi (a N), x ^ (-s) := by
        rw [integral_Ioi_rpow_of_lt htail_lt hNpos]
        have hs1_pos : 0 < s - 1 := by linarith
        have hs1 : s - 1 ≠ 0 := hs1_pos.ne'
        have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs.ne'.symm
        have hpow_pos : 0 < (a N) ^ (1 - s) := Real.rpow_pos_of_pos hNpos _
        have hnonneg : 0 ≤ (a N) ^ (1 - s) / (s - 1) := by
          exact div_nonneg hpow_pos.le hs1_pos.le
        calc
          0 ≤ (a N) ^ (1 - s) / (s - 1) := hnonneg
          _ = -((a N) ^ (-s + 1)) / (-s + 1) := by
                rw [show -s + 1 = 1 - s by ring]
                field_simp [h1s, hs1]
                ring
      have hdecomp :
          (∫ x in a (m + 2)..a N, x ^ (-s))
            + ∫ x in Set.Ioi (a N), x ^ (-s)
          =
          ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := by
        exact intervalIntegral.integral_interval_add_Ioi' hint
          (integrableOn_Ioi_rpow_of_lt htail_lt hNpos)
      nlinarith [hdecomp, htailN]
    have htail_eval :
        ∫ x in Set.Ioi (a (m + 2)), x ^ (-s)
          =
        (1 / (s - 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      have hs1 : s - 1 ≠ 0 := sub_ne_zero.mpr hs.ne'
      have h1s : 1 - s ≠ 0 := sub_ne_zero.mpr hs.ne'.symm
      rw [show a (m + 2) = (m : ℝ) + 3 / 2 by
        dsimp [a]
        norm_num [Nat.cast_add]
        ring_nf]
      rw [integral_Ioi_rpow_of_lt htail_lt hstart_pos']
      calc
        -(((m : ℝ) + 3 / 2) ^ (-s + 1)) / (-s + 1)
            = (((m : ℝ) + 3 / 2) ^ (1 - s)) / (s - 1) := by
                rw [show -s + 1 = 1 - s by ring]
                field_simp [h1s, hs1]
                ring
        _ = (((m : ℝ) + 3 / 2) ^ (-(s - 1))) / (s - 1) := by
              congr 1
              ring_nf
        _ = ((((m : ℝ) + 3 / 2) ^ (s - 1))⁻¹) / (s - 1) := by
              rw [Real.rpow_neg hstart_pos'.le]
        _ = (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
              simp [div_eq_mul_inv, mul_comm]
    calc
      (∑ k ∈ Finset.Ico (m + 2) N, ((k : ℝ) ^ (-s)))
          ≤ ∑ k ∈ Finset.Ico (m + 2) N,
              ∫ x in a k..a (k + 1), x ^ (-s) := hsum_le
      _ = ∫ x in a (m + 2)..a N, x ^ (-s) := hsum_intervals
      _ ≤ ∫ x in Set.Ioi (a (m + 2)), x ^ (-s) := hfinite_le_tail
      _ = (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := htail_eval
  · have hempty : Finset.Ico (m + 2) N = ∅ := by
      exact Finset.Ico_eq_empty_of_le (by omega)
    have hs1_pos : 0 < s - 1 := by linarith
    have hpow_pos : 0 < (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      exact Real.rpow_pos_of_pos (by positivity) _
    have hrhs_nonneg : 0 ≤ (1 / (s - 1)) / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
      exact div_nonneg (one_div_nonneg.mpr hs1_pos.le) hpow_pos.le
    simpa [hempty] using hrhs_nonneg

lemma logMesh_le_inv_succ (m : ℕ) :
    logMesh m ≤ 1 / ((m : ℝ) + 1) := by
  unfold logMesh
  have hpos : 0 < (m : ℝ) + 1 := by positivity
  have hratio_pos : 0 < (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by positivity
  calc
    Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1))
        ≤ (((m : ℝ) + 2) / ((m : ℝ) + 1)) - 1 :=
          Real.log_le_sub_one_of_pos hratio_pos
    _ = 1 / ((m : ℝ) + 1) := by field_simp [hpos.ne']; ring

lemma summable_logMesh_div_rpow
    {s : ℝ} (hs : 1 < s) :
    Summable fun m : ℕ =>
      logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
  have hspos : 0 < s - 1 := by linarith
  refine Summable.of_nonneg_of_le
    (fun m => by
      exact div_nonneg (logMesh_nonneg m)
        (le_of_lt (Real.rpow_pos_of_pos (by positivity) _)))
    ?_
    ((Real.summable_one_div_nat_add_rpow 1 s).2 hs)
  intro m
  have hlog := logMesh_le_inv_succ m
  have hbase1 : 0 < (m : ℝ) + 1 := by positivity
  have hbase2 : 0 < (m : ℝ) + 3 / 2 := by positivity
  have hbase_le : (m : ℝ) + 1 ≤ (m : ℝ) + 3 / 2 := by norm_num
  have hpow_le :
      ((m : ℝ) + 1) ^ (s - 1) ≤ ((m : ℝ) + 3 / 2) ^ (s - 1) := by
    exact Real.rpow_le_rpow hbase1.le hbase_le hspos.le
  have hden_pos : 0 < ((m : ℝ) + 3 / 2) ^ (s - 1) :=
    Real.rpow_pos_of_pos hbase2 _
  have hden1_pos : 0 < ((m : ℝ) + 1) ^ (s - 1) :=
    Real.rpow_pos_of_pos hbase1 _
  calc
    logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))
        ≤ (1 / ((m : ℝ) + 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1)) := by
          gcongr
    _ ≤ (1 / ((m : ℝ) + 1)) /
            (((m : ℝ) + 1) ^ (s - 1)) := by
          have hnum_nonneg : 0 ≤ 1 / ((m : ℝ) + 1) := by positivity
          have hrecip :
              1 / (((m : ℝ) + 3 / 2) ^ (s - 1)) ≤ 1 / (((m : ℝ) + 1) ^ (s - 1)) := by
            exact one_div_le_one_div_of_le hden1_pos hpow_le
          simpa [div_eq_mul_inv] using mul_le_mul_of_nonneg_left hrecip hnum_nonneg
    _ = 1 / |(m : ℝ) + 1| ^ s := by
          have habs : |(m : ℝ) + 1| = (m : ℝ) + 1 := abs_of_pos hbase1
          rw [div_eq_mul_inv, one_div, ← Real.rpow_neg_one, ← Real.rpow_neg hbase1.le]
          rw [← Real.rpow_add hbase1]
          have hs_eq : (-1 : ℝ) + -(s - 1) = -s := by ring
          rw [hs_eq]
          simpa [habs, one_div] using (Real.rpow_neg hbase1.le (y := s))

lemma finite_layer_cake_bound
    {s : ℝ} (hs : 1 < s) (N : ℕ) :
    (∑ n ∈ Finset.range N,
      Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s))
      ≤
    ∑ m ∈ Finset.range N,
      (1 / (s - 1)) *
        (logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
  have hspos : 0 < s - 1 := by linarith
  have hspow_pos (n : ℕ) : 0 < ((n : ℝ) + 1) ^ s := by
    exact Real.rpow_pos_of_pos (by positivity) _
  calc
    (∑ n ∈ Finset.range N,
      Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s))
        =
      ∑ n ∈ Finset.range N,
        (∑ m ∈ Finset.range n, logMesh m) / (((n : ℝ) + 1) ^ s) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [← log_nat_succ_eq_sum_logMesh n]
    _ =
      ∑ n ∈ Finset.range N,
        ∑ m ∈ Finset.range n,
          logMesh m * (((n : ℝ) + 1) ^ (-s)) := by
          refine Finset.sum_congr rfl ?_
          intro n hn
          rw [Finset.sum_div]
          refine Finset.sum_congr rfl ?_
          intro m hm
          rw [div_eq_mul_inv, ← Real.rpow_neg (by positivity)]
    _ =
      ∑ m ∈ Finset.range N,
        logMesh m *
          (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
          calc
            ∑ n ∈ Finset.range N,
              ∑ m ∈ Finset.range n, logMesh m * (((n : ℝ) + 1) ^ (-s))
                =
              ∑ m ∈ Finset.range N,
                ∑ n ∈ Finset.Ico (m + 1) N, logMesh m * (((n : ℝ) + 1) ^ (-s)) := by
                  simpa [Nat.Ico_zero_eq_range] using
                    (Finset.sum_Ico_Ico_comm' 0 N
                      (fun m n => logMesh m * (((n : ℝ) + 1) ^ (-s)))).symm
            _ =
              ∑ m ∈ Finset.range N,
                logMesh m *
                  (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
                    refine Finset.sum_congr rfl ?_
                    intro m hm
                    have hmN : m < N := Finset.mem_range.mp hm
                    have hshift :
                        (∑ n ∈ Finset.Ico (m + 1) N, (((n : ℝ) + 1) ^ (-s))) =
                          ∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s)) := by
                            rw [Finset.sum_Ico_eq_sum_range, Finset.sum_Ico_eq_sum_range]
                            have hlen : N - (m + 1) = N + 1 - (m + 2) := by
                              omega
                            rw [hlen]
                            refine Finset.sum_congr rfl ?_
                            intro x hx
                            norm_num [Nat.cast_add, add_left_comm, add_comm]
                    calc
                      ∑ n ∈ Finset.Ico (m + 1) N, logMesh m * (((n : ℝ) + 1) ^ (-s))
                          = logMesh m * (∑ n ∈ Finset.Ico (m + 1) N, (((n : ℝ) + 1) ^ (-s))) := by
                              rw [Finset.mul_sum]
                      _ = logMesh m * (∑ k ∈ Finset.Ico (m + 2) (N + 1), ((k : ℝ) ^ (-s))) := by
                              rw [hshift]
    _ ≤
      ∑ m ∈ Finset.range N,
        logMesh m *
          ((1 / (s - 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          refine Finset.sum_le_sum ?_
          intro m hm
          have hA : 0 ≤ logMesh m := logMesh_nonneg m
          gcongr
          exact sum_Ico_rpow_neg_le_midpoint_tail hs m (N + 1)
    _ =
      ∑ m ∈ Finset.range N,
        (1 / (s - 1)) *
          (logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          refine Finset.sum_congr rfl ?_
          intro m hm
          ring

lemma tsum_log_nat_succ_div_rpow_le_log_mesh
    {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
      ≤
    (1 / (s - 1)) *
      (∑' m : ℕ,
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
  have hspos : 0 < s - 1 := by linarith
  let f : ℕ → ℝ :=
    fun n => Real.log ((n : ℝ) + 1) / (((n : ℝ) + 1) ^ s)
  let g : ℕ → ℝ :=
    fun m => logMesh m / (((m : ℝ) + 3 / 2) ^ (s - 1))
  have hf_nonneg : ∀ n, 0 ≤ f n := by
    intro n
    dsimp [f]
    have hlog_arg : (1 : ℝ) ≤ (n : ℝ) + 1 := by
      have hn_nonneg : (0 : ℝ) ≤ n := by exact_mod_cast Nat.zero_le n
      linarith
    exact div_nonneg
      (Real.log_nonneg hlog_arg)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hg_nonneg : ∀ m, 0 ≤ g m := by
    intro m
    dsimp [g]
    exact div_nonneg
      (logMesh_nonneg m)
      (le_of_lt (Real.rpow_pos_of_pos (by positivity) _))
  have hg_summable : Summable g := by
    simpa [g, logMesh] using summable_logMesh_div_rpow hs
  have hpartial :
      ∀ N,
        ∑ n ∈ Finset.range N, f n
          ≤ ∑ m ∈ Finset.range N, (1 / (s - 1)) * g m := by
    intro N
    simpa [f, g, logMesh] using finite_layer_cake_bound hs N
  calc
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
        = ∑' n : ℕ, f n := by simp [f]
    _ ≤ ∑' m : ℕ, (1 / (s - 1)) * g m := by
          refine Real.tsum_le_of_sum_range_le ?_ ?_
          · intro n
            exact hf_nonneg n
          · intro N
            calc
              ∑ n ∈ Finset.range N, f n
                  ≤ ∑ m ∈ Finset.range N, (1 / (s - 1)) * g m :=
                    hpartial N
              _ ≤ ∑' m : ℕ, (1 / (s - 1)) * g m := by
                    have hsg : Summable fun m => (1 / (s - 1)) * g m :=
                      hg_summable.mul_left _
                    refine hsg.sum_le_tsum (Finset.range N) ?_
                    intro m hm
                    exact mul_nonneg (by positivity) (hg_nonneg m)
    _ =
      (1 / (s - 1)) * (∑' m : ℕ, g m) := by
          rw [tsum_mul_left]
    _ =
      (1 / (s - 1)) *
        (∑' m : ℕ,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
            (((m : ℝ) + 3 / 2) ^ (s - 1))) := by
          simp [g, logMesh]

lemma tsum_log_mesh_le_one_div_sub
    {s : ℝ} (hs : 1 < s) :
    (∑' m : ℕ,
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ (s - 1)))
      ≤ 1 / (s - 1) := by
  let δ : ℝ := s - 1
  have hδ : 0 < δ := by
    simpa [δ] using sub_pos.mpr hs
  have hδ_ne : δ ≠ 0 := hδ.ne'
  let g : ℝ → ℝ := fun x => Real.exp (-δ * x)
  have hg_cont : Continuous g := by
    fun_prop
  have hg_convex : ConvexOn ℝ Set.univ g := by
    convert convexOn_exp.comp_linearMap (LinearMap.mul ℝ ℝ (-δ)) using 1
  have havg_id {a b : ℝ} (hab : a < b) : (⨍ x in a..b, x) = (a + b) / 2 := by
    rw [interval_average_eq_div, integral_id]
    field_simp [sub_ne_zero.mpr hab.ne']
    ring
  have hmidpoint_le_average {a b : ℝ} (hab : a < b) :
      g ((a + b) / 2) ≤ ⨍ x in a..b, g x := by
    have hJ0 :
        g (⨍ x in Set.uIoc a b, (fun x : ℝ => x) x ∂MeasureTheory.volume) ≤
          ⨍ x in Set.uIoc a b, g ((fun x : ℝ => x) x) ∂MeasureTheory.volume := by
      exact
        hg_convex.map_set_average_le hg_cont.continuousOn isClosed_univ
          (by simpa using sub_ne_zero.mpr hab.ne') (by simp)
          (Filter.Eventually.of_forall fun x => by simp)
          (continuous_id.continuousOn.integrableOn_of_subset_isCompact
            isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc (by simp))
          (hg_cont.continuousOn.integrableOn_of_subset_isCompact
            isCompact_uIcc measurableSet_uIoc Set.uIoc_subset_uIcc (by simp))
    simpa [havg_id hab] using hJ0
  have hterm_nonneg (m : ℕ) :
      0 ≤
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ δ) := by
    have hratio_ge : 1 ≤ ((m : ℝ) + 2) / ((m : ℝ) + 1) := by
      have hm1_pos : 0 < (m : ℝ) + 1 := by positivity
      exact (one_le_div hm1_pos).2 (by linarith)
    have hlog_nonneg : 0 ≤ Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) :=
      Real.log_nonneg hratio_ge
    have hpow_nonneg : 0 ≤ (((m : ℝ) + 3 / 2) ^ δ) := by
      exact (Real.rpow_pos_of_pos (by positivity) _).le
    exact div_nonneg hlog_nonneg hpow_nonneg
  have hterm_le_integral (m : ℕ) :
      Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
          (((m : ℝ) + 3 / 2) ^ δ)
        ≤
      ∫ x in Real.log (m + 1)..Real.log (m + 2), g x := by
    let a : ℝ := Real.log (m + 1)
    let b : ℝ := Real.log (m + 2)
    have hm1_pos : 0 < (m : ℝ) + 1 := by positivity
    have hm2_pos : 0 < (m : ℝ) + 2 := by positivity
    have hmid_pos : 0 < (m : ℝ) + 3 / 2 := by positivity
    have hab : a < b := by
      dsimp [a, b]
      exact Real.log_lt_log hm1_pos (by linarith)
    have hJ' :
        g ((a + b) / 2) * (b - a) ≤ ∫ x in a..b, g x := by
      exact (le_div_iff₀ (sub_pos.mpr hab)).mp
        (by simpa [interval_average_eq_div] using hmidpoint_le_average (a := a) (b := b) hab)
    have hJ :
        (b - a) * g ((a + b) / 2) ≤ ∫ x in a..b, g x := by
      simpa [mul_comm] using hJ'
    have hgeom_sq :
        (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ (((m : ℝ) + 3 / 2) ^ 2) := by
      nlinarith
    have hgeom_le : Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2)) ≤ (m : ℝ) + 3 / 2 := by
      rw [Real.sqrt_le_iff]
      constructor
      · positivity
      · simpa [pow_two] using hgeom_sq
    have hmid_log_le : (a + b) / 2 ≤ Real.log ((m : ℝ) + 3 / 2) := by
      calc
        (a + b) / 2
            = Real.log (Real.sqrt (((m : ℝ) + 1) * ((m : ℝ) + 2))) := by
                dsimp [a, b]
                rw [Real.log_sqrt]
                · rw [Real.log_mul (by positivity) (by positivity)]
                · positivity
        _ ≤ Real.log ((m : ℝ) + 3 / 2) := Real.log_le_log (by positivity) hgeom_le
    have hmid_compare :
        g (Real.log ((m : ℝ) + 3 / 2)) ≤ g ((a + b) / 2) := by
      dsimp [g]
      apply Real.exp_le_exp.mpr
      nlinarith
    have hlen_eq : b - a = Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) := by
      dsimp [a, b]
      symm
      exact Real.log_div (by positivity) (by positivity)
    have hmid_eval :
        g (Real.log ((m : ℝ) + 3 / 2)) = 1 / (((m : ℝ) + 3 / 2) ^ δ) := by
      dsimp [g]
      rw [Real.rpow_def_of_pos hmid_pos, one_div, ← Real.exp_neg]
      congr 1
      ring
    calc
      Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) / (((m : ℝ) + 3 / 2) ^ δ)
          = (b - a) * g (Real.log ((m : ℝ) + 3 / 2)) := by
              rw [hlen_eq, hmid_eval]
              ring
      _ ≤ (b - a) * g ((a + b) / 2) :=
            mul_le_mul_of_nonneg_left hmid_compare (sub_nonneg.mpr hab.le)
      _ ≤ ∫ x in a..b, g x := hJ
      _ = ∫ x in Real.log (m + 1)..Real.log (m + 2), g x := by rfl
  have hintegral_bound (t : ℝ) :
      ∫ x in 0..t, g x ≤ 1 / δ := by
    have hcalc :
        ∫ x in 0..t, g x = (1 - Real.exp (-δ * t)) / δ := by
      calc
        ∫ x in 0..t, g x
            = (-δ)⁻¹ * ∫ y in (-δ) * (0 : ℝ)..(-δ) * t, Real.exp y := by
                simpa [g, mul_assoc, mul_comm, mul_left_comm] using
                  (intervalIntegral.integral_comp_mul_left
                    (f := fun y : ℝ => Real.exp y) (a := (0 : ℝ)) (b := t)
                    (c := -δ) (neg_ne_zero.mpr hδ_ne))
        _ = (-δ)⁻¹ * (Real.exp ((-δ) * t) - Real.exp (0 : ℝ)) := by
              simp
        _ = (1 - Real.exp (-δ * t)) / δ := by
              rw [Real.exp_zero]
              field_simp [hδ_ne]
              ring_nf
    rw [hcalc]
    have hExp_nonneg : 0 ≤ Real.exp (-δ * t) := by positivity
    exact div_le_div_of_nonneg_right (by linarith) hδ.le
  have hpartial (n : ℕ) :
      ∑ m ∈ Finset.range n,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) / (((m : ℝ) + 3 / 2) ^ δ)
        ≤
      1 / δ := by
    calc
      ∑ m ∈ Finset.range n,
          Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) / (((m : ℝ) + 3 / 2) ^ δ)
          ≤
        ∑ m ∈ Finset.range n, ∫ x in Real.log (m + 1)..Real.log (m + 2), g x := by
          refine Finset.sum_le_sum fun m hm => hterm_le_integral m
      _ = ∫ x in (Real.log (0 + 1 : ℕ))..(Real.log (n + 1)), g x := by
            simpa [Nat.cast_add, Nat.cast_one, add_assoc,
              show ((1 : ℝ) + 1) = 2 by norm_num] using
              (intervalIntegral.sum_integral_adjacent_intervals
                (f := g) (μ := MeasureTheory.volume)
                (a := fun k : ℕ => Real.log ((k : ℝ) + 1)) (n := n)
                (fun k hk => hg_cont.intervalIntegrable _ _))
      _ = ∫ x in 0..(Real.log (n + 1)), g x := by simp
      _ ≤ 1 / δ := hintegral_bound (Real.log (n + 1))
  exact
    (Real.tsum_le_of_sum_range_le
      (f := fun m : ℕ =>
        Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) / (((m : ℝ) + 3 / 2) ^ δ))
      hterm_nonneg hpartial).trans_eq (by simp [δ])

lemma one_div_sub_mul_one_div_sub_eq_one_div_sq
    {s : ℝ} (hs : 1 < s) :
    (1 / (s - 1)) * (1 / (s - 1)) = 1 / (s - 1) ^ 2 := by
  have hne : s - 1 ≠ 0 := by linarith
  field_simp [hne]

lemma tsum_log_nat_succ_div_rpow_le_one_div_sq_sub {s : ℝ} (hs : 1 < s) :
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
      ≤ 1 / (s - 1) ^ 2 := by
  have h₁ := tsum_log_nat_succ_div_rpow_le_log_mesh (s := s) hs
  have h₂ := tsum_log_mesh_le_one_div_sub (s := s) hs
  have hpos : 0 ≤ 1 / (s - 1) := by
    have hs_sub_pos : 0 < s - 1 := by
      linarith
    exact le_of_lt (one_div_pos.mpr hs_sub_pos)
  calc
    (∑' n : ℕ, Real.log (n + 1) / ((n + 1 : ℝ) ^ s))
        ≤ (1 / (s - 1)) *
            (∑' m : ℕ,
              Real.log (((m : ℝ) + 2) / ((m : ℝ) + 1)) /
                (((m : ℝ) + 3 / 2) ^ (s - 1))) := h₁
    _ ≤ (1 / (s - 1)) * (1 / (s - 1)) :=
        mul_le_mul_of_nonneg_left h₂ hpos
    _ = 1 / (s - 1) ^ 2 :=
        one_div_sub_mul_one_div_sub_eq_one_div_sq (s := s) hs

lemma neg_deriv_zetaSeries_le_one_div_sq_sub {s : ℝ} (hs : 1 < s) :
    -deriv zetaSeries s ≤ 1 / (s - 1) ^ 2 := by
  rw [neg_deriv_zetaSeries_eq_tsum_log_nat_succ_div_rpow hs]
  exact tsum_log_nat_succ_div_rpow_le_one_div_sq_sub hs

lemma zetaSeries_ge_one_div_sub_add_one_half {s : ℝ} (hs : 1 < s) :
    zetaSeries s ≥ 1 / (s - 1) + (1 / 2 : ℝ) := by
  let f : ℝ → ℝ := fun x => x ^ (-s)
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  have hs_ne : s ≠ 0 := hs_pos.ne'
  have hs_sub_ne : s - 1 ≠ 0 := by linarith
  have hconv : ConvexOn ℝ (Set.Ioi 0) f := by
    refine (strictConvexOn_of_deriv2_pos' (convex_Ioi (0 : ℝ)) ?_ ?_).convexOn
    · intro x hx
      exact (Real.continuousAt_rpow_const x (-s) (Or.inl hx.ne')).continuousWithinAt
    · intro x hx
      rw [show (deriv^[2] f) x = (deriv^[2] fun y : ℝ => y ^ (-s)) x by rfl]
      rw [Real.iter_deriv_rpow_const (-s) x 2]
      rw [descPochhammer_succ_eval, descPochhammer_succ_eval]
      have hcoeff : 0 < (-s) * (-s - 1) := by
        nlinarith
      have hpow : 0 < x ^ (-s - 2) := Real.rpow_pos_of_pos hx _
      simpa using mul_pos hcoeff hpow
  have hsecant (n : ℕ) :
      ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x ≤
        (f (n + 1) + f (n + 2)) / 2 := by
    have a_eq : (((n + 1 : ℕ) : ℝ)) = (n : ℝ) + 1 := by norm_num
    have b_eq : (((n + 2 : ℕ) : ℝ)) = (n : ℝ) + 2 := by norm_num
    have hle : (((n + 1 : ℕ) : ℝ)) ≤ (((n + 2 : ℕ) : ℝ)) := by norm_num
    have hpos1 : 0 < (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos n
    have hpos2 : 0 < (((n + 2 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos (n + 1)
    have hf_int :
        IntervalIntegrable f MeasureTheory.volume (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
      refine (continuousOn_of_forall_continuousAt fun x hx => ?_).intervalIntegrable
      rw [Set.uIcc_of_le hle] at hx
      have hx_pos : 0 < x := lt_of_lt_of_le hpos1 hx.1
      exact Real.continuousAt_rpow_const x (-s) (Or.inl hx_pos.ne')
    have hlin_int :
        IntervalIntegrable
          (fun x : ℝ => (((n + 2 : ℕ) : ℝ) - x) * f (n + 1) + (x - (n + 1 : ℝ)) * f (n + 2))
          MeasureTheory.volume (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
      refine (ContinuousOn.intervalIntegrable ?_)
      intro x hx
      fun_prop
    have hba : (((n + 2 : ℕ) : ℝ)) - (((n + 1 : ℕ) : ℝ)) = 1 := by norm_num
    have hpoint :
        ∀ x ∈ Set.Icc (((n + 1 : ℕ) : ℝ)) ((n + 2 : ℕ) : ℝ),
          f x ≤ (((n + 2 : ℕ) : ℝ) - x) * f (n + 1) + (x - (n + 1 : ℝ)) * f (n + 2) := by
      intro x hx
      rcases eq_or_lt_of_le hx.1 with rfl | hlt1
      · norm_num
      rcases eq_or_lt_of_le hx.2 with rfl | hlt2
      · norm_num
      have haux := hconv.secant_mono_aux1 hpos1 hpos2 hlt1 hlt2
      have htwo : (2 : ℝ) - 1 = 1 := by norm_num
      simpa [htwo, mul_comm, add_comm, add_left_comm, add_assoc,
        Nat.cast_add, Nat.cast_one] using haux
    have hmain :
        ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x ≤
          ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
            ((((n + 2 : ℕ) : ℝ) - x) * f (n + 1) + (x - (n + 1 : ℝ)) * f (n + 2)) := by
      exact intervalIntegral.integral_mono_on hle hf_int hlin_int hpoint
    have hsub1_int :
        IntervalIntegrable (fun x : ℝ => (((n + 2 : ℕ) : ℝ) - x)) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
      exact (by fun_prop : Continuous fun x : ℝ => (((n + 2 : ℕ) : ℝ) - x)).intervalIntegrable _ _
    have hsub2_int :
        IntervalIntegrable (fun x : ℝ => x - (((n + 1 : ℕ) : ℝ)) ) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
      exact (by fun_prop : Continuous fun x : ℝ => x - (((n + 1 : ℕ) : ℝ))).intervalIntegrable _ _
    have hmul1_int :
        IntervalIntegrable
          (fun x : ℝ => ((((n + 2 : ℕ) : ℝ) - x) * f (n + 1))) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) :=
      hsub1_int.mul_const (f (n + 1))
    have hmul2_int :
        IntervalIntegrable
          (fun x : ℝ => ((x - (((n + 1 : ℕ) : ℝ))) * f (n + 2)) ) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) :=
      hsub2_int.mul_const (f (n + 2))
    have h_id_int :
        IntervalIntegrable (fun x : ℝ => x) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) := by
      exact (by fun_prop : Continuous fun x : ℝ => x).intervalIntegrable _ _
    have hconst1_int :
        IntervalIntegrable (fun _ : ℝ => (((n + 1 : ℕ) : ℝ))) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) :=
      intervalIntegrable_const
    have hconst2_int :
        IntervalIntegrable (fun _ : ℝ => (((n + 2 : ℕ) : ℝ))) MeasureTheory.volume
          (((n + 1 : ℕ) : ℝ)) (((n + 2 : ℕ) : ℝ)) :=
      intervalIntegrable_const
    calc
      ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x
          ≤ ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
              ((((n + 2 : ℕ) : ℝ) - x) * f (n + 1) + (x - (n + 1 : ℝ)) * f (n + 2)) := hmain
      _ = (f (n + 1) + f (n + 2)) / 2 := by
          have hadd :
              ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
                  ((((n + 2 : ℕ) : ℝ) - x) * f (n + 1) + (x - (n + 1 : ℝ)) * f (n + 2))
                =
              (∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
                  (((n + 2 : ℕ) : ℝ) - x) * f (n + 1)) +
                ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ),
                  (x - (((n + 1 : ℕ) : ℝ))) * f (n + 2) := by
            simpa using intervalIntegral.integral_add hmul1_int hmul2_int
          rw [hadd]
          rw [intervalIntegral.integral_mul_const, intervalIntegral.integral_mul_const]
          rw [intervalIntegral.integral_sub hconst2_int h_id_int,
            intervalIntegral.integral_sub h_id_int hconst1_int,
            intervalIntegral.integral_const, intervalIntegral.integral_const,
            integral_id]
          norm_num [a_eq, b_eq]
          ring_nf
  have hterm_bound (n : ℕ) :
      ZetaAsymptotics.term (n + 1) s ≤
        (1 / (2 * s)) * (f (n + 1) - f (n + 2)) := by
    have hpos1 : 0 < (((n + 1 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos n
    have hpos2 : 0 < (((n + 2 : ℕ) : ℝ)) := by
      exact_mod_cast Nat.succ_pos (n + 1)
    have hterm :=
      ZetaAsymptotics.term_of_lt (n := n + 1) (by positivity) hs
    have hint :
        ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x =
          1 / (s - 1) *
            (1 / ((n + 1 : ℝ) ^ (s - 1)) - 1 / ((n + 2 : ℝ) ^ (s - 1))) := by
      change ∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), x ^ (-s) =
          1 / (s - 1) *
            (1 / ((n + 1 : ℝ) ^ (s - 1)) - 1 / ((n + 2 : ℝ) ^ (s - 1)))
      rw [integral_rpow]
      · rw [show -s + 1 = -(s - 1) by ring]
        rw [div_neg, ← neg_div, mul_comm, mul_one_div, neg_sub]
        have h1 : (((n + 1 : ℕ) : ℝ) ^ (-(s - 1))) = 1 / (((n + 1 : ℕ) : ℝ) ^ (s - 1)) := by
          simpa [one_div] using
            (Real.rpow_neg (show 0 ≤ (n + 1 : ℝ) by positivity) (y := s - 1))
        have h2 : (((n + 2 : ℕ) : ℝ) ^ (-(s - 1))) = 1 / (((n + 2 : ℕ) : ℝ) ^ (s - 1)) := by
          simpa [one_div] using
            (Real.rpow_neg (show 0 ≤ (n + 2 : ℝ) by positivity) (y := s - 1))
        rw [h1, h2]
        norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
      · refine Or.inr ⟨by linarith, ?_⟩
        exact Set.notMem_uIcc_of_lt hpos1 hpos2
    have hcast : (((n + 1 : ℕ) : ℝ) + 1) = (((n + 2 : ℕ) : ℝ)) := by
      norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
    have ha_ne : (((n + 1 : ℕ) : ℝ)) ^ s ≠ 0 := (Real.rpow_pos_of_pos hpos1 s).ne'
    have hb_ne : (((n + 2 : ℕ) : ℝ)) ^ s ≠ 0 := (Real.rpow_pos_of_pos hpos2 s).ne'
    have ha_sub :
        1 / (((n + 1 : ℕ) : ℝ) ^ (s - 1)) =
          (((n + 1 : ℕ) : ℝ)) / (((n + 1 : ℕ) : ℝ) ^ s) := by
      rw [Real.rpow_sub hpos1 s 1, Real.rpow_one]
      field_simp [ha_ne]
    have hb_sub :
        1 / (((n + 2 : ℕ) : ℝ) ^ (s - 1)) =
          (((n + 2 : ℕ) : ℝ)) / (((n + 2 : ℕ) : ℝ) ^ s) := by
      rw [Real.rpow_sub hpos2 s 1, Real.rpow_one]
      field_simp [hb_ne]
    have halg :
        1 / (s - 1) *
            (1 / (((n + 1 : ℕ) : ℝ) ^ (s - 1)) - 1 / (((n + 2 : ℕ) : ℝ) ^ (s - 1))) -
          (((n + 1 : ℕ) : ℝ) / s) *
            (1 / (((n + 1 : ℕ) : ℝ) ^ s) - 1 / (((n + 2 : ℕ) : ℝ) ^ s)) =
        (1 / s) *
          (1 / (s - 1) *
              (1 / (((n + 1 : ℕ) : ℝ) ^ (s - 1)) - 1 / (((n + 2 : ℕ) : ℝ) ^ (s - 1))) -
            1 / (((n + 2 : ℕ) : ℝ) ^ s)) := by
      rw [ha_sub, hb_sub]
      field_simp [hs_ne, hs_sub_ne, ha_ne, hb_ne]
      rw [← hcast]
      ring
    have hrepr :
        ZetaAsymptotics.term (n + 1) s =
          (1 / s) *
            ((∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x) - 1 / (((n + 2 : ℕ) : ℝ) ^ s)) := by
      rw [hterm, hcast, hint]
      simpa [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm] using halg
    have hs_nonneg : 0 ≤ 1 / s := by positivity
    have hmid :
        (1 / s) *
            ((∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x) - 1 / (((n + 2 : ℕ) : ℝ) ^ s))
          ≤
        (1 / s) * ((((f (n + 1) + f (n + 2)) / 2) - 1 / (((n + 2 : ℕ) : ℝ) ^ s))) := by
      have hsub :
          (∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x) -
              1 / ((((n + 2 : ℕ) : ℝ)) ^ s)
            ≤
          ((f (n + 1) + f (n + 2)) / 2) - 1 / ((((n + 2 : ℕ) : ℝ)) ^ s) := by
        exact sub_le_sub_right (hsecant n) (1 / ((((n + 2 : ℕ) : ℝ)) ^ s))
      exact mul_le_mul_of_nonneg_left hsub hs_nonneg
    have hb_f : 1 / ((((n + 2 : ℕ) : ℝ)) ^ s) = f (n + 2) := by
      simpa [f, one_div] using
        (Real.rpow_neg (show 0 ≤ (((n + 2 : ℕ) : ℝ)) by positivity) (y := s)).symm
    calc
      ZetaAsymptotics.term (n + 1) s
          = (1 / s) *
              ((∫ x in ((n + 1 : ℕ) : ℝ)..((n + 2 : ℕ) : ℝ), f x) -
                1 / ((((n + 2 : ℕ) : ℝ)) ^ s)) := hrepr
      _ ≤ (1 / s) * (((f (n + 1) + f (n + 2)) / 2) - 1 / ((((n + 2 : ℕ) : ℝ)) ^ s)) := hmid
      _ = (1 / (2 * s)) * (f (n + 1) - f (n + 2)) := by
          rw [hb_f]
          ring
  have hterm_nonneg : ∀ n : ℕ, 0 ≤ ZetaAsymptotics.term (n + 1) s := by
    intro n
    exact ZetaAsymptotics.term_nonneg (n + 1) s
  have hterm_tsum :
      ZetaAsymptotics.term_tsum s ≤ 1 / (2 * s) := by
    have htel :
        ∀ N : ℕ, ∑ i ∈ Finset.range N, (f (i + 1) - f (i + 2)) = f 1 - f (N + 1) := by
      intro N
      induction N with
      | zero =>
          simp
      | succ N hN =>
          rw [Finset.sum_range_succ, hN]
          have hcast : f (((N : ℝ) + 2)) = f ((((N + 1 : ℕ) : ℝ) + 1)) := by
            congr 1
            norm_num [Nat.cast_add, Nat.cast_one, add_assoc, add_left_comm, add_comm]
          rw [hcast]
          ring
    have hsum_range : ∀ N : ℕ,
        ∑ i ∈ Finset.range N, ZetaAsymptotics.term (i + 1) s ≤ 1 / (2 * s) := by
      intro N
      calc
        ∑ i ∈ Finset.range N, ZetaAsymptotics.term (i + 1) s
            ≤ ∑ i ∈ Finset.range N, (1 / (2 * s)) * (f (i + 1) - f (i + 2)) := by
                exact Finset.sum_le_sum fun i hi => hterm_bound i
        _ = (1 / (2 * s)) * (f 1 - f (N + 1)) := by
              rw [← Finset.mul_sum, htel N]
        _ ≤ 1 / (2 * s) := by
              have hf_nonneg : 0 ≤ f (N + 1) := Real.rpow_nonneg (by positivity) _
              have hfac_nonneg : 0 ≤ 1 / (2 * s) := by positivity
              have hsub : f 1 - f (N + 1) ≤ 1 := by
                simpa [f] using sub_le_self (f 1) hf_nonneg
              have hm := mul_le_mul_of_nonneg_left hsub hfac_nonneg
              simpa [f, div_eq_mul_inv] using hm
    have htsum :=
      Real.tsum_le_of_sum_range_le hterm_nonneg hsum_range
    simpa [ZetaAsymptotics.term_tsum] using htsum
  have hzt :
      ZetaAsymptotics.term_tsum s = 1 / (s - 1) - (1 / s) * zetaSeries s := by
    simpa [ZetaAsymptotics.term_tsum, zetaSeries] using ZetaAsymptotics.term_tsum_of_lt hs
  rw [hzt] at hterm_tsum
  have : 1 / (s - 1) - (1 / s) * zetaSeries s ≤ 1 / (2 * s) := hterm_tsum
  have hs_nonneg : 0 ≤ s := hs_pos.le
  have hs_two_ne : (2 : ℝ) * s ≠ 0 := by positivity
  have hs_ne' : s ≠ 0 := hs_pos.ne'
  have hs_sub_pos : 0 < s - 1 := by linarith
  have hs_sub_ne' : s - 1 ≠ 0 := hs_sub_pos.ne'
  have hgoal : 1 / (s - 1) + (1 / 2 : ℝ) ≤ zetaSeries s := by
    have hmul := (mul_le_mul_of_nonneg_left this hs_nonneg)
    have hs_eq : s * (1 / (s - 1) - (1 / s) * zetaSeries s) ≤ s * (1 / (2 * s)) := hmul
    have hs_rhs : s * (1 / (2 * s)) = (1 / 2 : ℝ) := by
      field_simp [hs_two_ne]
    have hs_lhs : s * (1 / (s - 1) - (1 / s) * zetaSeries s) = s / (s - 1) - zetaSeries s := by
      field_simp [hs_ne']
    have hs_frac : s / (s - 1) = 1 + 1 / (s - 1) := by
      field_simp [hs_sub_ne']
      ring
    rw [hs_lhs, hs_rhs] at hs_eq
    rw [hs_frac] at hs_eq
    linarith
  simpa using hgoal

lemma analyticSeries_le_two_div_sq_sub_one {s : ℝ} (hs : 1 < s) :
    analyticSeries s ≤ 2 / (s ^ 2 - 1) := by
  have hs_sub_pos : 0 < s - 1 := by
    linarith
  have hs_sub_ne : s - 1 ≠ 0 := by
    linarith
  have hs_add_ne : s + 1 ≠ 0 := by
    linarith
  have hs_sq_sub_ne : s ^ 2 - 1 ≠ 0 := by
    nlinarith
  have hζ_bound : 1 / (s - 1) + (1 / 2 : ℝ) ≤ zetaSeries s := by
    simpa using zetaSeries_ge_one_div_sub_add_one_half hs
  have hζ_lower : 0 < 1 / (s - 1) + (1 / 2 : ℝ) := by
    have hmain : 0 < 1 / (s - 1 : ℝ) := one_div_pos.mpr hs_sub_pos
    linarith
  have hζ_pos : 0 < zetaSeries s := lt_of_lt_of_le hζ_lower hζ_bound
  rw [analyticSeries_eq_neg_deriv_zetaSeries_div_zetaSeries hs]
  by_cases hnum_nonneg : 0 ≤ -deriv zetaSeries s
  · have hrecip :
        1 / zetaSeries s ≤ 1 / (1 / (s - 1) + (1 / 2 : ℝ)) :=
      one_div_le_one_div_of_le hζ_lower hζ_bound
    have hstep1 :
        (-deriv zetaSeries s) * (1 / zetaSeries s) ≤
          (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := by
      exact mul_le_mul_of_nonneg_left hrecip hnum_nonneg
    have hstep2 :
        (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) ≤
          (1 / (s - 1) ^ 2) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := by
      have hrecip_nonneg : 0 ≤ 1 / (1 / (s - 1) + (1 / 2 : ℝ)) := by
        positivity
      exact
        mul_le_mul_of_nonneg_right (neg_deriv_zetaSeries_le_one_div_sq_sub hs)
          hrecip_nonneg
    have hratio :
        (1 / (s - 1) ^ 2) / (1 / (s - 1) + (1 / 2 : ℝ)) = 2 / (s ^ 2 - 1) := by
      field_simp [hs_sub_ne, hs_add_ne, hs_sq_sub_ne]
      ring
    calc
      (-deriv zetaSeries s) / zetaSeries s
          = (-deriv zetaSeries s) * (1 / zetaSeries s) := by
              simp [div_eq_mul_inv]
      _ ≤ (-deriv zetaSeries s) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := hstep1
      _ ≤ (1 / (s - 1) ^ 2) * (1 / (1 / (s - 1) + (1 / 2 : ℝ))) := hstep2
      _ = (1 / (s - 1) ^ 2) / (1 / (s - 1) + (1 / 2 : ℝ)) := by
            simp [div_eq_mul_inv]
      _ = 2 / (s ^ 2 - 1) := hratio
  · have hnum_nonpos : -deriv zetaSeries s ≤ 0 := le_of_not_ge hnum_nonneg
    have hleft : (-deriv zetaSeries s) / zetaSeries s ≤ 0 := by
      exact div_nonpos_of_nonpos_of_nonneg hnum_nonpos (le_of_lt hζ_pos)
    have hs_sq_sub_pos : 0 < s ^ 2 - 1 := by
      nlinarith
    have hright : 0 ≤ 2 / (s ^ 2 - 1) := by
      exact le_of_lt (div_pos (by positivity) hs_sq_sub_pos)
    exact hleft.trans hright

lemma prime_log_term_le_one_div_add {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s + 1) := by
  have hs_pos : 0 < s := lt_trans zero_lt_one hs
  have hp_pos : 0 < (p : ℝ) := Nat.cast_pos.mpr hp.pos
  have hrpow_pos : 0 < Real.rpow (p : ℝ) s := Real.rpow_pos_of_pos hp_pos s
  have h_exp_two : (2 : ℝ) ≤ Real.exp 1 := by
    simpa [one_add_one_eq_two] using Real.add_one_le_exp 1
  have h_log_over_exp : s * Real.log p ≤ Real.rpow (p : ℝ) s / Real.exp 1 := by
    apply (le_div_iff₀ (Real.exp_pos 1)).2
    have h := Real.exp_one_mul_le_exp (x := s * Real.log p)
    simpa [Real.rpow_def_of_pos hp_pos, mul_comm, mul_left_comm, mul_assoc] using h
  have h_main : Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (Real.exp 1 * s) := by
    apply (div_le_iff₀ hrpow_pos).2
    have h' : Real.log p ≤ (Real.rpow (p : ℝ) s / Real.exp 1) / s := by
      apply (le_div_iff₀ hs_pos).2
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_log_over_exp
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h'
  have h_den : s + 1 ≤ Real.exp 1 * s := by
    calc
      s + 1 ≤ s + s := by linarith
      _ = (2 : ℝ) * s := by ring
      _ ≤ Real.exp 1 * s := by
        gcongr
  exact h_main.trans (one_div_le_one_div_of_le (by positivity) h_den)

lemma two_div_sq_sub_one_add_one_div_add_eq_one_div_sub {s : ℝ} (hs : 1 < s) :
    2 / (s ^ 2 - 1) + 1 / (s + 1) = 1 / (s - 1) := by
  have hs_sub : s - 1 ≠ 0 := by linarith
  have hs_add : s + 1 ≠ 0 := by linarith
  have hfactor : s ^ 2 - 1 = (s - 1) * (s + 1) := by ring
  rw [hfactor]
  field_simp [hs_sub, hs_add]
  ring

lemma analyticSeries_add_log_term_le_of_aux_bounds {s : ℝ} (hs : 1 < s)
    {p : ℕ} (hp : p.Prime) :
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s - 1) := by
  calc
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s
        ≤ 2 / (s ^ 2 - 1) + 1 / (s + 1) := by
          exact add_le_add (analyticSeries_le_two_div_sq_sub_one hs)
            (prime_log_term_le_one_div_add hs hp)
    _ = 1 / (s - 1) := two_div_sq_sub_one_add_one_div_add_eq_one_div_sub hs

theorem analyticSeries_add_log_term_le {s : ℝ} (hs : 1 < s) {p : ℕ} (hp : p.Prime) :
    analyticSeries s + Real.log p / Real.rpow (p : ℝ) s ≤ 1 / (s - 1) :=
  analyticSeries_add_log_term_le_of_aux_bounds hs hp

lemma inflow_modifiedFlow_le_erdosWeight_of_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : IsPrimePow N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
  classical
  let L : ℝ := Real.log N
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  obtain ⟨p, k, hp, hk, hNpow⟩ := (isPrimePow_nat_iff N).mp hPrimePow
  let qp : {q : ℕ // 2 ≤ q} := ⟨p, hp.two_le⟩
  have hN0_nat : N ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hN)
  have hN_pos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0_nat
  have hN_cast : (1 : ℝ) < N := by
    exact_mod_cast hN
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hN_cast
  have hLne : L ≠ 0 := hLpos.ne'
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have hNp : 1 < N * p := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hp.pos)
  have hNp0_nat : N * p ≠ 0 := Nat.mul_ne_zero hN0_nat hp.ne_zero
  have hNp0 : ((N * p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNp0_nat
  have hNpPow : N * p = p ^ (k + 1) := by
    rw [← hNpow, pow_succ]
  have hbase_one :
      baseFlow (N * p) 1 =
        Real.log p / (((N * p : ℕ) : ℝ) * (L + Real.log p) ^ 2) := by
    have hNp_pp : IsPrimePow (N * p) := by
      rw [hNpPow]
      exact (isPrimePow_pow_iff (Nat.succ_ne_zero _)).2 hp.isPrimePow
    have hvm_Np : ArithmeticFunction.vonMangoldt (N * p) = Real.log p := by
      rw [hNpPow, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hlog_Np : Real.log (N * p) = L + Real.log p := by
      simpa [L, Nat.cast_mul] using
        (Real.log_mul hN0 (Nat.cast_ne_zero.mpr hp.ne_zero))
    rw [baseFlow, if_pos hNp, if_pos (one_dvd _), Nat.div_one, if_pos hNp_pp]
    simp [hvm_Np, hlog_Np]
  have hmodified_eq_base_of_ne_special :
      ∀ K : ℕ, K ≠ N * p → modifiedFlow K N = baseFlow K N := by
    intro K hKne
    have hfirst :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ K = p' ^ k' ∧ N = 1 := by
      rintro ⟨p', hp', k', hk', hKpow, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ K = p' ^ k' ∧ N = p' ^ (k' - 1) := by
      rintro ⟨p', hp', k', hk', hKpow, hNpow'⟩
      have hk'1 : k' - 1 ≠ 0 := by omega
      have hpow_eq : p ^ k = p' ^ (k' - 1) := by
        rw [hNpow, hNpow']
      rcases hp.pow_inj' hp' hk_ne hk'1 hpow_eq with ⟨hpeq, hk_eq⟩
      have hk'_succ : k' = k + 1 := by omega
      have hKeq : K = N * p := by
        calc
          K = p' ^ k' := hKpow
          _ = p ^ (k + 1) := by rw [hpeq, hk'_succ]
          _ = N * p := by rw [pow_succ, hNpow]
      exact hKne hKeq
    simp [modifiedFlow, hfirst, hsecond]
  have hmodified_at_special :
      modifiedFlow (N * p) N = baseFlow (N * p) N + baseFlow (N * p) 1 := by
    have hfirst :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ N * p = p' ^ k' ∧ N = 1 := by
      rintro ⟨p', hp', k', hk', hKpow, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ N * p = p' ^ k' ∧ N = p' ^ (k' - 1) := by
      refine ⟨p, hp, k + 1, by omega, ?_, ?_⟩
      · rw [pow_succ, hNpow]
      · simpa using hNpow.symm
    simp [modifiedFlow, hfirst, hsecond]
  let e : {q : ℕ // 2 ≤ q} → ℕ := fun q => N * q.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Nat.mul_left_cancel hN_pos hab
  have hbase_zero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
    intro K hK
    by_cases hdiv : N ∣ K
    · rcases hdiv with ⟨q, rfl⟩
      by_cases hqge2 : 2 ≤ q
      · exfalso
        exact hK ⟨⟨q, hqge2⟩, rfl⟩
      · have hnotpp : ¬ IsPrimePow q := by
          intro hqpp
          obtain ⟨p', k', hp', hk', hpow⟩ := (isPrimePow_nat_iff q).mp hqpp
          have hk1 : 1 ≤ k' := Nat.succ_le_of_lt hk'
          have h2 : 2 ≤ q := by
            calc
              2 ≤ p' := hp'.two_le
              _ ≤ p' ^ k' := Nat.le_self_pow (show k' ≠ 0 by omega) p'
              _ = q := hpow
          exact hqge2 h2
        by_cases hNq : 1 < N * q
        · simp [baseFlow, hNq, Nat.mul_div_right q hN_pos, hnotpp]
        · simp [baseFlow, hNq]
    · simp [baseFlow, hdiv]
  have hmodified_zero : ∀ K : ℕ, K ∉ Set.range e → modifiedFlow K N = 0 := by
    intro K hK
    have hKne : K ≠ N * p := by
      intro hEq
      exact hK ⟨qp, by simpa [e, qp] using hEq.symm⟩
    simpa [hmodified_eq_base_of_ne_special K hKne] using hbase_zero K hK
  have hbase_mul (q : {q : ℕ // 2 ≤ q}) :
      baseFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hNq : 1 < N * q.1 := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hqnatpos)
    have hdvd : N ∣ N * q.1 := ⟨q.1, by simp⟩
    have hdiv : (N * q.1) / N = q.1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q.1 hN_pos
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    by_cases hqpp : IsPrimePow q.1
    · rw [baseFlow, if_pos hNq, if_pos hdvd]
      have hlog : Real.log (((N * q.1 : ℕ) : ℝ)) = L + Real.log q.1 := by
        simpa [L, Nat.cast_mul] using Real.log_mul hN0' hq0
      exact
        (by
          simpa only [hdiv, hqpp] using
            congrArg
              (fun x =>
                ArithmeticFunction.vonMangoldt q.1 /
                  ((((N * q.1 : ℕ) : ℝ)) * x ^ 2))
              hlog)
    · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact hqpp
      simp [baseFlow, hNq, hdvd, hdiv, hqpp, hvm]
  have hmodified_mul (q : {q : ℕ // 2 ≤ q}) :
      modifiedFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) +
        if q = qp then
          Real.log p / (((N * p : ℕ) : ℝ) * (L + Real.log p) ^ 2)
        else
          0 := by
    by_cases hq : q = qp
    · subst hq
      rw [hmodified_at_special, hbase_mul qp, hbase_one]
      simp [qp]
    · have hKne : N * q.1 ≠ N * p := by
        intro hEq
        apply hq
        apply Subtype.ext
        exact Nat.mul_left_cancel hN_pos hEq
      rw [hmodified_eq_base_of_ne_special (N * q.1) hKne, hbase_mul]
      simp [hq]
  let G : {q : ℕ // 2 ≤ q} → ℝ → ℝ := fun q t =>
    (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) +
        if q = qp then Real.log p / (((N * p : ℕ) : ℝ)) else 0) *
      (t * Real.exp (-((L + Real.log q.1) * t)))
  let fSum : ℝ → ℝ := fun t =>
    (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
      (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
  have hsum_analytic {t : ℝ} (ht : 0 < t) :
      Summable (fun q : {q : ℕ // 2 ≤ q} =>
        ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    let full : ℕ → ℝ := fun n =>
      if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / Real.rpow (n : ℝ) (1 + t)
    have hLs :
        LSeriesSummable (fun n => ↑(ArithmeticFunction.vonMangoldt n)) (1 + t : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using add_lt_add_left ht 1)
    have hsum_full : Summable full := by
      simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hLs.norm
    have hfull_zero :
        ∀ n ∉ Set.range (Subtype.val : {q : ℕ // 2 ≤ q} → ℕ), full n = 0 := by
      intro n hn
      have hnlt2 : n < 2 := by
        by_contra h
        exact hn ⟨⟨n, not_lt.mp h⟩, rfl⟩
      interval_cases n <;> simp [full]
    have hsub : Summable (full ∘ Subtype.val) :=
      (Function.Injective.summable_iff Subtype.val_injective hfull_zero).2 hsum_full
    refine hsub.congr ?_
    intro q
    simp [full, show ((q : ℕ) ≠ 0) by omega]
  have hHas_analytic {t : ℝ} (ht : 0 < t) :
      HasSum
        (fun q : {q : ℕ // 2 ≤ q} =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
        (analyticSeries (1 + t)) := by
    simpa [analyticSeries] using (hsum_analytic ht).hasSum
  have hF_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ))) *
          (t * Real.exp (-((L + Real.log q.1) * t))) =
        ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
          (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log q.1) * t) = -L * t + -(Real.log q.1 * t) by ring, Real.exp_add]
    have hmul : -(Real.log (q.1 : ℝ) * t) = Real.log (q.1 : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hqpos (-t)]
    rw [Real.rpow_neg (le_of_lt hqpos), ← mul_assoc]
    have hrpow : Real.rpow (q.1 : ℝ) (1 + t) = (q.1 : ℝ) * Real.rpow (q.1 : ℝ) t := by
      simpa using (Real.rpow_add hqpos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv, Real.rpow_eq_pow]
    ring_nf
  have hE_term {t : ℝ} (ht : 0 < t) :
      (Real.log p / (((N * p : ℕ) : ℝ))) * (t * Real.exp (-((L + Real.log p) * t))) =
        ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
          (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log p) * t) = -L * t + -(Real.log p * t) by ring, Real.exp_add]
    have hmul : -(Real.log (p : ℝ) * t) = Real.log (p : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hppos (-t)]
    rw [Real.rpow_neg (le_of_lt hppos), ← mul_assoc]
    have hrpow : Real.rpow (p : ℝ) (1 + t) = (p : ℝ) * Real.rpow (p : ℝ) t := by
      simpa using (Real.rpow_add hppos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv, Real.rpow_eq_pow]
    ring_nf
  have hG_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      G q t = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
        (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
          if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0) := by
    by_cases hq : q = qp
    · subst hq
      calc
        G qp t
            = (ArithmeticFunction.vonMangoldt p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) +
              (Real.log p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) := by
                  simp [G, qp, add_mul]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t)) +
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
                rw [hF_term ht qp, hE_term ht]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t) +
                Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
                  rw [← mul_add]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t) +
                if qp = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0) := by
                  simp
    · simpa [G, hq] using hF_term ht q
  have hG_hasSum {t : ℝ} (ht : 0 < t) :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => G q t) (fSum t) := by
    have hcorr :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0)
          (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
      simpa using (hasSum_ite_eq qp (Real.log p / Real.rpow (p : ℝ) (1 + t)))
    have hsum_inner :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
              if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0)
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
      exact (hHas_analytic ht).add hcorr
    have hconst :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
                if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0))
          (((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
            (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))) := by
      simpa [mul_assoc] using
        hsum_inner.mul_left ((1 / (N : ℝ)) * (t * Real.exp (-L * t)))
    convert hconst using 1
    · ext q
      exact hG_term ht q
  have hG_int (q : {q : ℕ // 2 ≤ q}) :
      ∫ t in Set.Ioi (0 : ℝ), G q t = modifiedFlow (N * q.1) N := by
    by_cases hq : q = qp
    · subst hq
      have hb : 0 < L + Real.log p := by
        exact add_pos hLpos (Real.log_pos (by exact_mod_cast hp.one_lt))
      have hkernel :
          ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log p) * t)) =
            (1 / (L + Real.log p)) ^ 2 := by
        have hkernel' :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (1 : ℝ) * Real.exp (-((L + Real.log p) * t)) =
              (1 / (L + Real.log p)) ^ 2 := by
          simpa [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.Gamma_two] using
            (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := L + Real.log p)
              (by norm_num) hb)
        simpa [Real.rpow_one] using hkernel'
      have hGqp :
          G qp =
            fun t : ℝ =>
              (ArithmeticFunction.vonMangoldt p / (((N * p : ℕ) : ℝ)) +
                  Real.log p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) := by
        funext t
        simp [G, qp, add_mul]
      rw [hGqp, MeasureTheory.integral_const_mul, hkernel, hmodified_mul qp, if_pos rfl]
      simp [qp, ArithmeticFunction.vonMangoldt_apply_prime hp, div_eq_mul_inv]
      field_simp [hNp0, hb.ne']
    · have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      have hNq0_nat : N * q.1 ≠ 0 := Nat.mul_ne_zero hN_pos.ne' (Nat.ne_of_gt hqnatpos)
      have hNq0 : (((N * q.1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast hNq0_nat
      have hb : 0 < L + Real.log q.1 := by
        have hqcast : (1 : ℝ) < q.1 := by exact_mod_cast q.2
        exact add_pos hLpos (Real.log_pos hqcast)
      have hkernel :
          ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t)) =
            (1 / (L + Real.log q.1)) ^ 2 := by
        have hkernel' :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (1 : ℝ) * Real.exp (-((L + Real.log q.1) * t)) =
              (1 / (L + Real.log q.1)) ^ 2 := by
          simpa [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.Gamma_two] using
            (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := L + Real.log q.1)
              (by norm_num) hb)
        simpa [Real.rpow_one] using hkernel'
      have hGq :
          G q =
            fun t : ℝ =>
              (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log q.1) * t))) := by
        funext t
        simp [G, hq]
      rw [hGq, MeasureTheory.integral_const_mul, hkernel, hmodified_mul q, if_neg hq]
      simp [div_eq_mul_inv]
      field_simp [hNq0, hb.ne']
  have hG_meas : ∀ q : {q : ℕ // 2 ≤ q}, MeasureTheory.AEStronglyMeasurable (G q) μ := by
    intro q
    dsimp [G]
    fun_prop
  have h_bound :
      ∀ q : {q : ℕ // 2 ≤ q}, ∀ᵐ t : ℝ ∂μ, ‖G q t‖ ≤ G q t := by
    intro q
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hcoeff_nonneg :
        0 ≤ ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) +
          if q = qp then Real.log p / (((N * p : ℕ) : ℝ)) else 0 := by
      apply add_nonneg
      · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        positivity
      · by_cases hq : q = qp
        · subst hq
          have hp_cast : (1 : ℝ) < p := by
            exact_mod_cast hp.one_lt
          split_ifs with h
          · exact div_nonneg
              (Real.log_pos hp_cast).le
              (by positivity : 0 ≤ (((N * p : ℕ) : ℝ)))
          · contradiction
        · simp [hq]
    have hG_nonneg : 0 ≤ G q t := by
      dsimp [G]
      exact mul_nonneg hcoeff_nonneg (mul_nonneg ht.le (le_of_lt (Real.exp_pos _)))
    calc
      ‖G q t‖ = G q t := Real.norm_of_nonneg hG_nonneg
      _ ≤ G q t := le_rfl
  have h_bound_summable :
      ∀ᵐ t : ℝ ∂μ, Summable (fun q : {q : ℕ // 2 ≤ q} => G q t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hG_hasSum ht).summable
  have h_tsum_eq :
      ∀ᵐ t : ℝ ∂μ, (∑' q : {q : ℕ // 2 ≤ q}, G q t) = fSum t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hG_hasSum ht).tsum_eq
  have hanalytic_meas :
      AEMeasurable (fun t : ℝ => analyticSeries (1 + t)) μ := by
    let Aq : {q : ℕ // 2 ≤ q} → ℝ → NNReal := fun q t =>
      Real.toNNReal (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
    have hAq_meas : ∀ q : {q : ℕ // 2 ≤ q}, Measurable (Aq q) := by
      intro q
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (show q.1 ≠ 0 by omega)
      have hpow_meas : Measurable (fun t : ℝ => (q.1 : ℝ) ^ (1 + t)) :=
        ((Real.continuous_const_rpow hq0).comp (continuous_const.add continuous_id)).measurable
      exact (measurable_const.div hpow_meas).real_toNNReal
    have htsum : Measurable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, Aq q t) :=
      Measurable.nnreal_tsum hAq_meas
    refine htsum.coe_nnreal_real.aemeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hnonneg :
        ∀ q : {q : ℕ // 2 ≤ q},
          0 ≤ ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ) ^ (1 + t) := by
      intro q
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hqnatpos) _)
    calc
      ↑(∑' q : {q : ℕ // 2 ≤ q}, Aq q t)
          = ∑' q : {q : ℕ // 2 ≤ q}, (Aq q t : ℝ) := by
              rw [NNReal.coe_tsum]
      _ = ∑' q : {q : ℕ // 2 ≤ q},
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) := by
              refine tsum_congr ?_
              intro q
              dsimp [Aq]
              calc
                (Real.toNNReal
                    (ArithmeticFunction.vonMangoldt q.1 /
                      Real.rpow (q.1 : ℝ) (1 + t)) : ℝ)
                    =
                    max
                      (ArithmeticFunction.vonMangoldt q.1 /
                        Real.rpow (q.1 : ℝ) (1 + t))
                      0 := by
                        exact Real.coe_toNNReal' _
                _ = ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) :=
                  max_eq_left (hnonneg q)
      _ = analyticSeries (1 + t) := by
            exact (hHas_analytic ht).tsum_eq
  have hfSum_meas : AEMeasurable fSum μ := by
    have hfactor_meas :
        AEMeasurable (fun t : ℝ => (1 / (N : ℝ)) * (t * Real.exp (-L * t))) μ := by
      fun_prop
    have hcorr_meas :
        AEMeasurable (fun t : ℝ => Real.log p / Real.rpow (p : ℝ) (1 + t)) μ := by
      have hpow_cont : Continuous (fun t : ℝ => Real.rpow (p : ℝ) (1 + t)) :=
        (Real.continuous_const_rpow (Nat.cast_ne_zero.mpr hp.ne_zero)).comp
          (continuous_const.add continuous_id)
      exact (continuous_const.div hpow_cont
        (fun t => (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne')).aemeasurable
    simpa [fSum] using hfactor_meas.mul (hanalytic_meas.add hcorr_meas)
  have hsimple_int :
      MeasureTheory.Integrable (fun t : ℝ => (1 / (N : ℝ)) * Real.exp (-L * t)) μ := by
    simpa [μ, MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (exp_neg_integrableOn_Ioi 0 hLpos).const_mul (1 / (N : ℝ))
  have hfSum_bound :
      ∀ᵐ t : ℝ ∂μ, ‖fSum t‖ ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log p / Real.rpow (p : ℝ) (1 + t) := by
      exact div_nonneg
        (Real.log_pos (by exact_mod_cast hp.one_lt)).le
        (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _))
    have hA_le :
        analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t) ≤ 1 / t := by
      have ht' : 1 < 1 + t := by linarith
      convert analyticSeries_add_log_term_le ht' hp using 1
      · ring_nf
    have hf_nonneg : 0 ≤ fSum t := by
      dsimp [fSum]
      exact mul_nonneg
        (by positivity)
        (add_nonneg hA_nonneg hcorr_nonneg)
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_le :
      ∀ᵐ t : ℝ ∂μ, fSum t ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log p / Real.rpow (p : ℝ) (1 + t) := by
      exact div_nonneg
        (Real.log_pos (by exact_mod_cast hp.one_lt)).le
        (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _))
    have hA_le :
        analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t) ≤ 1 / t := by
      have ht' : 1 < 1 + t := by linarith
      convert analyticSeries_add_log_term_le ht' hp using 1
      · ring_nf
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_int : MeasureTheory.Integrable fSum μ :=
    hsimple_int.mono' hfSum_meas.aestronglyMeasurable hfSum_bound
  have h_tsum_eq_ae :
      (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, G q t) =ᵐ[μ] fSum := h_tsum_eq
  have h_bound_integrable :
      MeasureTheory.Integrable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, G q t) μ :=
    hfSum_int.congr h_tsum_eq_ae.symm
  have h_hasSum_ae :
      ∀ᵐ t : ℝ ∂μ, HasSum (fun q : {q : ℕ // 2 ≤ q} => G q t) (fSum t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hG_hasSum ht
  have hIntHasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => ∫ t, G q t ∂μ) (∫ t, fSum t ∂μ) :=
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (bound := G) hG_meas h_bound h_bound_summable h_bound_integrable h_hasSum_ae
  have hsub_hasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => modifiedFlow (N * q.1) N) (∫ t, fSum t ∂μ) := by
    exact hIntHasSum.congr_fun fun q => (hG_int q).symm
  have hmodified_hasSum :
      HasSum (fun K : ℕ => modifiedFlow K N) (∫ t, fSum t ∂μ) :=
    (Function.Injective.hasSum_iff he hmodified_zero).mp hsub_hasSum
  have hinflow_modified :
      inflow modifiedFlow N = ∫ t, fSum t ∂μ := by
    simpa [inflow] using hmodified_hasSum.tsum_eq
  have hsimple_integral :
      ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ = erdosWeight N := by
    calc
      ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ
          = (1 / (N : ℝ)) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-L * t) := by
              simp [μ, MeasureTheory.integral_const_mul]
      _ = (1 / (N : ℝ)) * (1 / L) := by
            congr 1
            calc
              ∫ t in Set.Ioi (0 : ℝ), Real.exp (-L * t)
                  = L ^ (-1 / (1 : ℝ)) * Real.Gamma (1 / (1 : ℝ) + 1) := by
                      simpa [Real.rpow_one] using
                        (integral_exp_neg_mul_rpow (p := 1) zero_lt_one hLpos)
              _ = 1 / L := by
                    have htwo : ((1 / (1 : ℝ)) + 1) = 2 := by norm_num
                    have hnegone : ((-1 : ℝ) / (1 : ℝ)) = -(1 : ℝ) := by norm_num
                    rw [htwo, Real.Gamma_two]
                    rw [hnegone, Real.rpow_neg (le_of_lt hLpos),
                      Real.rpow_one, inv_eq_one_div]
                    ring
      _ = erdosWeight N := by
            simp [erdosWeight, L]
            field_simp [hN0, hLne]
  have hfinal_integral :
      ∫ t, fSum t ∂μ ≤ erdosWeight N := by
    calc
      ∫ t, fSum t ∂μ ≤ ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ := by
        exact MeasureTheory.integral_mono_ae hfSum_int hsimple_int hfSum_le
      _ = erdosWeight N := hsimple_integral
  calc
    inflow modifiedFlow N = ∫ t, fSum t ∂μ := hinflow_modified
    _ ≤ erdosWeight N := hfinal_integral

lemma inflow_modifiedFlow_le_erdosWeight_of_not_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : ¬ IsPrimePow N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
  classical
  let L : ℝ := Real.log N
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hN0_nat : N ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hN)
  have hN_pos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0_nat
  have hN_cast : (1 : ℝ) < N := by
    exact_mod_cast hN
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hN_cast
  have hLne : L ≠ 0 := hLpos.ne'
  have hmodified_eq_base : ∀ K : ℕ, modifiedFlow K N = baseFlow K N := by
    intro K
    rw [modifiedFlow]
    have hfirst :
        ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ K = p ^ x ∧ N = 1 := by
      rintro ⟨p, hp, x, hx, hK, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ K = p ^ x ∧ N = p ^ (x - 1) := by
      rintro ⟨p, hp, x, hx, hK, hNpow⟩
      have hk1 : x - 1 ≠ 0 := by omega
      exact hPrimePow <| hNpow.symm ▸ (isPrimePow_pow_iff hk1).2 hp.isPrimePow
    simp [hfirst, hsecond]
  let e : {q : ℕ // 2 ≤ q} → ℕ := fun q => N * q.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Nat.mul_left_cancel hN_pos hab
  have hbase_zero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
    intro K hK
    by_cases hdiv : N ∣ K
    · rcases hdiv with ⟨q, rfl⟩
      by_cases hqge2 : 2 ≤ q
      · exfalso
        exact hK ⟨⟨q, hqge2⟩, rfl⟩
      · have hnotpp : ¬ IsPrimePow q := by
          intro hqpp
          exact hqge2 <| Nat.succ_le_of_lt <| IsPrimePow.one_lt hqpp
        by_cases hNq : 1 < N * q
        · simp [baseFlow, hNq, Nat.mul_div_right q hN_pos, hnotpp]
        · simp [baseFlow, hNq]
    · simp [baseFlow, hdiv]
  have hbase_mul (q : {q : ℕ // 2 ≤ q}) :
      baseFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hNq : 1 < N * q.1 := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hqnatpos)
    have hdvd : N ∣ N * q.1 := ⟨q.1, by simp⟩
    have hdiv : (N * q.1) / N = q.1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q.1 hN_pos
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    by_cases hqpp : IsPrimePow q.1
    · rw [baseFlow, if_pos hNq, if_pos hdvd]
      have hlog : Real.log (((N * q.1 : ℕ) : ℝ)) = L + Real.log q.1 := by
        simpa [L, Nat.cast_mul] using Real.log_mul hN0' hq0
      exact
        (by
          simpa only [hdiv, hqpp] using
            congrArg
              (fun x =>
                ArithmeticFunction.vonMangoldt q.1 /
                  ((((N * q.1 : ℕ) : ℝ)) * x ^ 2))
              hlog)
    · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact hqpp
      simp [baseFlow, hNq, hdvd, hdiv, hqpp, hvm]
  let F : {q : ℕ // 2 ≤ q} → ℝ → ℝ := fun q t =>
    ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
      (t * Real.exp (-((L + Real.log q.1) * t)))
  let fSum : ℝ → ℝ := fun t =>
    (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * analyticSeries (1 + t)
  have hsum_analytic {t : ℝ} (ht : 0 < t) :
      Summable (fun q : {q : ℕ // 2 ≤ q} =>
        ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    let full : ℕ → ℝ := fun n =>
      if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / Real.rpow (n : ℝ) (1 + t)
    have hLs :
        LSeriesSummable (fun n => ↑(ArithmeticFunction.vonMangoldt n)) (1 + t : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using add_lt_add_left ht 1)
    have hsum_full : Summable full := by
      simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hLs.norm
    have hfull_zero :
        ∀ n ∉ Set.range (Subtype.val : {q : ℕ // 2 ≤ q} → ℕ), full n = 0 := by
      intro n hn
      have hnlt2 : n < 2 := by
        by_contra h
        exact hn ⟨⟨n, not_lt.mp h⟩, rfl⟩
      interval_cases n <;> simp [full]
    have hsub : Summable (full ∘ Subtype.val) :=
      (Function.Injective.summable_iff Subtype.val_injective hfull_zero).2 hsum_full
    refine hsub.congr ?_
    intro q
    simp [full, show ((q : ℕ) ≠ 0) by omega]
  have hHas_analytic {t : ℝ} (ht : 0 < t) :
      HasSum
        (fun q : {q : ℕ // 2 ≤ q} =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
        (analyticSeries (1 + t)) := by
    simpa [analyticSeries] using (hsum_analytic ht).hasSum
  have hF_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      F q t = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
        (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    dsimp [F]
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log q.1) * t) = -L * t + -(Real.log q.1 * t) by ring, Real.exp_add]
    have hmul : -(Real.log (q.1 : ℝ) * t) = Real.log (q.1 : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hqpos (-t)]
    rw [Real.rpow_neg (le_of_lt hqpos), ← mul_assoc]
    have hrpow : (q.1 : ℝ) ^ (1 + t) = (q.1 : ℝ) * (q.1 : ℝ) ^ t := by
      simpa using (Real.rpow_add hqpos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv]
    field_simp [hN0, hqpos.ne', (Real.rpow_pos_of_pos hqpos t).ne']
  have hF_hasSum {t : ℝ} (ht : 0 < t) :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => F q t) (fSum t) := by
    have hconst :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)))
          (((1 / (N : ℝ)) * (t * Real.exp (-L * t))) * analyticSeries (1 + t)) := by
      simpa [mul_assoc] using
        (hHas_analytic ht).mul_left ((1 / (N : ℝ)) * (t * Real.exp (-L * t)))
    exact hconst.congr_fun fun q => hF_term ht q
  have hF_int (q : {q : ℕ // 2 ≤ q}) :
      ∫ t in Set.Ioi (0 : ℝ), F q t =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    have hqgt1 : (1 : ℝ) < q.1 := by
      have hqge2 : (2 : ℝ) ≤ q.1 := by exact_mod_cast q.2
      linarith
    have hb : 0 < L + Real.log q.1 := by
      exact add_pos hLpos (Real.log_pos hqgt1)
    calc
      ∫ t in Set.Ioi (0 : ℝ), F q t
          = ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
              ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t)) := by
                simp [F, MeasureTheory.integral_const_mul]
      _ = ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
            (L + Real.log q.1) ^ (-2 : ℝ) := by
              congr 1
              calc
                ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t))
                    = (L + Real.log q.1) ^ (-(1 + 1) / (1 : ℝ)) *
                        (1 / (1 : ℝ)) * Real.Gamma ((1 + 1) / (1 : ℝ)) := by
                          convert
                            (integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1)
                              zero_lt_one (by norm_num) hb) using 1
                          · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                            intro t ht
                            have hlin : -((L + Real.log q.1) * t) = (-Real.log q.1 + -L) * t := by
                              ring
                            simp [hlin]
                _ = (L + Real.log q.1) ^ (-2 : ℝ) := by
                      have htwo : ((1 + 1 : ℝ) / (1 : ℝ)) = 2 := by norm_num
                      rw [htwo, Real.Gamma_two]
                      norm_num
      _ = ArithmeticFunction.vonMangoldt q.1 /
            (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
              have hNq0 : (((N * q.1 : ℕ) : ℝ)) ≠ 0 := by
                exact_mod_cast (Nat.mul_pos hN_pos hqnatpos).ne'
              rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hb)]
              field_simp [hNq0, hb.ne']
              have hsquare :
                  (L + Real.log q.1) ^ 2 =
                    L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2 := by
                ring
              have hsquareR :
                  (L + Real.log q.1) ^ (2 : ℝ) =
                    L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2 := by
                simpa [Real.rpow_natCast] using hsquare
              have haux :
                ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                    ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                    ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                    = ArithmeticFunction.vonMangoldt q.1 *
                      (L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2) := by
                        ring
              have hcalc :
                ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                    ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                    ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                    = ArithmeticFunction.vonMangoldt q.1 * (L + Real.log q.1) ^ (2 : ℝ) := by
                      calc
                        ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                            ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                            ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                            = ArithmeticFunction.vonMangoldt q.1 *
                              (L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2) := haux
                        _ = ArithmeticFunction.vonMangoldt q.1 * (L + Real.log q.1) ^ (2 : ℝ) := by
                              rw [hsquareR]
              simp
  have hF_meas : ∀ q : {q : ℕ // 2 ≤ q}, MeasureTheory.AEStronglyMeasurable (F q) μ := by
    intro q
    dsimp [F]
    fun_prop
  have h_bound :
      ∀ q : {q : ℕ // 2 ≤ q}, ∀ᵐ t : ℝ ∂μ, ‖F q t‖ ≤ F q t := by
    intro q
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hF_nonneg : 0 ≤ F q t := by
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      dsimp [F]
      apply mul_nonneg
      · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        positivity
      · exact mul_nonneg ht.le (le_of_lt (Real.exp_pos _))
    simp [Real.norm_eq_abs, abs_of_nonneg hF_nonneg]
  have h_bound_summable :
      ∀ᵐ t : ℝ ∂μ, Summable (fun q : {q : ℕ // 2 ≤ q} => F q t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hF_hasSum ht).summable
  have h_hasSum_ae :
      ∀ᵐ t : ℝ ∂μ, HasSum (fun q : {q : ℕ // 2 ≤ q} => F q t) (fSum t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hF_hasSum ht
  have h_tsum_eq :
      ∀ᵐ t : ℝ ∂μ, (∑' q : {q : ℕ // 2 ≤ q}, F q t) = fSum t := by
    filter_upwards [h_hasSum_ae] with t ht
    exact ht.tsum_eq
  have hanalytic_meas :
      AEMeasurable (fun t : ℝ => analyticSeries (1 + t)) μ := by
    let Aq : {q : ℕ // 2 ≤ q} → ℝ → NNReal := fun q t =>
      Real.toNNReal (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
    have hAq_meas : ∀ q : {q : ℕ // 2 ≤ q}, Measurable (Aq q) := by
      intro q
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (show q.1 ≠ 0 by omega)
      have hpow_meas : Measurable (fun t : ℝ => (q.1 : ℝ) ^ (1 + t)) :=
        ((Real.continuous_const_rpow hq0).comp (continuous_const.add continuous_id)).measurable
      exact (measurable_const.div hpow_meas).real_toNNReal
    have htsum : Measurable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, Aq q t) :=
      Measurable.nnreal_tsum hAq_meas
    refine htsum.coe_nnreal_real.aemeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hnonneg :
        ∀ q : {q : ℕ // 2 ≤ q},
          0 ≤ ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ) ^ (1 + t) := by
      intro q
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hqnatpos) _)
    calc
      ↑(∑' q : {q : ℕ // 2 ≤ q}, Aq q t)
          = ∑' q : {q : ℕ // 2 ≤ q}, (Aq q t : ℝ) := by
              rw [NNReal.coe_tsum]
      _ = ∑' q : {q : ℕ // 2 ≤ q},
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) := by
              refine tsum_congr ?_
              intro q
              dsimp [Aq]
              simp [max_eq_left (hnonneg q)]
      _ = analyticSeries (1 + t) := by
            simp [analyticSeries]
  have hfSum_meas : AEMeasurable fSum μ := by
    have hfactor_meas : AEMeasurable (fun t : ℝ => (1 / (N : ℝ)) * (t * Real.exp (-L * t))) μ := by
      fun_prop
    simpa [fSum] using hfactor_meas.mul hanalytic_meas
  have hsimple_int :
      MeasureTheory.Integrable (fun t : ℝ => (1 / (N : ℝ)) * Real.exp (-L * t)) μ := by
    simpa [μ, MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (exp_neg_integrableOn_Ioi 0 hLpos).const_mul (1 / (N : ℝ))
  have hfSum_bound :
      ∀ᵐ t : ℝ ∂μ, ‖fSum t‖ ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
      have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      exact div_nonneg hlog2.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    have hA_le : analyticSeries (1 + t) ≤ 1 / t := by
      have hs : 1 < 1 + t := by linarith
      have hmain :
          analyticSeries (1 + t) + Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) ≤ 1 / t := by
        simpa using (analyticSeries_add_log_term_le hs Nat.prime_two)
      calc
        analyticSeries (1 + t)
            ≤ analyticSeries (1 + t) + Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
              linarith
        _ ≤ 1 / t := hmain
    have hf_nonneg : 0 ≤ fSum t := by
      dsimp [fSum]
      exact mul_nonneg
        (by positivity)
        hA_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * analyticSeries (1 + t)
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_int : MeasureTheory.Integrable fSum μ :=
    hsimple_int.mono' hfSum_meas.aestronglyMeasurable hfSum_bound
  have h_bound_integrable :
      MeasureTheory.Integrable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, F q t) μ :=
    hfSum_int.congr (h_tsum_eq.mono fun t ht => ht.symm)
  have hIntHasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => ∫ t, F q t ∂μ) (∫ t, fSum t ∂μ) :=
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (bound := F) hF_meas h_bound h_bound_summable h_bound_integrable h_hasSum_ae
  have hsub_hasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => baseFlow (N * q.1) N) (∫ t, fSum t ∂μ) := by
    exact hIntHasSum.congr_fun fun q => (hbase_mul q).trans (hF_int q).symm
  have hbase_hasSum :
      HasSum (fun K : ℕ => baseFlow K N) (∫ t, fSum t ∂μ) :=
    (Function.Injective.hasSum_iff he hbase_zero).mp hsub_hasSum
  have hinflow_base :
      inflow baseFlow N = ∫ t, fSum t ∂μ := by
    simpa [inflow] using hbase_hasSum.tsum_eq
  have hsimple_integral :
      ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ = erdosWeight N := by
    calc
      ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ
          = (1 / (N : ℝ)) * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-L * t) := by
              simp [μ, MeasureTheory.integral_const_mul]
      _ = (1 / (N : ℝ)) * (1 / L) := by
            congr 1
            calc
              ∫ t in Set.Ioi (0 : ℝ), Real.exp (-L * t)
                  = L ^ (-1 / (1 : ℝ)) * Real.Gamma (1 / (1 : ℝ) + 1) := by
                      simpa [Real.rpow_one] using
                        (integral_exp_neg_mul_rpow (p := 1) zero_lt_one hLpos)
              _ = 1 / L := by
                    have htwo : ((1 / (1 : ℝ)) + 1) = 2 := by norm_num
                    have hnegone : ((-1 : ℝ) / (1 : ℝ)) = -(1 : ℝ) := by norm_num
                    rw [htwo, Real.Gamma_two]
                    rw [hnegone, Real.rpow_neg (le_of_lt hLpos),
                      Real.rpow_one, inv_eq_one_div]
                    ring
      _ = erdosWeight N := by
            simp [erdosWeight, L]
            field_simp [hN0, hLne]
  have hfSum_le :
      fSum ≤ᵐ[μ] fun t : ℝ => (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [hfSum_bound] with t ht
    exact le_trans (le_abs_self _) ht
  have hfinal_integral :
      ∫ t, fSum t ∂μ ≤ erdosWeight N := by
    calc
      ∫ t, fSum t ∂μ ≤ ∫ t, ((1 / (N : ℝ)) * Real.exp (-L * t)) ∂μ := by
        exact MeasureTheory.integral_mono_ae hfSum_int hsimple_int hfSum_le
      _ = erdosWeight N := hsimple_integral
  calc
    inflow modifiedFlow N = inflow baseFlow N := by
      simp [inflow, hmodified_eq_base]
    _ = ∫ t, fSum t ∂μ := hinflow_base
    _ ≤ erdosWeight N := hfinal_integral

lemma inflow_modifiedFlow_le_erdosWeight {N : ℕ} (hN : 1 < N) :
    inflow modifiedFlow N ≤ erdosWeight N := by
  by_cases hPrimePow : IsPrimePow N
  · exact inflow_modifiedFlow_le_erdosWeight_of_isPrimePow hN hPrimePow
  · exact inflow_modifiedFlow_le_erdosWeight_of_not_isPrimePow hN hPrimePow

theorem outflow_modifiedFlow_ge_inflow_modifiedFlow {N : ℕ} (hN : 1 < N) :
    inflow modifiedFlow N ≤ outflow modifiedFlow N := by
  simpa [outflow_modifiedFlow_eq_erdosWeight hN] using
    (inflow_modifiedFlow_le_erdosWeight (N := N) hN)

theorem modifiedFlow_to_one_pos_iff_prime {N : ℕ} (hN : 1 < N) :
    0 < modifiedFlow N 1 ↔ N.Prime := by
  classical
  constructor
  · intro hpos
    have hpow2 : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k := by
      intro h
      have hbranch : ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rcases h with ⟨p, k, hp, hk, hNk⟩
        exact ⟨p, hp, k, hk, hNk⟩
      have hzero : modifiedFlow N 1 = 0 := by
        unfold modifiedFlow
        simp [hbranch]
      simp [hzero] at hpos
    have hpow2' : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ 1 = p ^ (k - 1) := by
      rintro ⟨p, k, hp, hk, hNk, _⟩
      exact hpow2 ⟨p, k, hp, hk, hNk⟩
    have hbase : 0 < baseFlow N 1 := by
      have hbranch : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rintro ⟨p, hp, k, hk, hNk⟩
        exact hpow2 ⟨p, k, hp, hk, hNk⟩
      have hbranch' : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x ∧ 1 = p ^ (x - 1) := by
        rintro ⟨p, hp, k, hk, hNk, hk1⟩
        exact hpow2' ⟨p, k, hp, hk, hNk, hk1⟩
      have hmf : modifiedFlow N 1 = baseFlow N 1 := by
        unfold modifiedFlow
        simp [hbranch, hbranch']
      rwa [hmf] at hpos
    have hPrimePow : IsPrimePow N := by
      by_contra hPrimePow
      have hzero : baseFlow N 1 = 0 := by
        simp only [baseFlow, if_pos hN, if_pos (one_dvd N), Nat.div_one, if_neg hPrimePow]
      simp [hzero] at hbase
    obtain ⟨p, k, hp, hk, hkpow⟩ := (isPrimePow_nat_iff N).mp hPrimePow
    have hk_not_ge_two : ¬ 2 ≤ k := by
      intro hk2
      exact hpow2 ⟨p, k, hp, hk2, hkpow.symm⟩
    have hk1 : k = 1 := by
      omega
    have hNp : N = p := by
      simpa [hk1] using hkpow.symm
    simpa [hNp] using hp
  · intro hprime
    have hpow2 : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k := by
      rintro ⟨p, k, hp, hk, hNk⟩
      exact (Nat.Prime.not_prime_pow (x := p) hk) (by simpa [hNk] using hprime)
    have hpow2' : ¬ ∃ p k : ℕ, p.Prime ∧ 2 ≤ k ∧ N = p ^ k ∧ 1 = p ^ (k - 1) := by
      rintro ⟨p, k, hp, hk, hNk, _⟩
      exact hpow2 ⟨p, k, hp, hk, hNk⟩
    have hmf : modifiedFlow N 1 = baseFlow N 1 := by
      have hbranch : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x := by
        rintro ⟨p, hp, k, hk, hNk⟩
        exact hpow2 ⟨p, k, hp, hk, hNk⟩
      have hbranch' : ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ N = p ^ x ∧ 1 = p ^ (x - 1) := by
        rintro ⟨p, hp, k, hk, hNk, hk1⟩
        exact hpow2' ⟨p, k, hp, hk, hNk, hk1⟩
      unfold modifiedFlow
      simp [hbranch, hbranch']
    have hlog : 0 < Real.log N := by
      exact Real.log_pos (Nat.one_lt_cast.2 hN)
    have hden : 0 < (N : ℝ) * (Real.log N) ^ 2 := by
      refine mul_pos ?_ ?_
      · exact Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one hN)
      · exact sq_pos_of_pos hlog
    have hnum : 0 < ArithmeticFunction.vonMangoldt N := by
      rw [ArithmeticFunction.vonMangoldt_apply_prime hprime]
      exact hlog
    have hbase : 0 < baseFlow N 1 := by
      rw [baseFlow, if_pos hN, if_pos (one_dvd N), Nat.div_one, if_pos hprime.isPrimePow]
      exact div_pos hnum hden
    rwa [hmf]

def primeSet : Set ℕ :=
  { p | p.Prime }

def PrimitiveSet (A : Set ℕ) : Prop :=
  (∀ ⦃a : ℕ⦄, a ∈ A → 2 ≤ a) ∧
    ∀ ⦃a b : ℕ⦄, a ∈ A → b ∈ A → a ∣ b → a = b

def DivisibilityFlow (W : ℕ → ℕ → ℝ) : Prop :=
  (∀ m n, 0 ≤ W m n) ∧
    ∀ m n, ¬ (n ∣ m ∧ n < m) → W m n = 0

def SatisfiesFlowConjecture (W : ℕ → ℕ → ℝ) : Prop :=
  DivisibilityFlow W ∧
    (∀ r : ℕ, 2 ≤ r → erdosWeight r ≤ outflow W r) ∧
    (∀ p : ℕ, p.Prime → outflow W p = erdosWeight p) ∧
    (∀ r : ℕ, 2 ≤ r → inflow W r ≤ outflow W r) ∧
    (∀ m : ℕ, 2 ≤ m → ¬ m.Prime → W m 1 = 0)

theorem modifiedFlow_satisfies_flow_conjecture :
    SatisfiesFlowConjecture modifiedFlow := by
  classical
  have hbase_nonneg : ∀ m n : ℕ, 0 ≤ baseFlow m n := by
    intro m n
    by_cases hm : 1 < m
    · by_cases hdiv : n ∣ m
      · by_cases hpow : IsPrimePow (m / n)
        · rw [baseFlow, if_pos hm, if_pos hdiv, if_pos hpow]
          have hm0 : 0 < (m : ℝ) := by
            exact_mod_cast (lt_trans Nat.zero_lt_one hm)
          have hlog : 0 < Real.log m := by
            exact Real.log_pos (by exact_mod_cast hm)
          refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
          exact le_of_lt (mul_pos hm0 (sq_pos_of_pos hlog))
        · rw [baseFlow, if_pos hm, if_pos hdiv, if_neg hpow]
      · rw [baseFlow, if_pos hm, if_neg hdiv]
    · rw [baseFlow, if_neg hm]
  have hbase_support : ∀ m n : ℕ, ¬ (n ∣ m ∧ n < m) → baseFlow m n = 0 := by
    intro m n hmn
    unfold baseFlow
    by_cases hm : 1 < m
    · by_cases hdiv : n ∣ m
      · by_cases hpow : IsPrimePow (m / n)
        · exfalso
          apply hmn
          refine ⟨hdiv, ?_⟩
          have hm0 : 0 < m := lt_trans Nat.zero_lt_one hm
          have hn0 : 0 < n := Nat.pos_of_dvd_of_pos hdiv hm0
          have hq : 1 < m / n := IsPrimePow.one_lt hpow
          have hlt : n * 1 < n * (m / n) := Nat.mul_lt_mul_of_pos_left hq hn0
          simpa [Nat.mul_div_cancel' hdiv] using hlt
        · simp [hm, hdiv, hpow]
      · simp [hm, hdiv]
    · simp [hm]
  have hmodified_nonneg : ∀ m n : ℕ, 0 ≤ modifiedFlow m n := by
    intro m n
    unfold modifiedFlow
    split_ifs with h1 h2
    · simp
    · exact add_nonneg (hbase_nonneg m n) (hbase_nonneg m 1)
    · exact hbase_nonneg m n
  have hmodified_support : ∀ m n : ℕ, ¬ (n ∣ m ∧ n < m) → modifiedFlow m n = 0 := by
    intro m n hmn
    unfold modifiedFlow
    split_ifs with h1 h2
    · rfl
    · exfalso
      apply hmn
      rcases h2 with ⟨p, k, hp, hk, rfl, rfl⟩
      refine ⟨pow_dvd_pow p (Nat.sub_le _ _), ?_⟩
      have hklt : k - 1 < k := by
        omega
      exact Nat.pow_lt_pow_right hp.one_lt hklt
    · exact hbase_support m n hmn
  have h12 : 1 < 2 := by decide
  refine ⟨⟨hmodified_nonneg, hmodified_support⟩, ?_, ?_, ?_, ?_⟩
  · intro r hr
    have hr' : 1 < r := lt_of_lt_of_le h12 hr
    exact le_of_eq (outflow_modifiedFlow_eq_erdosWeight hr').symm
  · intro p hp
    exact outflow_modifiedFlow_eq_erdosWeight hp.one_lt
  · intro r hr
    exact outflow_modifiedFlow_ge_inflow_modifiedFlow (lt_of_lt_of_le h12 hr)
  · intro m hm hnotprime
    have hm' : 1 < m := lt_of_lt_of_le h12 hm
    have hnotpos : ¬ 0 < modifiedFlow m 1 := by
      intro hpos
      exact hnotprime ((modifiedFlow_to_one_pos_iff_prime hm').1 hpos)
    exact le_antisymm (le_of_not_gt hnotpos) (hmodified_nonneg m 1)

noncomputable def primitiveWeightSum (A : Set ℕ) : ℝ :=
  ∑' a : A, erdosWeight (a : ℕ)

noncomputable def primeWeightSum : ℝ :=
  primitiveWeightSum primeSet

def primitiveDivisorClosure (A : Set ℕ) : Set ℕ :=
  { d | 2 ≤ d ∧ ∃ a ∈ A, d ∣ a }

def boundaryOutPairs (Ω : Set ℕ) : Set (ℕ × ℕ) :=
  { mn | mn.1 ∈ Ω ∧ mn.2 ∉ Ω ∧ mn.2 ∣ mn.1 ∧ mn.2 < mn.1 }

def boundaryInPairs (Ω : Set ℕ) : Set (ℕ × ℕ) :=
  { mn | mn.1 ∉ Ω ∧ mn.2 ∈ Ω ∧ mn.2 ∣ mn.1 ∧ mn.2 < mn.1 }

noncomputable def boundaryOutflow (W : ℕ → ℕ → ℝ) (Ω : Set ℕ) : ℝ :=
  ∑' mn : boundaryOutPairs Ω, W mn.1.1 mn.1.2

noncomputable def boundaryInflow (W : ℕ → ℕ → ℝ) (Ω : Set ℕ) : ℝ :=
  ∑' mn : boundaryInPairs Ω, W mn.1.1 mn.1.2

open Filter Asymptotics MeasureTheory
open scoped Nat.Prime

def shiftedPrimeIndicator (n : ℕ) : ℝ :=
  if (n + 1).Prime then 1 else 0

def shiftedPrimeWeightReal (x : ℝ) : ℝ :=
  (((x + 1) * Real.log (x + 1))⁻¹)

def shiftedPrimeWeightDeriv (x : ℝ) : ℝ :=
  ((((x + 1) * Real.log (x + 1)) ^ 2)⁻¹ * (-1 - Real.log (x + 1)))

def shiftedPrimeWeightBound (t : ℝ) : ℝ :=
  1 / ((t + 1) * Real.log (t + 1) ^ 2)

lemma sum_shiftedPrimeIndicator_le_primeCounting (n : ℕ) :
    ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ ≤ (π (n + 1) : ℝ) := by
  classical
  let s : Finset ℕ := (Finset.Icc 1 n).filter fun k => (k + 1).Prime
  have hs' : ∀ k : ℕ, ‖shiftedPrimeIndicator k‖ = if (k + 1).Prime then (1 : ℝ) else 0 := by
    intro k
    by_cases hk : (k + 1).Prime <;> simp [shiftedPrimeIndicator, hk]
  have hs : ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ = (s.card : ℝ) := by
    rw [show (fun k : ℕ => ‖shiftedPrimeIndicator k‖) =
      fun k => if (k + 1).Prime then (1 : ℝ) else 0 from funext hs']
    simp [s]
  have hsub : s.image (fun k => k + 1) ⊆ (n + 2).primesBelow := by
    intro p hp
    rcases Finset.mem_image.mp hp with ⟨k, hk, rfl⟩
    have hk_mem : k ∈ Finset.Icc 1 n := (Finset.mem_filter.mp hk).1
    have hkprime : (k + 1).Prime := (Finset.mem_filter.mp hk).2
    rw [Nat.mem_primesBelow]
    constructor
    · have hk_le : k ≤ n := (Finset.mem_Icc.mp hk_mem).2
      omega
    · exact hkprime
  have hcard_nat : s.card ≤ ((n + 2).primesBelow).card := by
    calc
      s.card = (s.image (fun k => k + 1)).card := by
        symm
        exact Finset.card_image_of_injective s (fun a b h => Nat.succ.inj (by simpa using h))
      _ ≤ ((n + 2).primesBelow).card := Finset.card_le_card hsub
  calc
    ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ = (s.card : ℝ) := hs
    _ ≤ (((n + 2).primesBelow).card : ℝ) := by exact_mod_cast hcard_nat
    _ = (π (n + 1) : ℝ) := by
      rw [Nat.primesBelow_card_eq_primeCounting']
      norm_num [Nat.primeCounting]

lemma hasDerivAt_norm_shiftedPrimeWeight {x : ℝ} (hx : 1 ≤ x) :
    HasDerivAt (fun t => ‖shiftedPrimeWeightReal t‖) (shiftedPrimeWeightDeriv x) x := by
  have hx1 : x + 1 ≠ 0 := by
    have : 0 < x + 1 := by linarith
    linarith
  have hlog : Real.log (x + 1) ≠ 0 := by
    have hpos : 0 < Real.log (x + 1) := by
      apply Real.log_pos
      linarith
    linarith
  have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := by
    simpa using (hasDerivAt_id x).add_const (1 : ℝ)
  have hlog' : HasDerivAt (fun y : ℝ => Real.log (y + 1)) ((x + 1)⁻¹) x := by
    simpa using (Real.hasDerivAt_log hx1).comp x h1
  have hmul0 := h1.mul hlog'
  have hmul_val :
      Real.log (x + 1) + (x + 1) * (x + 1)⁻¹ = Real.log (x + 1) + 1 := by
    field_simp [hx1]
  have hmul :
      HasDerivAt (fun y : ℝ => (y + 1) * Real.log (y + 1))
        (Real.log (x + 1) + 1) x := by
    simpa [hmul_val, mul_comm, mul_left_comm, mul_assoc] using hmul0
  have hderiv :
      HasDerivAt shiftedPrimeWeightReal (shiftedPrimeWeightDeriv x) x := by
    simpa [shiftedPrimeWeightReal, shiftedPrimeWeightDeriv, mul_comm, mul_left_comm, mul_assoc]
      using hmul.inv (mul_ne_zero hx1 hlog)
  have hpos_eventually : ∀ᶠ y in nhds x, 0 < shiftedPrimeWeightReal y := by
    have hgt : ∀ᶠ y in nhds x, 0 < y := Ioi_mem_nhds (show (0 : ℝ) < x by linarith)
    filter_upwards [hgt] with y hy
    have hylog : 0 < Real.log (y + 1) := Real.log_pos (by linarith)
    have hyden : 0 < (y + 1) * Real.log (y + 1) := by positivity
    simpa [shiftedPrimeWeightReal] using inv_pos.mpr hyden
  have heq : (fun t => ‖shiftedPrimeWeightReal t‖) =ᶠ[nhds x] shiftedPrimeWeightReal := by
    filter_upwards [hpos_eventually] with y hy
    simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hy)]
  rw [heq.hasDerivAt_iff]
  exact hderiv

lemma locallyIntegrable_deriv_norm_shiftedPrimeWeight :
    LocallyIntegrableOn (deriv (fun t => ‖shiftedPrimeWeightReal t‖)) (Set.Ici 1) := by
  have hcont : ContinuousOn shiftedPrimeWeightDeriv (Set.Ici 1) := by
    intro x hx
    have hx' : 1 ≤ x := hx
    have hx1 : x + 1 ≠ 0 := by
      have : 0 < x + 1 := by linarith
      linarith
    have hlog : Real.log (x + 1) ≠ 0 := by
      have hpos : 0 < Real.log (x + 1) := by
        apply Real.log_pos
        linarith
      linarith
    have hcont_add : ContinuousWithinAt (fun t : ℝ => t + (1 : ℝ)) (Set.Ici 1) x :=
      (continuousAt_id.add continuousAt_const).continuousWithinAt
    have hcont_log : ContinuousWithinAt (fun t : ℝ => Real.log (t + 1)) (Set.Ici 1) x := by
      simpa using (ContinuousAt.comp_continuousWithinAt (f := fun t : ℝ => t + 1) (g := Real.log)
        (Real.continuousAt_log hx1) hcont_add)
    have hmul : ContinuousWithinAt (fun t : ℝ => (t + 1) * Real.log (t + 1)) (Set.Ici 1) x :=
      hcont_add.mul hcont_log
    have hpow : ContinuousWithinAt (fun t : ℝ => ((t + 1) * Real.log (t + 1)) ^ 2) (Set.Ici 1) x :=
      hmul.pow 2
    have hpow_ne : ((x + 1) * Real.log (x + 1)) ^ 2 ≠ 0 := by
      exact pow_ne_zero 2 (mul_ne_zero hx1 hlog)
    have hinv :
        ContinuousWithinAt (fun t : ℝ => (((t + 1) * Real.log (t + 1)) ^ 2)⁻¹) (Set.Ici 1) x :=
      hpow.inv₀ hpow_ne
    have hother : ContinuousWithinAt (fun t : ℝ => -1 - Real.log (t + 1)) (Set.Ici 1) x :=
      continuousWithinAt_const.sub hcont_log
    simpa [shiftedPrimeWeightDeriv] using hinv.mul hother
  have hloc : LocallyIntegrableOn shiftedPrimeWeightDeriv (Set.Ici 1) :=
    hcont.locallyIntegrableOn measurableSet_Ici
  refine MeasureTheory.LocallyIntegrableOn.congr ?_ hloc
  filter_upwards [ae_restrict_mem measurableSet_Ici] with x hx
  simpa [shiftedPrimeWeightDeriv] using (hasDerivAt_norm_shiftedPrimeWeight hx).deriv.symm

lemma summable_shiftedPrimeWeights_indicator :
    Summable (fun n : ℕ => if (n + 1).Prime then erdosWeight (n + 1) else 0) := by
  have hf_diff : ∀ t ∈ Set.Ici 1, DifferentiableAt ℝ (fun x ↦ ‖shiftedPrimeWeightReal x‖) t := by
    intro t ht
    exact (hasDerivAt_norm_shiftedPrimeWeight ht).differentiableAt
  have h_bdd :
      (fun n : ℕ => ‖shiftedPrimeWeightReal n‖ *
        ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖) =O[atTop] fun _ => (1 : ℝ) := by
    let C : ℝ := Real.log 4 + 1
    refine Asymptotics.IsBigO.of_bound C ?_
    have hpi_real : ∀ᶠ x : ℝ in atTop, (π ⌊x⌋₊ : ℝ) ≤ C * x / Real.log x := by
      simpa [C] using (Chebyshev.eventually_primeCounting_le (ε := 1) (by positivity))
    have htend : Tendsto (fun n : ℕ => ((n + 1 : ℕ) : ℝ)) atTop atTop :=
      tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1)
    have hpi_nat0 : ∀ᶠ n : ℕ in atTop,
        (π ⌊((n + 1 : ℕ) : ℝ)⌋₊ : ℝ) ≤ C * ((n + 1 : ℕ) : ℝ) / Real.log ((n + 1 : ℕ) : ℝ) := by
      exact htend.eventually hpi_real
    have hpi_nat : ∀ᶠ n : ℕ in atTop,
        (π (n + 1) : ℝ) ≤ C * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1) := by
      filter_upwards [hpi_nat0] with n hn
      have hfloor : ⌊(n : ℝ) + 1⌋₊ = n + 1 := by
        simpa [Nat.floor_natCast, Nat.cast_add, add_comm]
          using (Nat.floor_add_one (show 0 ≤ (n : ℝ) by positivity))
      simpa [Nat.cast_add, hfloor] using hn
    filter_upwards [eventually_ge_atTop 2, hpi_nat] with n hn hpi
    have hsum := sum_shiftedPrimeIndicator_le_primeCounting n
    have hn' : (2 : ℝ) ≤ n := by exact_mod_cast hn
    have hlog_pos : 0 < Real.log ((n : ℝ) + 1) := by
      apply Real.log_pos
      have : (1 : ℝ) < (n : ℝ) + 1 := by nlinarith
      simpa
    have hden_pos : 0 < (((n : ℝ) + 1) * Real.log ((n : ℝ) + 1)) := by positivity
    calc
      ‖‖shiftedPrimeWeightReal n‖ * ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖‖
          = ‖shiftedPrimeWeightReal n‖ * ∑ k ∈ Finset.Icc 1 n, ‖shiftedPrimeIndicator k‖ := by
              rw [Real.norm_of_nonneg]
              exact mul_nonneg (norm_nonneg _) (Finset.sum_nonneg fun _ _ => norm_nonneg _)
      _ ≤ ‖shiftedPrimeWeightReal n‖ * (π (n + 1) : ℝ) := by
            gcongr
      _ ≤ ‖shiftedPrimeWeightReal n‖ *
            (C * ((n : ℝ) + 1) / Real.log ((n : ℝ) + 1)) := by
            gcongr
      _ = (C : ℝ) / (Real.log ((n : ℝ) + 1) ^ 2) := by
            rw [show ‖shiftedPrimeWeightReal n‖ = shiftedPrimeWeightReal n by
              have hfpos : 0 < shiftedPrimeWeightReal n := by
                simpa [shiftedPrimeWeightReal] using inv_pos.mpr hden_pos
              simp [Real.norm_eq_abs, abs_of_nonneg (le_of_lt hfpos)],
              shiftedPrimeWeightReal]
            field_simp [hlog_pos.ne', hden_pos.ne']
      _ = C * (Real.log ((n : ℝ) + 1) ^ 2)⁻¹ := by rw [div_eq_mul_inv]
      _ ≤ C * 1 := by
            have hC : 0 ≤ C := by positivity
            gcongr
            have hexp_lt_three : Real.exp 1 < 3 := by
              have h := Real.exp_one_lt_d9
              linarith
            have h3 : (3 : ℝ) ≤ (n : ℝ) + 1 := by nlinarith
            have h_exp_le : Real.exp 1 ≤ (n : ℝ) + 1 := le_trans hexp_lt_three.le h3
            have hlog_ge : 1 ≤ Real.log ((n : ℝ) + 1) :=
              (Real.le_log_iff_exp_le (by positivity)).2 h_exp_le
            have hsq : 1 ≤ Real.log ((n : ℝ) + 1) ^ 2 := by
              nlinarith [sq_nonneg (Real.log ((n : ℝ) + 1)), hlog_ge]
            simpa using (one_div_le_one_div_of_le (show (0 : ℝ) < 1 by norm_num) hsq)
      _ = C * ‖(1 : ℝ)‖ := by simp
  have hg1 :
      (fun t ↦ deriv (fun t ↦ ‖shiftedPrimeWeightReal t‖) t *
        ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖) =O[atTop] shiftedPrimeWeightBound := by
    let C : ℝ := Real.log 4 + 1
    refine Asymptotics.IsBigO.of_bound (2 * C) ?_
    have hpi_real : ∀ᶠ x : ℝ in atTop, (π ⌊x⌋₊ : ℝ) ≤ C * x / Real.log x := by
      simpa [C] using (Chebyshev.eventually_primeCounting_le (ε := 1) (by positivity))
    have hshift : Tendsto (fun t : ℝ => t + 1) atTop atTop :=
      tendsto_atTop_add_const_right _ _ tendsto_id
    have hpi_shift : ∀ᶠ t : ℝ in atTop, (π ⌊t + 1⌋₊ : ℝ) ≤ C * (t + 1) / Real.log (t + 1) := by
      exact hshift.eventually hpi_real
    filter_upwards [eventually_ge_atTop 2, hpi_shift] with t ht hpi
    have ht1 : 1 ≤ t := by linarith
    have ht0 : 0 ≤ t := by linarith
    have ht1_ne : t + 1 ≠ 0 := by linarith
    have hlog_pos : 0 < Real.log (t + 1) := by
      apply Real.log_pos
      linarith
    have hsum : ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ ≤
        C * (t + 1) / Real.log (t + 1) := by
      calc
        ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ ≤ (π (⌊t⌋₊ + 1) : ℝ) :=
          sum_shiftedPrimeIndicator_le_primeCounting _
        _ = (π ⌊t + 1⌋₊ : ℝ) := by
          have hfloor : ⌊t⌋₊ + 1 = ⌊t + 1⌋₊ := by
            simpa [add_comm] using (Nat.floor_add_one ht0).symm
          rw [hfloor]
        _ ≤ C * (t + 1) / Real.log (t + 1) := hpi
    have hsum_nonneg : 0 ≤ ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ :=
      Finset.sum_nonneg fun _ _ => norm_nonneg _
    have hlog_ge : 1 ≤ Real.log (t + 1) := by
      have hexp_lt_three : Real.exp 1 < 3 := by
        have h := Real.exp_one_lt_d9
        linarith
      have h3 : (3 : ℝ) ≤ t + 1 := by linarith
      have h_exp_le : Real.exp 1 ≤ t + 1 := le_trans hexp_lt_three.le h3
      exact (Real.le_log_iff_exp_le (by positivity)).2 h_exp_le
    have habs_d : ‖shiftedPrimeWeightDeriv t‖ =
        ((((t + 1) * Real.log (t + 1)) ^ 2)⁻¹) * (1 + Real.log (t + 1)) := by
      rw [shiftedPrimeWeightDeriv, Real.norm_eq_abs, abs_mul]
      have h_inv_nonneg : 0 ≤ ((((t + 1) * Real.log (t + 1)) ^ 2)⁻¹ : ℝ) := by positivity
      rw [abs_of_nonneg h_inv_nonneg, abs_of_nonpos]
      · ring
      · linarith
    have hg_nonneg : 0 ≤ shiftedPrimeWeightBound t := by
      have hden : 0 < (t + 1) * Real.log (t + 1) ^ 2 := by positivity
      exact le_of_lt (one_div_pos.mpr hden)
    calc
      ‖deriv (fun t ↦ ‖shiftedPrimeWeightReal t‖) t *
          ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖‖
          = ‖deriv (fun t ↦ ‖shiftedPrimeWeightReal t‖) t‖ *
              ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ := by
                rw [norm_mul, show ‖∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖‖ =
                  ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ by
                    exact Real.norm_of_nonneg hsum_nonneg]
      _ = ‖shiftedPrimeWeightDeriv t‖ * ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ := by
            rw [show deriv (fun t ↦ ‖shiftedPrimeWeightReal t‖) t = shiftedPrimeWeightDeriv t by
              simpa [shiftedPrimeWeightDeriv] using (hasDerivAt_norm_shiftedPrimeWeight ht1).deriv]
      _ = ((((t + 1) * Real.log (t + 1)) ^ 2)⁻¹) * (1 + Real.log (t + 1)) *
            ∑ k ∈ Finset.Icc 1 ⌊t⌋₊, ‖shiftedPrimeIndicator k‖ := by
            rw [habs_d]
      _ ≤ ((((t + 1) * Real.log (t + 1)) ^ 2)⁻¹) * (2 * Real.log (t + 1)) *
            (C * (t + 1) / Real.log (t + 1)) := by
            gcongr
            · linarith
      _ = (2 * C) * shiftedPrimeWeightBound t := by
            unfold shiftedPrimeWeightBound
            field_simp [hlog_pos.ne', ht1_ne]
      _ = (2 * C) * ‖shiftedPrimeWeightBound t‖ := by
            rw [Real.norm_of_nonneg hg_nonneg]
  have hg2 : IntegrableAtFilter shiftedPrimeWeightBound atTop := by
    rw [integrableAtFilter_atTop_iff]
    have hIoi : IntegrableOn shiftedPrimeWeightBound (Set.Ioi 1) := by
      refine MeasureTheory.integrableOn_Ioi_deriv_of_nonneg (a := 1) (l := 0)
        (g := fun t : ℝ => -(Real.log (t + 1))⁻¹)
        (g' := fun t : ℝ => 1 / ((t + 1) * Real.log (t + 1) ^ 2)) ?_ ?_ ?_ ?_
      · have hcont_add : ContinuousWithinAt (fun t : ℝ => t + (1 : ℝ)) (Set.Ici 1) 1 :=
            (continuousAt_id.add continuousAt_const).continuousWithinAt
        have hcont_log : ContinuousWithinAt (fun t : ℝ => Real.log (t + 1)) (Set.Ici 1) 1 := by
          simpa using (ContinuousAt.comp_continuousWithinAt (f := fun t : ℝ => t + 1)
            (g := Real.log) (Real.continuousAt_log (by norm_num : ((1 : ℝ) + 1) ≠ 0)) hcont_add)
        exact (hcont_log.inv₀ (by norm_num : Real.log ((1 : ℝ) + 1) ≠ 0)).neg
      · intro x hx
        have hxgt1 : 1 < x + 1 := by
          have hx' : 1 < x := hx
          nlinarith
        have hx1 : x + 1 ≠ 0 := (lt_trans zero_lt_one hxgt1).ne'
        have hlog : Real.log (x + 1) ≠ 0 := (Real.log_pos hxgt1).ne'
        have h1 : HasDerivAt (fun y : ℝ => y + 1) 1 x := (hasDerivAt_id x).add_const 1
        have hlog' : HasDerivAt (fun y : ℝ => Real.log (y + 1)) ((x + 1)⁻¹) x := by
          simpa using
            (HasDerivAt.comp (x := x) (h := fun y : ℝ => y + 1) (Real.hasDerivAt_log hx1) h1)
        have hinv :
            HasDerivAt (fun y : ℝ => (Real.log (y + 1))⁻¹) (-(x + 1)⁻¹ / Real.log (x + 1) ^ 2) x :=
            by
          simpa [pow_two, mul_comm, mul_left_comm, mul_assoc] using hlog'.inv hlog
        simpa [div_eq_mul_inv, pow_two, mul_comm, mul_left_comm, mul_assoc] using hinv.neg
      · intro x hx
        have hxgt1 : 1 < x + 1 := by
          have hx' : 1 < x := hx
          nlinarith
        have hden : 0 < (x + 1) * Real.log (x + 1) ^ 2 := by
          have hlog : 0 < Real.log (x + 1) := Real.log_pos hxgt1
          positivity
        exact le_of_lt (one_div_pos.mpr hden)
      · have hlog_tendsto : Tendsto (fun t : ℝ => Real.log (t + 1)) atTop atTop := by
          exact Real.tendsto_log_atTop.comp (tendsto_atTop_add_const_right _ _ tendsto_id)
        have hinv_tendsto : Tendsto (fun t : ℝ => (Real.log (t + 1))⁻¹) atTop (nhds 0) := by
          exact tendsto_inv_atTop_zero.comp hlog_tendsto
        simpa using hinv_tendsto.neg
    refine ⟨1, ?_⟩
    exact (integrableOn_Ici_iff_integrableOn_Ioi (b := 1) (by finiteness)).2 hIoi
  have hs : Summable (fun n : ℕ => shiftedPrimeWeightReal n * shiftedPrimeIndicator n) :=
    summable_mul_of_bigO_atTop' (c := shiftedPrimeIndicator) (f := shiftedPrimeWeightReal)
      hf_diff locallyIntegrable_deriv_norm_shiftedPrimeWeight h_bdd hg1 hg2
  refine hs.congr ?_
  intro n
  by_cases hn : (n + 1).Prime
  · simp [shiftedPrimeWeightReal, shiftedPrimeIndicator, erdosWeight, hn]
  · simp [shiftedPrimeIndicator, hn]

def shiftedPrimeEquiv : {n : ℕ // (n + 1).Prime} ≃ {p : ℕ // p.Prime} where
  toFun n := ⟨n.1 + 1, n.2⟩
  invFun p := ⟨p.1 - 1, by
    simpa [Nat.sub_add_cancel p.2.one_le] using p.2⟩
  left_inv n := by
    apply Subtype.ext
    simp
  right_inv p := by
    apply Subtype.ext
    simpa using Nat.succ_pred_eq_of_pos p.2.pos

lemma summable_primeWeights :
    Summable (fun p : {p : ℕ // p.Prime} => erdosWeight p.1) := by
  have hsub : Summable (fun n : {n : ℕ // (n + 1).Prime} => erdosWeight (n.1 + 1)) := by
    let F : ℕ → ℝ := fun n => if (n + 1).Prime then erdosWeight (n + 1) else 0
    have hF : Summable F := by
      simpa [F] using summable_shiftedPrimeWeights_indicator
    have hzero : ∀ n ∉ Set.range ((↑) : {n : ℕ // (n + 1).Prime} → ℕ), F n = 0 := by
      intro n hn
      have hnotprime : ¬ (n + 1).Prime := by
        intro hprime
        apply hn
        exact ⟨⟨n, hprime⟩, rfl⟩
      simp [F, hnotprime]
    have hcomp : (fun n : {n : ℕ // (n + 1).Prime} => F n) = fun n => erdosWeight (n.1 + 1) := by
      funext n
      simp [F, n.2]
    rw [← hcomp]
    exact ((Function.Injective.summable_iff
      (f := F) (g := ((↑) : {n : ℕ // (n + 1).Prime} → ℕ)) Subtype.val_injective hzero).2 hF)
  exact (Equiv.summable_iff shiftedPrimeEquiv).1 hsub

lemma primitiveDivisorClosure_spec_of_finite {A : Set ℕ} (hA : PrimitiveSet A)
    (hfin : A.Finite) :
    (primitiveDivisorClosure A).Finite ∧
      A ⊆ primitiveDivisorClosure A ∧
      ∀ {d e : ℕ}, d ∈ primitiveDivisorClosure A → 2 ≤ e → e ∣ d →
        e ∈ primitiveDivisorClosure A := by
  have hclosure_subset :
      primitiveDivisorClosure A ⊆ ⋃ a ∈ A, ((Nat.divisors a : Finset ℕ) : Set ℕ) := by
    intro d hd
    rcases (show 2 ≤ d ∧ ∃ a ∈ A, d ∣ a by simpa [primitiveDivisorClosure] using hd) with
      ⟨_, a, ha, hda⟩
    refine Set.mem_iUnion.2 ⟨a, ?_⟩
    refine Set.mem_iUnion.2 ⟨ha, ?_⟩
    have ha0 : a ≠ 0 := ne_of_gt (lt_of_lt_of_le (by decide) (hA.1 ha))
    exact Nat.mem_divisors.mpr ⟨hda, ha0⟩
  have hclosure_fin :
      (primitiveDivisorClosure A).Finite := by
    refine (hfin.biUnion ?_).subset hclosure_subset
    intro a ha
    exact Finset.finite_toSet (Nat.divisors a)
  have hA_subset : A ⊆ primitiveDivisorClosure A := by
    intro a ha
    exact show a ∈ primitiveDivisorClosure A by
      simpa [primitiveDivisorClosure] using ⟨hA.1 ha, a, ha, dvd_rfl⟩
  refine ⟨hclosure_fin, hA_subset, ?_⟩
  intro d e hd he hed
  rcases (show 2 ≤ d ∧ ∃ a ∈ A, d ∣ a by simpa [primitiveDivisorClosure] using hd) with
    ⟨_, a, ha, hda⟩
  exact show e ∈ primitiveDivisorClosure A by
    simpa [primitiveDivisorClosure] using ⟨he, a, ha, dvd_trans hed hda⟩

lemma modifiedFlow_nonneg (m n : ℕ) : 0 ≤ modifiedFlow m n :=
  (modifiedFlow_satisfies_flow_conjecture.1.1) m n

lemma modifiedFlow_eq_zero_of_not_dvd_lt {m n : ℕ}
    (h : ¬ (n ∣ m ∧ n < m)) : modifiedFlow m n = 0 :=
  (modifiedFlow_satisfies_flow_conjecture.1.2) m n h

lemma summable_modifiedFlow_row (m : ℕ) :
    Summable (fun n : ℕ => modifiedFlow m n) := by
  classical
  refine summable_of_ne_finset_zero (s := m.divisors) ?_
  intro n hn
  apply modifiedFlow_eq_zero_of_not_dvd_lt
  intro h
  have hm0 : m ≠ 0 := by omega
  exact hn (Nat.mem_divisors.mpr ⟨h.1, hm0⟩)

lemma outflow_modifiedFlow_eq_sum_finset_add_compl (s : Finset ℕ) (m : ℕ) :
    outflow modifiedFlow m =
      (∑ n ∈ s, modifiedFlow m n) +
        ∑' n : { n // n ∉ s }, modifiedFlow m n := by
  simpa [outflow] using ((summable_modifiedFlow_row m).sum_add_tsum_subtype_compl s).symm


lemma summable_shift_rpow_neg_two : Summable (fun j : ℕ => ((j : ℝ) + 1) ^ (-2 : ℝ)) := by
  have hpow : Summable (fun j : ℕ => (j : ℝ) ^ (-2 : ℝ)) := by
    exact (Real.summable_nat_rpow).2 (by norm_num)
  have hshift : Summable (fun j : ℕ => (((j + 1 : ℕ) : ℝ) ^ (-2 : ℝ))) :=
    (summable_nat_add_iff 1).2 hpow
  simpa [Nat.cast_add, add_comm, add_left_comm, add_assoc] using hshift

lemma baseFlow_nonneg (m n : ℕ) : 0 ≤ baseFlow m n := by
  by_cases hm : 1 < m
  · by_cases hdiv : n ∣ m
    · by_cases hpow : IsPrimePow (m / n)
      · rw [baseFlow, if_pos hm, if_pos hdiv, if_pos hpow]
        refine div_nonneg ArithmeticFunction.vonMangoldt_nonneg ?_
        have hm0 : 0 < (m : ℝ) := by
          exact_mod_cast (lt_trans Nat.zero_lt_one hm)
        have hlog : 0 < Real.log m := by
          exact Real.log_pos (by exact_mod_cast hm)
        exact le_of_lt (mul_pos hm0 (sq_pos_of_pos hlog))
      · rw [baseFlow, if_pos hm, if_pos hdiv, if_neg hpow]
    · rw [baseFlow, if_pos hm, if_neg hdiv]
  · rw [baseFlow, if_neg hm]

lemma baseFlow_mul_primepow_eq {N p j : ℕ} (hN : 0 < N) (hp : p.Prime) :
    baseFlow (N * p ^ (j + 1)) N =
      Real.log p /
        ((((N * p ^ (j + 1) : ℕ) : ℝ)) * (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2)) := by
  have hpow_gt1 : 1 < p ^ (j + 1) := by
    exact one_lt_pow' hp.one_lt (by omega)
  have hNp : 1 < N * p ^ (j + 1) := by
    have hNge1 : 1 ≤ N := Nat.succ_le_of_lt hN
    have hmul : N < N * p ^ (j + 1) := by
      simpa using (Nat.mul_lt_mul_of_pos_left hpow_gt1 hN)
    exact lt_of_le_of_lt hNge1 hmul
  have hdvd : N ∣ N * p ^ (j + 1) := ⟨p ^ (j + 1), by simp⟩
  have hpp : IsPrimePow (p ^ (j + 1)) := by
    exact (isPrimePow_pow_iff (by omega)).2 hp.isPrimePow
  rw [baseFlow, if_pos hNp, if_pos hdvd, Nat.mul_div_right _ hN, if_pos hpp]
  rw [ArithmeticFunction.vonMangoldt_apply_pow (by omega),
      ArithmeticFunction.vonMangoldt_apply_prime hp]

lemma baseFlow_mul_primepow_le {N p j : ℕ} (hN : 0 < N) (hp : p.Prime) :
    baseFlow (N * p ^ (j + 1)) N ≤
      (1 / (N : ℝ)) * erdosWeight p * (((j : ℝ) + 1) ^ (-2 : ℝ)) := by
  rw [baseFlow_mul_primepow_eq hN hp]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (Nat.ne_of_gt hN)
  have hp0 : (p : ℝ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hlogp_pos : 0 < Real.log p := Real.log_pos (by exact_mod_cast hp.one_lt)
  have hlog_ge : (((j : ℝ) + 1) * Real.log p) ≤ Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) := by
    have hlogN_nonneg : 0 ≤ Real.log N := Real.log_natCast_nonneg N
    have hpow0 : (((p ^ (j + 1) : ℕ) : ℝ)) ≠ 0 := by
      exact_mod_cast (pow_pos hp.pos _).ne'
    have hlogmul := Real.log_mul hN0 hpow0
    have hlogpow : Real.log (((p ^ (j + 1) : ℕ) : ℝ)) = (((j : ℝ) + 1) * Real.log p) := by
      rw [Nat.cast_pow, ← Real.rpow_natCast, Real.log_rpow]
      · norm_num
      · exact_mod_cast hp.pos
    rw [show Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) =
        Real.log N + Real.log (((p ^ (j + 1) : ℕ) : ℝ)) by
      simpa [Nat.cast_mul] using hlogmul]
    rw [hlogpow]
    linarith
  have hlog_nonneg : 0 ≤ (((j : ℝ) + 1) * Real.log p) := by positivity
  have hsq_le : ((((j : ℝ) + 1) * Real.log p) ^ 2) ≤
      (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2) := by
    nlinarith
  have hA : (N : ℝ) * p ≤ (((N * p ^ (j + 1) : ℕ) : ℝ)) := by
    exact_mod_cast (Nat.mul_le_mul_left N (Nat.le_self_pow (by omega) p))
  have hsq_nonneg : 0 ≤ ((((j : ℝ) + 1) * Real.log p) ^ 2) := by positivity
  have hB_nonneg : 0 ≤ ((((N * p ^ (j + 1) : ℕ) : ℝ))) := by positivity
  have hden_le :
      ((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2) ≤
        (((N * p ^ (j + 1) : ℕ) : ℝ)) *
          (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2) := by
    exact mul_le_mul hA hsq_le hsq_nonneg hB_nonneg
  have hlogp_nonneg : 0 ≤ Real.log p := hlogp_pos.le
  have hden_pos : 0 < ((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2) := by
    positivity
  calc
    Real.log p /
        ((((N * p ^ (j + 1) : ℕ) : ℝ)) * (Real.log (((N * p ^ (j + 1) : ℕ) : ℝ)) ^ 2))
        ≤ Real.log p / (((N : ℝ) * p) * ((((j : ℝ) + 1) * Real.log p) ^ 2)) := by
          exact div_le_div_of_nonneg_left hlogp_nonneg hden_pos hden_le
    _ = (1 / (N : ℝ)) * erdosWeight p * (((j : ℝ) + 1) ^ (-2 : ℝ)) := by
          rw [erdosWeight]
          have hsq :
              ((((j : ℝ) + 1) * Real.log p) ^ 2) =
                (((j : ℝ) + 1) ^ 2) * (Real.log p) ^ 2 := by
            ring
          have hrpow :
              (((j : ℝ) + 1) ^ (-2 : ℝ)) = ((((j : ℝ) + 1) ^ 2))⁻¹ := by
            rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (by positivity) 2]
            norm_num
          rw [hsq, hrpow]
          field_simp [hN0, hp0, hlogp_pos.ne']

lemma summable_baseFlow_col (N : ℕ) : Summable (fun K : ℕ => baseFlow K N) := by
  classical
  by_cases hN : N = 0
  · refine summable_of_ne_finset_zero (s := ∅) ?_
    intro K hK
    simp [baseFlow, hN]
  · have hNpos : 0 < N := Nat.pos_of_ne_zero hN
    let e : (Σ p : {p : ℕ // p.Prime}, ℕ) → ℕ := fun a => N * a.1.1 ^ (a.2 + 1)
    have he : Function.Injective e := by
      intro a b hab
      cases a with
      | mk ap aj =>
        cases b with
        | mk bp bj =>
          simp only [e] at hab ⊢
          have hpow : ap.1 ^ (aj + 1) = bp.1 ^ (bj + 1) := by
            exact Nat.eq_of_mul_eq_mul_left hNpos hab
          rcases ap.2.pow_inj' bp.2 (by omega) (by omega) hpow with ⟨hp, hj⟩
          have hapbp : ap = bp := by
            apply Subtype.ext
            simpa using hp
          subst hapbp
          have hajbj : aj = bj := by omega
          subst hajbj
          rfl
    have hzero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
      intro K hK
      by_cases hdiv : N ∣ K
      · rcases hdiv with ⟨q, rfl⟩
        by_cases hqpp : IsPrimePow q
        · exfalso
          obtain ⟨p, k, hp, hk, hq⟩ := (isPrimePow_nat_iff q).mp hqpp
          apply hK
          refine ⟨⟨⟨p, hp⟩, k - 1⟩, ?_⟩
          simp [e, hq, show k - 1 + 1 = k by omega]
        · by_cases hNq : 1 < N * q
          · simp [baseFlow, hNq, Nat.mul_div_right q hNpos, hqpp]
          · simp [baseFlow, hNq]
      · simp [baseFlow, hdiv]
    let g : (Σ p : {p : ℕ // p.Prime}, ℕ) → ℝ :=
      fun a => (1 / (N : ℝ)) * erdosWeight a.1.1 * (((a.2 : ℝ) + 1) ^ (-2 : ℝ))
    have hg_nonneg : ∀ a, 0 ≤ g a := by
      intro a
      have hp1 : 1 < a.1.1 := a.1.2.one_lt
      have herdos_nonneg : 0 ≤ erdosWeight a.1.1 := by
        rw [erdosWeight]
        positivity
      have hrpow_nonneg : 0 ≤ (((a.2 : ℝ) + 1) ^ (-2 : ℝ)) := by positivity
      have hNinv_nonneg : 0 ≤ (1 / (N : ℝ)) := by positivity
      exact mul_nonneg (mul_nonneg hNinv_nonneg herdos_nonneg) hrpow_nonneg
    have hinner : ∀ p : {p : ℕ // p.Prime}, Summable (fun j : ℕ => g ⟨p, j⟩) := by
      intro p
      have hs : Summable (fun j : ℕ => (((j : ℝ) + 1) ^ (-2 : ℝ))) := summable_shift_rpow_neg_two
      simpa [g, mul_assoc, mul_left_comm, mul_comm] using
        (Summable.mul_left ((1 / (N : ℝ)) * erdosWeight p.1) hs)
    have houter : Summable (fun p : {p : ℕ // p.Prime} => ∑' j : ℕ, g ⟨p, j⟩) := by
      let C : ℝ := ∑' j : ℕ, (((j : ℝ) + 1) ^ (-2 : ℝ))
      have hC : Summable (fun p : {p : ℕ // p.Prime} => ((1 / (N : ℝ)) * C) * erdosWeight p.1) := by
        simpa [mul_assoc, mul_left_comm, mul_comm] using
          (Summable.mul_left (((1 / (N : ℝ)) * C)) summable_primeWeights)
      refine hC.congr ?_
      intro p
      have htsum :
          (∑' j : ℕ, g ⟨p, j⟩) = ((1 / (N : ℝ)) * erdosWeight p.1) * C := by
        simpa [g, C, mul_assoc, mul_left_comm, mul_comm] using
          (summable_shift_rpow_neg_two.tsum_mul_left (((1 / (N : ℝ)) * erdosWeight p.1)))
      rw [htsum]
      ring
    have hg : Summable g := (summable_sigma_of_nonneg hg_nonneg).2 ⟨hinner, houter⟩
    have hbase_on_range : ∀ a, baseFlow (e a) N ≤ g a := by
      intro a
      simpa [e, g] using baseFlow_mul_primepow_le hNpos a.1.2
    have hbase_range_summable :
        Summable (fun a : (Σ p : {p : ℕ // p.Prime}, ℕ) => baseFlow (e a) N) := by
      exact Summable.of_nonneg_of_le
        (fun a => baseFlow_nonneg (e a) N)
        hbase_on_range hg
    exact
      (Function.Injective.summable_iff (f := fun K => baseFlow K N) (g := e) he hzero).1
        hbase_range_summable

lemma modifiedFlow_le_baseFlow_add_baseFlow_one (m n : ℕ) :
    modifiedFlow m n ≤ baseFlow m n + baseFlow m 1 := by
  rw [modifiedFlow]
  split_ifs <;> nlinarith [baseFlow_nonneg m n, baseFlow_nonneg m 1]

lemma summable_modifiedFlow_col (N : ℕ) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  have hsum : Summable (fun K : ℕ => baseFlow K N + baseFlow K 1) :=
    (summable_baseFlow_col N).add (summable_baseFlow_col 1)
  exact Summable.of_nonneg_of_le
    (fun K => modifiedFlow_nonneg K N)
    (fun K => modifiedFlow_le_baseFlow_add_baseFlow_one K N)
    hsum

lemma inflow_modifiedFlow_eq_sum_finset_add_compl (s : Finset ℕ) (n : ℕ) :
    inflow modifiedFlow n =
      (∑ m ∈ s, modifiedFlow m n) +
        ∑' m : { m // m ∉ s }, modifiedFlow m n := by
  simpa [inflow] using ((summable_modifiedFlow_col n).sum_add_tsum_subtype_compl s).symm

lemma boundaryOutflow_eq_sum_compl (s : Finset ℕ) :
    boundaryOutflow modifiedFlow (↑s : Set ℕ) =
      ∑ r ∈ s, ∑' n : { n // n ∉ s }, modifiedFlow r n := by
  classical
  let e : boundaryOutPairs (↑s : Set ℕ) ≃
      Σ r : {r // r ∈ s}, {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} :=
    { toFun := fun mn =>
        ⟨⟨mn.1.1, mn.2.1⟩, ⟨mn.1.2, mn.2.2.1, mn.2.2.2⟩⟩
      invFun := fun rn =>
        ⟨(rn.1.1, rn.2.1), rn.1.2, rn.2.2.1, rn.2.2.2⟩
      left_inv := by
        intro mn
        cases mn
        rfl
      right_inv := by
        intro rn
        cases rn
        rfl }
  have hinner :
      ∀ r : {r // r ∈ s},
        Summable (fun n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} => modifiedFlow r.1 n.1) := by
    intro r
    simpa using
      (summable_modifiedFlow_row r.1).subtype {n : ℕ | n ∉ s ∧ n ∣ r.1 ∧ n < r.1}
  have houter :
      Summable (fun r : {r // r ∈ s} =>
        ∑' n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1}, modifiedFlow r.1 n.1) := by
    exact Summable.of_finite
  have hsigma :
      Summable (fun z : Σ r : {r // r ∈ s}, {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} =>
        modifiedFlow z.1.1 z.2.1) := by
    refine (summable_sigma_of_nonneg (fun z => modifiedFlow_nonneg _ _)).2 ?_
    exact ⟨hinner, houter⟩
  have hprecise :
      ∀ r : {r // r ∈ s},
        (∑' n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1}, modifiedFlow r.1 n.1) =
          ∑' n : {n // n ∉ s}, modifiedFlow r.1 n.1 := by
    intro r
    have hsupport :
        Function.support (fun n : {n // n ∉ s} => modifiedFlow r.1 n.1) ⊆
          {n | n.1 ∣ r.1 ∧ n.1 < r.1} := by
      intro n hn
      by_contra hbad
      exact hn <| by
        apply modifiedFlow_eq_zero_of_not_dvd_lt
        simpa [Set.mem_setOf_eq] using hbad
    let e' :
        {x : {n // n ∉ s} // x.1 ∣ r.1 ∧ x.1 < r.1} ≃
          {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} :=
      { toFun := fun n => ⟨n.1.1, n.1.2, n.2.1, n.2.2⟩
        invFun := fun n => ⟨⟨n.1, n.2.1⟩, n.2.2.1, n.2.2.2⟩
        left_inv := by intro n; cases n; rfl
        right_inv := by intro n; cases n; rfl }
    have hsub :
        (∑' x : {x : {n // n ∉ s} // x.1 ∣ r.1 ∧ x.1 < r.1}, modifiedFlow r.1 x.1.1) =
          ∑' n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1}, modifiedFlow r.1 n.1 := by
      simpa [e'] using
        (Equiv.tsum_eq e' (fun n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} => modifiedFlow r.1 n.1))
    exact hsub.symm.trans (tsum_subtype_eq_of_support_subset hsupport)
  calc
    boundaryOutflow modifiedFlow (↑s : Set ℕ)
      = ∑' z : Σ r : {r // r ∈ s}, {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1},
          modifiedFlow z.1.1 z.2.1 := by
            simpa [boundaryOutflow, e] using
              (Equiv.tsum_eq e (fun z : Σ r : {r // r ∈ s},
                  {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1} =>
                modifiedFlow z.1.1 z.2.1))
    _ = ∑' r : {r // r ∈ s},
          ∑' n : {n // n ∉ s ∧ n ∣ r.1 ∧ n < r.1}, modifiedFlow r.1 n.1 := by
            exact hsigma.tsum_sigma' hinner
    _ = ∑' r : {r // r ∈ s}, ∑' n : {n // n ∉ s}, modifiedFlow r.1 n.1 := by
          congr
          ext r
          exact hprecise r
    _ = ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n := by
          simpa using
            (Finset.tsum_subtype' s (fun r => ∑' n : {n // n ∉ s}, modifiedFlow r n))

lemma boundaryInflow_eq_sum_compl (s : Finset ℕ) :
    boundaryInflow modifiedFlow (↑s : Set ℕ) =
      ∑ n ∈ s, ∑' m : { m // m ∉ s }, modifiedFlow m n := by
  classical
  let e : boundaryInPairs (↑s : Set ℕ) ≃
      Σ n : {n // n ∈ s}, {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} :=
    { toFun := fun mn =>
        ⟨⟨mn.1.2, mn.2.2.1⟩, ⟨mn.1.1, mn.2.1, mn.2.2.2.1, mn.2.2.2.2⟩⟩
      invFun := fun nm =>
        ⟨(nm.2.1, nm.1.1), nm.2.2.1, nm.1.2, nm.2.2.2.1, nm.2.2.2.2⟩
      left_inv := by
        intro mn
        cases mn
        rfl
      right_inv := by
        intro nm
        cases nm
        rfl }
  have hinner :
      ∀ n : {n // n ∈ s},
        Summable (fun m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} => modifiedFlow m.1 n.1) := by
    intro n
    simpa using
      (summable_modifiedFlow_col n.1).subtype {m : ℕ | m ∉ s ∧ n.1 ∣ m ∧ n.1 < m}
  have houter :
      Summable (fun n : {n // n ∈ s} =>
        ∑' m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m}, modifiedFlow m.1 n.1) := by
    exact Summable.of_finite
  have hsigma :
      Summable (fun z : Σ n : {n // n ∈ s}, {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} =>
        modifiedFlow z.2.1 z.1.1) := by
    refine (summable_sigma_of_nonneg (fun z => modifiedFlow_nonneg _ _)).2 ?_
    exact ⟨hinner, houter⟩
  have hprecise :
      ∀ n : {n // n ∈ s},
        (∑' m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m}, modifiedFlow m.1 n.1) =
          ∑' m : {m // m ∉ s}, modifiedFlow m.1 n.1 := by
    intro n
    have hsupport :
        Function.support (fun m : {m // m ∉ s} => modifiedFlow m.1 n.1) ⊆
          {m | n.1 ∣ m.1 ∧ n.1 < m.1} := by
      intro m hm
      by_contra hbad
      exact hm <| by
        apply modifiedFlow_eq_zero_of_not_dvd_lt
        simpa [Set.mem_setOf_eq] using hbad
    let e' :
        {x : {m // m ∉ s} // n.1 ∣ x.1 ∧ n.1 < x.1} ≃
          {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} :=
      { toFun := fun m => ⟨m.1.1, m.1.2, m.2.1, m.2.2⟩
        invFun := fun m => ⟨⟨m.1, m.2.1⟩, m.2.2.1, m.2.2.2⟩
        left_inv := by intro m; cases m; rfl
        right_inv := by intro m; cases m; rfl }
    have hsub :
        (∑' x : {x : {m // m ∉ s} // n.1 ∣ x.1 ∧ n.1 < x.1}, modifiedFlow x.1.1 n.1) =
          ∑' m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m}, modifiedFlow m.1 n.1 := by
      simpa [e'] using
        (Equiv.tsum_eq e' (fun m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} =>
          modifiedFlow m.1 n.1))
    exact hsub.symm.trans (tsum_subtype_eq_of_support_subset hsupport)
  calc
    boundaryInflow modifiedFlow (↑s : Set ℕ)
      = ∑' z : Σ n : {n // n ∈ s}, {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m},
          modifiedFlow z.2.1 z.1.1 := by
            simpa [boundaryInflow, e] using
              (Equiv.tsum_eq e (fun z : Σ n : {n // n ∈ s},
                  {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m} =>
                modifiedFlow z.2.1 z.1.1))
    _ = ∑' n : {n // n ∈ s},
          ∑' m : {m // m ∉ s ∧ n.1 ∣ m ∧ n.1 < m}, modifiedFlow m.1 n.1 := by
            exact hsigma.tsum_sigma' hinner
    _ = ∑' n : {n // n ∈ s}, ∑' m : {m // m ∉ s}, modifiedFlow m.1 n.1 := by
          congr
          ext n
          exact hprecise n
    _ = ∑ n ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m n := by
          simpa using
            (Finset.tsum_subtype' s (fun n => ∑' m : {m // m ∉ s}, modifiedFlow m n))

lemma tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow {Ω : Set ℕ}
    (hΩfin : Ω.Finite) :
    (∑' r : Ω, (outflow modifiedFlow (r : ℕ) - inflow modifiedFlow (r : ℕ))) =
      boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
  classical
  let s : Finset ℕ := hΩfin.toFinset
  have hsΩ : (↑s : Set ℕ) = Ω := hΩfin.coe_toFinset
  rw [← hsΩ]
  have hout :
      ∑ r ∈ s, outflow modifiedFlow r =
        (∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n := by
    calc
      ∑ r ∈ s, outflow modifiedFlow r
        = ∑ r ∈ s, ((∑ n ∈ s, modifiedFlow r n) +
            ∑' n : {n // n ∉ s}, modifiedFlow r n) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [outflow_modifiedFlow_eq_sum_finset_add_compl s r]
      _ = (∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
            ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n := by
              rw [Finset.sum_add_distrib]
  have hin :
      ∑ r ∈ s, inflow modifiedFlow r =
        (∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
    calc
      ∑ r ∈ s, inflow modifiedFlow r
        = ∑ r ∈ s, ((∑ m ∈ s, modifiedFlow m r) +
            ∑' m : {m // m ∉ s}, modifiedFlow m r) := by
              refine Finset.sum_congr rfl ?_
              intro r hr
              rw [inflow_modifiedFlow_eq_sum_finset_add_compl s r]
      _ = (∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
            ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
              rw [Finset.sum_add_distrib]
  have hinternal :
      ∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n =
        ∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r := by
    simpa using (Finset.sum_comm (s := s) (t := s) (f := fun r n => modifiedFlow r n))
  calc
    (∑' r : (↑s : Set ℕ), (outflow modifiedFlow (r : ℕ) - inflow modifiedFlow (r : ℕ)))
      = ∑ r ∈ s, (outflow modifiedFlow r - inflow modifiedFlow r) := by
          simpa using
            (Finset.tsum_subtype' s
              (fun r => outflow modifiedFlow r - inflow modifiedFlow r))
    _ = (∑ r ∈ s, outflow modifiedFlow r) - ∑ r ∈ s, inflow modifiedFlow r := by
          rw [Finset.sum_sub_distrib]
    _ =
        ((∑ r ∈ s, ∑ n ∈ s, modifiedFlow r n) +
          ∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n) -
        ((∑ r ∈ s, ∑ m ∈ s, modifiedFlow m r) +
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r) := by
            rw [hout, hin]
    _ = (∑ r ∈ s, ∑' n : {n // n ∉ s}, modifiedFlow r n) -
          ∑ r ∈ s, ∑' m : {m // m ∉ s}, modifiedFlow m r := by
            rw [hinternal]
            ring
    _ = boundaryOutflow modifiedFlow (↑s : Set ℕ) -
          boundaryInflow modifiedFlow (↑s : Set ℕ) := by
            rw [boundaryOutflow_eq_sum_compl, boundaryInflow_eq_sum_compl]

lemma boundaryOutflow_le_primeWeightSum_of_downwardClosed {Ω : Set ℕ}
    (hΩ_ge_two : ∀ {d : ℕ}, d ∈ Ω → 2 ≤ d)
    (hΩdown : ∀ {d e : ℕ}, d ∈ Ω → 2 ≤ e → e ∣ d → e ∈ Ω) :
    boundaryOutflow modifiedFlow Ω ≤ primeWeightSum := by
  classical
  rcases modifiedFlow_satisfies_flow_conjecture with
    ⟨⟨_, hmodified_support⟩, _, hprime_outflow, _, hcomposite_to_one⟩
  have hone_not_mem : 1 ∉ Ω := by
    intro h1
    have h := hΩ_ge_two h1
    omega
  have hboundary_target_eq_one : ∀ mn : boundaryOutPairs Ω, mn.1.2 = 1 := by
    intro mn
    rcases mn with ⟨⟨m, n⟩, hmn⟩
    rcases hmn with ⟨hmΩ, hnΩ, hdiv, _⟩
    have hm2 : 2 ≤ m := hΩ_ge_two hmΩ
    have hmpos : 0 < m := by omega
    have hnpos : 0 < n := Nat.pos_of_dvd_of_pos hdiv hmpos
    have hnle : n ≤ 1 := by
      by_contra hgt
      have hn2 : 2 ≤ n := by omega
      exact hnΩ (hΩdown hmΩ hn2 hdiv)
    have hpred : n.pred = 0 := by
      rw [Nat.pred_eq_sub_one, Nat.sub_eq_zero_of_le hnle]
    have hsucc : n.pred.succ = n := Nat.succ_pred_eq_of_pos hnpos
    rw [hpred] at hsucc
    simpa using hsucc.symm
  let eBoundaryFun : boundaryOutPairs Ω → Ω := fun mn => ⟨mn.1.1, mn.2.1⟩
  have heBoundary_bij : Function.Bijective eBoundaryFun := by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Prod.ext
      · simpa [eBoundaryFun] using congrArg Subtype.val h
      · simp [hboundary_target_eq_one a, hboundary_target_eq_one b]
    · intro m
      refine ⟨⟨(m.1, 1), ?_⟩, ?_⟩
      · refine ⟨m.2, hone_not_mem, one_dvd _, ?_⟩
        have hm2 : 2 ≤ m.1 := hΩ_ge_two m.2
        exact lt_of_lt_of_le Nat.one_lt_two hm2
      · rfl
  let eBoundary : boundaryOutPairs Ω ≃ Ω := Equiv.ofBijective eBoundaryFun heBoundary_bij
  have hprime_at_one : ∀ {p : ℕ}, p.Prime → modifiedFlow p 1 = erdosWeight p := by
    intro p hp
    have hout : outflow modifiedFlow p = modifiedFlow p 1 := by
      unfold outflow
      rw [tsum_eq_single 1]
      intro n hn
      apply hmodified_support p n
      intro h
      rcases h with ⟨hdiv, hlt⟩
      rcases (Nat.dvd_prime hp).1 hdiv with h1 | hp'
      · exact hn h1
      · subst hp'
        exact (lt_irrefl _ hlt).elim
    calc
      modifiedFlow p 1 = outflow modifiedFlow p := hout.symm
      _ = erdosWeight p := hprime_outflow p hp
  have hpointwise : ∀ m : Ω, modifiedFlow m.1 1 = if m.1.Prime then erdosWeight m.1 else 0 := by
    intro m
    by_cases hm : m.1.Prime
    · simp [hm, hprime_at_one hm]
    · have hm2 : 2 ≤ m.1 := hΩ_ge_two m.2
      simp [hm, hcomposite_to_one m.1 hm2 hm]
  let SΩ : Set {p : ℕ // p.Prime} := { p | p.1 ∈ Ω }
  let ePrimeΩFun : {m : Ω // m.1.Prime} → SΩ := fun m => ⟨⟨m.1.1, m.2⟩, m.1.2⟩
  have hePrimeΩ_bij : Function.Bijective ePrimeΩFun := by
    constructor
    · intro a b h
      apply Subtype.ext
      apply Subtype.ext
      simpa [ePrimeΩFun] using congrArg (fun q : SΩ => q.1.1) h
    · intro p
      refine ⟨⟨⟨p.1.1, p.2⟩, p.1.2⟩, ?_⟩
      rfl
  let ePrimeΩ : {m : Ω // m.1.Prime} ≃ SΩ := Equiv.ofBijective ePrimeΩFun hePrimeΩ_bij
  have hboundary_eq :
      boundaryOutflow modifiedFlow Ω = ∑' q : SΩ, erdosWeight q.1.1 := by
    unfold boundaryOutflow
    calc
      ∑' mn : boundaryOutPairs Ω, modifiedFlow mn.1.1 mn.1.2
          = ∑' mn : boundaryOutPairs Ω, modifiedFlow mn.1.1 1 := by
              apply tsum_congr
              intro mn
              simp [hboundary_target_eq_one mn]
      _ = ∑' m : Ω, modifiedFlow m.1 1 := by
            simpa [eBoundary] using (Equiv.tsum_eq eBoundary (fun m : Ω => modifiedFlow m.1 1))
      _ = ∑' m : Ω, if m.1.Prime then erdosWeight m.1 else 0 := by
            apply tsum_congr
            intro m
            exact hpointwise m
      _ = ∑' p : {m : Ω // m.1.Prime}, erdosWeight p.1.1 := by
            symm
            simpa [Set.indicator, Set.mem_setOf_eq] using
              (tsum_subtype {m : Ω | m.1.Prime} (fun m : Ω => erdosWeight m.1))
      _ = ∑' q : SΩ, erdosWeight q.1.1 := by
            simpa [ePrimeΩ] using (Equiv.tsum_eq ePrimeΩ (fun q : SΩ => erdosWeight q.1.1))
  have hnonneg_prime : ∀ p : {p : ℕ // p.Prime}, 0 ≤ erdosWeight p.1 := by
    intro p
    have hp1 : 1 < (p : ℕ) := p.2.one_lt
    have hlog : 0 < Real.log (p : ℝ) := Real.log_pos (Nat.one_lt_cast.2 hp1)
    have hden : 0 ≤ ((p : ℝ) * Real.log p) := by positivity
    simpa [erdosWeight] using one_div_nonneg.mpr hden
  calc
    boundaryOutflow modifiedFlow Ω = ∑' q : SΩ, erdosWeight q.1.1 := hboundary_eq
    _ ≤ ∑' p : {p : ℕ // p.Prime}, erdosWeight p.1 := by
          exact Summable.tsum_subtype_le (fun p : {p : ℕ // p.Prime} => erdosWeight p.1)
            SΩ hnonneg_prime summable_primeWeights
    _ = primeWeightSum := rfl
lemma boundaryOutflow_ge_boundaryInflow_add_tsum_divergence_of_subset
    {A Ω : Set ℕ} (hΩfin : Ω.Finite)
    (hΩ_ge_two : ∀ {r : ℕ}, r ∈ Ω → 2 ≤ r) (hAΩ : A ⊆ Ω) :
    boundaryInflow modifiedFlow Ω +
      (∑' a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) ≤
        boundaryOutflow modifiedFlow Ω := by
  classical
  let f : ℕ → ℝ := fun r => outflow modifiedFlow r - inflow modifiedFlow r
  have htwo : 1 < 2 := by decide
  have hnonneg : ∀ r ∈ Ω, 0 ≤ f r := by
    intro r hr
    exact sub_nonneg.mpr <|
      outflow_modifiedFlow_ge_inflow_modifiedFlow
        (lt_of_lt_of_le htwo (hΩ_ge_two hr))
  have hAfin : A.Finite := hΩfin.subset hAΩ
  letI := hΩfin.fintype
  letI := hAfin.fintype
  let e : A ≃ {r : Ω // (r : ℕ) ∈ A} :=
    { toFun := fun a => ⟨⟨a.1, hAΩ a.2⟩, a.2⟩
      invFun := fun r => ⟨r.1.1, r.2⟩
      left_inv := by
        intro a
        cases a
        rfl
      right_inv := by
        intro r
        apply Subtype.ext
        apply Subtype.ext
        rfl }
  have hAeq :
      (∑' a : A, f (a : ℕ)) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype]
    exact Fintype.sum_equiv e (fun a : A => f (a : ℕ))
      (fun r : {s : Ω // (s : ℕ) ∈ A} => f (r : ℕ)) (by intro a; rfl)
  have hsplit :
      (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
          (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) =
        ∑' r : Ω, f (r : ℕ) := by
    rw [tsum_fintype, tsum_fintype, tsum_fintype]
    simpa using
      (Fintype.sum_subtype_add_sum_subtype (fun r : Ω => (r : ℕ) ∈ A)
        (fun r : Ω => f (r : ℕ)))
  have hcompl_nonneg : 0 ≤ ∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ) := by
    rw [tsum_fintype]
    exact Finset.sum_nonneg fun r _ => by
      simpa using hnonneg (r : ℕ) r.1.2
  have hA_le_Ω :
      (∑' a : A, f (a : ℕ)) ≤ ∑' r : Ω, f (r : ℕ) := by
    calc
      ∑' a : A, f (a : ℕ) = ∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ) := hAeq
      _ ≤ (∑' r : {s : Ω // (s : ℕ) ∈ A}, f (r : ℕ)) +
            (∑' r : {s : Ω // (s : ℕ) ∉ A}, f (r : ℕ)) := by
              linarith
      _ = ∑' r : Ω, f (r : ℕ) := hsplit
  have hΩboundary :
      (∑' r : Ω, f (r : ℕ)) =
        boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
    simpa [f] using
      tsum_outflow_sub_inflow_eq_boundaryOutflow_sub_boundaryInflow (Ω := Ω) hΩfin
  have hmain :
      (∑' a : A, f (a : ℕ)) ≤
        boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := by
    calc
      ∑' a : A, f (a : ℕ) ≤ ∑' r : Ω, f (r : ℕ) := hA_le_Ω
      _ = boundaryOutflow modifiedFlow Ω - boundaryInflow modifiedFlow Ω := hΩboundary
  linarith

lemma flow_into_primitive_member_from_outside_divisorClosure {A : Set ℕ}
    (hA : PrimitiveSet A) {a m : ℕ} (ha : a ∈ A)
    (hflow : modifiedFlow m a ≠ 0) :
    m ∉ primitiveDivisorClosure A := by
  intro hm
  rcases hm with ⟨hm_ge_two, b, hb, hm_dvd_b⟩
  have hdiv_lt : a ∣ m ∧ a < m := by
    by_contra hnot
    exact hflow (modifiedFlow_satisfies_flow_conjecture.1.2 m a hnot)
  have ha_dvd_m : a ∣ m := hdiv_lt.1
  have ha_lt_m : a < m := hdiv_lt.2
  have ha_dvd_b : a ∣ b := dvd_trans ha_dvd_m hm_dvd_b
  have hab_eq : a = b := hA.2 ha hb ha_dvd_b
  have hm_dvd_a : m ∣ a := hab_eq ▸ hm_dvd_b
  have ha_pos : 0 < a := lt_of_lt_of_le Nat.zero_lt_two (hA.1 ha)
  have hm_le_a : m ≤ a := Nat.le_of_dvd ha_pos hm_dvd_a
  exact (not_le_of_gt ha_lt_m) hm_le_a

lemma summable_modifiedFlow_col_of_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : IsPrimePow N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  classical
  let L : ℝ := Real.log N
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  obtain ⟨p, k, hp, hk, hNpow⟩ := (isPrimePow_nat_iff N).mp hPrimePow
  let qp : {q : ℕ // 2 ≤ q} := ⟨p, hp.two_le⟩
  have hN0_nat : N ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hN)
  have hN_pos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0_nat
  have hN_cast : (1 : ℝ) < N := by
    exact_mod_cast hN
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hN_cast
  have hLne : L ≠ 0 := hLpos.ne'
  have hk_ne : k ≠ 0 := Nat.ne_of_gt hk
  have hNp : 1 < N * p := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hp.pos)
  have hNp0_nat : N * p ≠ 0 := Nat.mul_ne_zero hN0_nat hp.ne_zero
  have hNp0 : ((N * p : ℕ) : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hNp0_nat
  have hNpPow : N * p = p ^ (k + 1) := by
    rw [← hNpow, pow_succ]
  have hbase_one :
      baseFlow (N * p) 1 =
        Real.log p / (((N * p : ℕ) : ℝ) * (L + Real.log p) ^ 2) := by
    have hNp_pp : IsPrimePow (N * p) := by
      rw [hNpPow]
      exact (isPrimePow_pow_iff (Nat.succ_ne_zero _)).2 hp.isPrimePow
    have hvm_Np : ArithmeticFunction.vonMangoldt (N * p) = Real.log p := by
      rw [hNpPow, ArithmeticFunction.vonMangoldt_apply_pow (Nat.succ_ne_zero _),
        ArithmeticFunction.vonMangoldt_apply_prime hp]
    have hlog_Np : Real.log (N * p) = L + Real.log p := by
      simpa [L, Nat.cast_mul] using
        (Real.log_mul hN0 (Nat.cast_ne_zero.mpr hp.ne_zero))
    rw [baseFlow, if_pos hNp, if_pos (one_dvd _), Nat.div_one, if_pos hNp_pp]
    simp [hvm_Np, hlog_Np]
  have hmodified_eq_base_of_ne_special :
      ∀ K : ℕ, K ≠ N * p → modifiedFlow K N = baseFlow K N := by
    intro K hKne
    have hfirst :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ K = p' ^ k' ∧ N = 1 := by
      rintro ⟨p', hp', k', hk', hKpow, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ K = p' ^ k' ∧ N = p' ^ (k' - 1) := by
      rintro ⟨p', hp', k', hk', hKpow, hNpow'⟩
      have hk'1 : k' - 1 ≠ 0 := by omega
      have hpow_eq : p ^ k = p' ^ (k' - 1) := by
        rw [hNpow, hNpow']
      rcases hp.pow_inj' hp' hk_ne hk'1 hpow_eq with ⟨hpeq, hk_eq⟩
      have hk'_succ : k' = k + 1 := by omega
      have hKeq : K = N * p := by
        calc
          K = p' ^ k' := hKpow
          _ = p ^ (k + 1) := by rw [hpeq, hk'_succ]
          _ = N * p := by rw [pow_succ, hNpow]
      exact hKne hKeq
    simp [modifiedFlow, hfirst, hsecond]
  have hmodified_at_special :
      modifiedFlow (N * p) N = baseFlow (N * p) N + baseFlow (N * p) 1 := by
    have hfirst :
        ¬ ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ N * p = p' ^ k' ∧ N = 1 := by
      rintro ⟨p', hp', k', hk', hKpow, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ∃ p' : ℕ, p'.Prime ∧ ∃ k' : ℕ, 2 ≤ k' ∧ N * p = p' ^ k' ∧ N = p' ^ (k' - 1) := by
      refine ⟨p, hp, k + 1, by omega, ?_, ?_⟩
      · rw [pow_succ, hNpow]
      · simpa using hNpow.symm
    simp [modifiedFlow, hfirst, hsecond]
  let e : {q : ℕ // 2 ≤ q} → ℕ := fun q => N * q.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Nat.mul_left_cancel hN_pos hab
  have hbase_zero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
    intro K hK
    by_cases hdiv : N ∣ K
    · rcases hdiv with ⟨q, rfl⟩
      by_cases hqge2 : 2 ≤ q
      · exfalso
        exact hK ⟨⟨q, hqge2⟩, rfl⟩
      · have hnotpp : ¬ IsPrimePow q := by
          intro hqpp
          obtain ⟨p', k', hp', hk', hpow⟩ := (isPrimePow_nat_iff q).mp hqpp
          have hk1 : 1 ≤ k' := Nat.succ_le_of_lt hk'
          have h2 : 2 ≤ q := by
            calc
              2 ≤ p' := hp'.two_le
              _ ≤ p' ^ k' := Nat.le_self_pow (show k' ≠ 0 by omega) p'
              _ = q := hpow
          exact hqge2 h2
        by_cases hNq : 1 < N * q
        · simp [baseFlow, hNq, Nat.mul_div_right q hN_pos, hnotpp]
        · simp [baseFlow, hNq]
    · simp [baseFlow, hdiv]
  have hmodified_zero : ∀ K : ℕ, K ∉ Set.range e → modifiedFlow K N = 0 := by
    intro K hK
    have hKne : K ≠ N * p := by
      intro hEq
      exact hK ⟨qp, by simpa [e, qp] using hEq.symm⟩
    simpa [hmodified_eq_base_of_ne_special K hKne] using hbase_zero K hK
  have hbase_mul (q : {q : ℕ // 2 ≤ q}) :
      baseFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hNq : 1 < N * q.1 := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hqnatpos)
    have hdvd : N ∣ N * q.1 := ⟨q.1, by simp⟩
    have hdiv : (N * q.1) / N = q.1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q.1 hN_pos
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    by_cases hqpp : IsPrimePow q.1
    · rw [baseFlow, if_pos hNq, if_pos hdvd]
      have hlog : Real.log (((N * q.1 : ℕ) : ℝ)) = L + Real.log q.1 := by
        simpa [L, Nat.cast_mul] using Real.log_mul hN0' hq0
      exact
        (by
          simpa only [hdiv, hqpp] using
            congrArg
              (fun x =>
                ArithmeticFunction.vonMangoldt q.1 /
                  ((((N * q.1 : ℕ) : ℝ)) * x ^ 2))
              hlog)
    · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact hqpp
      simp [baseFlow, hNq, hdvd, hdiv, hqpp, hvm]
  have hmodified_mul (q : {q : ℕ // 2 ≤ q}) :
      modifiedFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) +
        if q = qp then
          Real.log p / (((N * p : ℕ) : ℝ) * (L + Real.log p) ^ 2)
        else
          0 := by
    by_cases hq : q = qp
    · subst hq
      rw [hmodified_at_special, hbase_mul qp, hbase_one]
      simp [qp]
    · have hKne : N * q.1 ≠ N * p := by
        intro hEq
        apply hq
        apply Subtype.ext
        exact Nat.mul_left_cancel hN_pos hEq
      rw [hmodified_eq_base_of_ne_special (N * q.1) hKne, hbase_mul]
      simp [hq]
  let G : {q : ℕ // 2 ≤ q} → ℝ → ℝ := fun q t =>
    (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) +
        if q = qp then Real.log p / (((N * p : ℕ) : ℝ)) else 0) *
      (t * Real.exp (-((L + Real.log q.1) * t)))
  let fSum : ℝ → ℝ := fun t =>
    (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
      (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
  have hsum_analytic {t : ℝ} (ht : 0 < t) :
      Summable (fun q : {q : ℕ // 2 ≤ q} =>
        ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    let full : ℕ → ℝ := fun n =>
      if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / Real.rpow (n : ℝ) (1 + t)
    have hLs :
        LSeriesSummable (fun n => ↑(ArithmeticFunction.vonMangoldt n)) (1 + t : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using add_lt_add_left ht 1)
    have hsum_full : Summable full := by
      simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hLs.norm
    have hfull_zero :
        ∀ n ∉ Set.range (Subtype.val : {q : ℕ // 2 ≤ q} → ℕ), full n = 0 := by
      intro n hn
      have hnlt2 : n < 2 := by
        by_contra h
        exact hn ⟨⟨n, not_lt.mp h⟩, rfl⟩
      interval_cases n <;> simp [full]
    have hsub : Summable (full ∘ Subtype.val) :=
      (Function.Injective.summable_iff Subtype.val_injective hfull_zero).2 hsum_full
    refine hsub.congr ?_
    intro q
    simp [full, show ((q : ℕ) ≠ 0) by omega]
  have hHas_analytic {t : ℝ} (ht : 0 < t) :
      HasSum
        (fun q : {q : ℕ // 2 ≤ q} =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
        (analyticSeries (1 + t)) := by
    simpa [analyticSeries] using (hsum_analytic ht).hasSum
  have hF_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ))) *
          (t * Real.exp (-((L + Real.log q.1) * t))) =
        ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
          (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log q.1) * t) = -L * t + -(Real.log q.1 * t) by ring, Real.exp_add]
    have hmul : -(Real.log (q.1 : ℝ) * t) = Real.log (q.1 : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hqpos (-t)]
    rw [Real.rpow_neg (le_of_lt hqpos), ← mul_assoc]
    have hrpow : Real.rpow (q.1 : ℝ) (1 + t) = (q.1 : ℝ) * Real.rpow (q.1 : ℝ) t := by
      simpa using (Real.rpow_add hqpos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv, Real.rpow_eq_pow]
    ring_nf
  have hE_term {t : ℝ} (ht : 0 < t) :
      (Real.log p / (((N * p : ℕ) : ℝ))) * (t * Real.exp (-((L + Real.log p) * t))) =
        ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
          (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
    have hppos : 0 < (p : ℝ) := by exact_mod_cast hp.pos
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log p) * t) = -L * t + -(Real.log p * t) by ring, Real.exp_add]
    have hmul : -(Real.log (p : ℝ) * t) = Real.log (p : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hppos (-t)]
    rw [Real.rpow_neg (le_of_lt hppos), ← mul_assoc]
    have hrpow : Real.rpow (p : ℝ) (1 + t) = (p : ℝ) * Real.rpow (p : ℝ) t := by
      simpa using (Real.rpow_add hppos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv, Real.rpow_eq_pow]
    ring_nf
  have hG_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      G q t = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
        (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
          if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0) := by
    by_cases hq : q = qp
    · subst hq
      calc
        G qp t
            = (ArithmeticFunction.vonMangoldt p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) +
              (Real.log p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) := by
                  simp [G, qp, add_mul]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t)) +
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
                rw [hF_term ht qp, hE_term ht]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t) +
                Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
                  rw [← mul_add]
        _ = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt p / Real.rpow (p : ℝ) (1 + t) +
                if qp = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0) := by
                  simp
    · simpa [G, hq] using hF_term ht q
  have hG_hasSum {t : ℝ} (ht : 0 < t) :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => G q t) (fSum t) := by
    have hcorr :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0)
          (Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
      simpa using (hasSum_ite_eq qp (Real.log p / Real.rpow (p : ℝ) (1 + t)))
    have hsum_inner :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
              if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0)
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t)) := by
      exact (hHas_analytic ht).add hcorr
    have hconst :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) +
                if q = qp then Real.log p / Real.rpow (p : ℝ) (1 + t) else 0))
          (((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
            (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))) := by
      simpa [mul_assoc] using
        hsum_inner.mul_left ((1 / (N : ℝ)) * (t * Real.exp (-L * t)))
    convert hconst using 1
    · ext q
      exact hG_term ht q
  have hG_int (q : {q : ℕ // 2 ≤ q}) :
      ∫ t in Set.Ioi (0 : ℝ), G q t = modifiedFlow (N * q.1) N := by
    by_cases hq : q = qp
    · subst hq
      have hb : 0 < L + Real.log p := by
        exact add_pos hLpos (Real.log_pos (by exact_mod_cast hp.one_lt))
      have hkernel :
          ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log p) * t)) =
            (1 / (L + Real.log p)) ^ 2 := by
        have hkernel' :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (1 : ℝ) * Real.exp (-((L + Real.log p) * t)) =
              (1 / (L + Real.log p)) ^ 2 := by
          simpa [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.Gamma_two] using
            (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := L + Real.log p)
              (by norm_num) hb)
        simpa [Real.rpow_one] using hkernel'
      have hGqp :
          G qp =
            fun t : ℝ =>
              (ArithmeticFunction.vonMangoldt p / (((N * p : ℕ) : ℝ)) +
                  Real.log p / (((N * p : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log p) * t))) := by
        funext t
        simp [G, qp, add_mul]
      rw [hGqp, MeasureTheory.integral_const_mul, hkernel, hmodified_mul qp, if_pos rfl]
      simp [qp, ArithmeticFunction.vonMangoldt_apply_prime hp, div_eq_mul_inv]
      field_simp [hNp0, hb.ne']
    · have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      have hNq0_nat : N * q.1 ≠ 0 := Nat.mul_ne_zero hN_pos.ne' (Nat.ne_of_gt hqnatpos)
      have hNq0 : (((N * q.1 : ℕ) : ℝ)) ≠ 0 := by
        exact_mod_cast hNq0_nat
      have hb : 0 < L + Real.log q.1 := by
        have hqcast : (1 : ℝ) < q.1 := by exact_mod_cast q.2
        exact add_pos hLpos (Real.log_pos hqcast)
      have hkernel :
          ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t)) =
            (1 / (L + Real.log q.1)) ^ 2 := by
        have hkernel' :
            ∫ t in Set.Ioi (0 : ℝ), t ^ (1 : ℝ) * Real.exp (-((L + Real.log q.1) * t)) =
              (1 / (L + Real.log q.1)) ^ 2 := by
          simpa [show ((2 : ℝ) - 1) = (1 : ℝ) by norm_num, Real.Gamma_two] using
            (Real.integral_rpow_mul_exp_neg_mul_Ioi (a := (2 : ℝ)) (r := L + Real.log q.1)
              (by norm_num) hb)
        simpa [Real.rpow_one] using hkernel'
      have hGq :
          G q =
            fun t : ℝ =>
              (ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ))) *
                (t * Real.exp (-((L + Real.log q.1) * t))) := by
        funext t
        simp [G, hq]
      rw [hGq, MeasureTheory.integral_const_mul, hkernel, hmodified_mul q, if_neg hq]
      simp [div_eq_mul_inv]
      field_simp [hNq0, hb.ne']
  have hG_meas : ∀ q : {q : ℕ // 2 ≤ q}, MeasureTheory.AEStronglyMeasurable (G q) μ := by
    intro q
    dsimp [G]
    fun_prop
  have h_bound :
      ∀ q : {q : ℕ // 2 ≤ q}, ∀ᵐ t : ℝ ∂μ, ‖G q t‖ ≤ G q t := by
    intro q
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hcoeff_nonneg :
        0 ≤ ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) +
          if q = qp then Real.log p / (((N * p : ℕ) : ℝ)) else 0 := by
      apply add_nonneg
      · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        positivity
      · by_cases hq : q = qp
        · subst hq
          have hp_cast : (1 : ℝ) < p := by
            exact_mod_cast hp.one_lt
          split_ifs with h
          · exact div_nonneg
              (Real.log_pos hp_cast).le
              (by positivity : 0 ≤ (((N * p : ℕ) : ℝ)))
          · contradiction
        · simp [hq]
    have hG_nonneg : 0 ≤ G q t := by
      dsimp [G]
      exact mul_nonneg hcoeff_nonneg (mul_nonneg ht.le (le_of_lt (Real.exp_pos _)))
    calc
      ‖G q t‖ = G q t := Real.norm_of_nonneg hG_nonneg
      _ ≤ G q t := le_rfl
  have h_bound_summable :
      ∀ᵐ t : ℝ ∂μ, Summable (fun q : {q : ℕ // 2 ≤ q} => G q t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hG_hasSum ht).summable
  have h_tsum_eq :
      ∀ᵐ t : ℝ ∂μ, (∑' q : {q : ℕ // 2 ≤ q}, G q t) = fSum t := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hG_hasSum ht).tsum_eq
  have hanalytic_meas :
      AEMeasurable (fun t : ℝ => analyticSeries (1 + t)) μ := by
    let Aq : {q : ℕ // 2 ≤ q} → ℝ → NNReal := fun q t =>
      Real.toNNReal (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
    have hAq_meas : ∀ q : {q : ℕ // 2 ≤ q}, Measurable (Aq q) := by
      intro q
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (show q.1 ≠ 0 by omega)
      have hpow_meas : Measurable (fun t : ℝ => (q.1 : ℝ) ^ (1 + t)) :=
        ((Real.continuous_const_rpow hq0).comp (continuous_const.add continuous_id)).measurable
      exact (measurable_const.div hpow_meas).real_toNNReal
    have htsum : Measurable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, Aq q t) :=
      Measurable.nnreal_tsum hAq_meas
    refine htsum.coe_nnreal_real.aemeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hnonneg :
        ∀ q : {q : ℕ // 2 ≤ q},
          0 ≤ ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ) ^ (1 + t) := by
      intro q
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hqnatpos) _)
    calc
      ↑(∑' q : {q : ℕ // 2 ≤ q}, Aq q t)
          = ∑' q : {q : ℕ // 2 ≤ q}, (Aq q t : ℝ) := by
              rw [NNReal.coe_tsum]
      _ = ∑' q : {q : ℕ // 2 ≤ q},
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) := by
              refine tsum_congr ?_
              intro q
              dsimp [Aq]
              calc
                (Real.toNNReal
                    (ArithmeticFunction.vonMangoldt q.1 /
                      Real.rpow (q.1 : ℝ) (1 + t)) : ℝ)
                    =
                    max
                      (ArithmeticFunction.vonMangoldt q.1 /
                        Real.rpow (q.1 : ℝ) (1 + t))
                      0 := by
                        exact Real.coe_toNNReal' _
                _ = ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) :=
                  max_eq_left (hnonneg q)
      _ = analyticSeries (1 + t) := by
            exact (hHas_analytic ht).tsum_eq
  have hfSum_meas : AEMeasurable fSum μ := by
    have hfactor_meas :
        AEMeasurable (fun t : ℝ => (1 / (N : ℝ)) * (t * Real.exp (-L * t))) μ := by
      fun_prop
    have hcorr_meas :
        AEMeasurable (fun t : ℝ => Real.log p / Real.rpow (p : ℝ) (1 + t)) μ := by
      have hpow_cont : Continuous (fun t : ℝ => Real.rpow (p : ℝ) (1 + t)) :=
        (Real.continuous_const_rpow (Nat.cast_ne_zero.mpr hp.ne_zero)).comp
          (continuous_const.add continuous_id)
      exact (continuous_const.div hpow_cont
        (fun t => (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _).ne')).aemeasurable
    simpa [fSum] using hfactor_meas.mul (hanalytic_meas.add hcorr_meas)
  have hsimple_int :
      MeasureTheory.Integrable (fun t : ℝ => (1 / (N : ℝ)) * Real.exp (-L * t)) μ := by
    simpa [μ, MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (exp_neg_integrableOn_Ioi 0 hLpos).const_mul (1 / (N : ℝ))
  have hfSum_bound :
      ∀ᵐ t : ℝ ∂μ, ‖fSum t‖ ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log p / Real.rpow (p : ℝ) (1 + t) := by
      exact div_nonneg
        (Real.log_pos (by exact_mod_cast hp.one_lt)).le
        (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _))
    have hA_le :
        analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t) ≤ 1 / t := by
      have ht' : 1 < 1 + t := by linarith
      convert analyticSeries_add_log_term_le ht' hp using 1
      · ring_nf
    have hf_nonneg : 0 ≤ fSum t := by
      dsimp [fSum]
      exact mul_nonneg
        (by positivity)
        (add_nonneg hA_nonneg hcorr_nonneg)
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_le :
      ∀ᵐ t : ℝ ∂μ, fSum t ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log p / Real.rpow (p : ℝ) (1 + t) := by
      exact div_nonneg
        (Real.log_pos (by exact_mod_cast hp.one_lt)).le
        (le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hp.pos) _))
    have hA_le :
        analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t) ≤ 1 / t := by
      have ht' : 1 < 1 + t := by linarith
      convert analyticSeries_add_log_term_le ht' hp using 1
      · ring_nf
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) *
          (analyticSeries (1 + t) + Real.log p / Real.rpow (p : ℝ) (1 + t))
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_int : MeasureTheory.Integrable fSum μ :=
    hsimple_int.mono' hfSum_meas.aestronglyMeasurable hfSum_bound
  have h_tsum_eq_ae :
      (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, G q t) =ᵐ[μ] fSum := h_tsum_eq
  have h_bound_integrable :
      MeasureTheory.Integrable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, G q t) μ :=
    hfSum_int.congr h_tsum_eq_ae.symm
  have h_hasSum_ae :
      ∀ᵐ t : ℝ ∂μ, HasSum (fun q : {q : ℕ // 2 ≤ q} => G q t) (fSum t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hG_hasSum ht
  have hIntHasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => ∫ t, G q t ∂μ) (∫ t, fSum t ∂μ) :=
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (bound := G) hG_meas h_bound h_bound_summable h_bound_integrable h_hasSum_ae
  have hsub_hasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => modifiedFlow (N * q.1) N) (∫ t, fSum t ∂μ) := by
    exact hIntHasSum.congr_fun fun q => (hG_int q).symm
  have hmodified_hasSum :
      HasSum (fun K : ℕ => modifiedFlow K N) (∫ t, fSum t ∂μ) :=
    (Function.Injective.hasSum_iff he hmodified_zero).mp hsub_hasSum
  exact hmodified_hasSum.summable

lemma summable_modifiedFlow_col_of_not_isPrimePow {N : ℕ} (hN : 1 < N)
    (hPrimePow : ¬ IsPrimePow N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  classical
  let L : ℝ := Real.log N
  let μ := MeasureTheory.volume.restrict (Set.Ioi (0 : ℝ))
  have hN0_nat : N ≠ 0 := ne_of_gt (lt_trans Nat.zero_lt_one hN)
  have hN_pos : 0 < N := lt_trans Nat.zero_lt_one hN
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hN0_nat
  have hN_cast : (1 : ℝ) < N := by
    exact_mod_cast hN
  have hLpos : 0 < L := by
    dsimp [L]
    exact Real.log_pos hN_cast
  have hLne : L ≠ 0 := hLpos.ne'
  have hmodified_eq_base : ∀ K : ℕ, modifiedFlow K N = baseFlow K N := by
    intro K
    rw [modifiedFlow]
    have hfirst :
        ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ K = p ^ x ∧ N = 1 := by
      rintro ⟨p, hp, x, hx, hK, hN1⟩
      exact (ne_of_gt hN) hN1
    have hsecond :
        ¬ ∃ p : ℕ, p.Prime ∧ ∃ x : ℕ, 2 ≤ x ∧ K = p ^ x ∧ N = p ^ (x - 1) := by
      rintro ⟨p, hp, x, hx, hK, hNpow⟩
      have hk1 : x - 1 ≠ 0 := by omega
      exact hPrimePow <| hNpow.symm ▸ (isPrimePow_pow_iff hk1).2 hp.isPrimePow
    simp [hfirst, hsecond]
  let e : {q : ℕ // 2 ≤ q} → ℕ := fun q => N * q.1
  have he : Function.Injective e := by
    intro a b hab
    apply Subtype.ext
    exact Nat.mul_left_cancel hN_pos hab
  have hbase_zero : ∀ K : ℕ, K ∉ Set.range e → baseFlow K N = 0 := by
    intro K hK
    by_cases hdiv : N ∣ K
    · rcases hdiv with ⟨q, rfl⟩
      by_cases hqge2 : 2 ≤ q
      · exfalso
        exact hK ⟨⟨q, hqge2⟩, rfl⟩
      · have hnotpp : ¬ IsPrimePow q := by
          intro hqpp
          exact hqge2 <| Nat.succ_le_of_lt <| IsPrimePow.one_lt hqpp
        by_cases hNq : 1 < N * q
        · simp [baseFlow, hNq, Nat.mul_div_right q hN_pos, hnotpp]
        · simp [baseFlow, hNq]
    · simp [baseFlow, hdiv]
  have hbase_mul (q : {q : ℕ // 2 ≤ q}) :
      baseFlow (N * q.1) N =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hNq : 1 < N * q.1 := lt_of_lt_of_le hN (Nat.le_mul_of_pos_right N hqnatpos)
    have hdvd : N ∣ N * q.1 := ⟨q.1, by simp⟩
    have hdiv : (N * q.1) / N = q.1 := by
      simpa [Nat.mul_comm] using Nat.mul_div_right q.1 hN_pos
    have hN0' : (N : ℝ) ≠ 0 := by exact_mod_cast hN_pos.ne'
    have hq0 : (q.1 : ℝ) ≠ 0 := by
      exact_mod_cast (show q.1 ≠ 0 by omega)
    by_cases hqpp : IsPrimePow q.1
    · rw [baseFlow, if_pos hNq, if_pos hdvd]
      have hlog : Real.log (((N * q.1 : ℕ) : ℝ)) = L + Real.log q.1 := by
        simpa [L, Nat.cast_mul] using Real.log_mul hN0' hq0
      exact
        (by
          simpa only [hdiv, hqpp] using
            congrArg
              (fun x =>
                ArithmeticFunction.vonMangoldt q.1 /
                  ((((N * q.1 : ℕ) : ℝ)) * x ^ 2))
              hlog)
    · have hvm : ArithmeticFunction.vonMangoldt q.1 = 0 := by
        rw [ArithmeticFunction.vonMangoldt_eq_zero_iff]
        exact hqpp
      simp [baseFlow, hNq, hdvd, hdiv, hqpp, hvm]
  let F : {q : ℕ // 2 ≤ q} → ℝ → ℝ := fun q t =>
    ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
      (t * Real.exp (-((L + Real.log q.1) * t)))
  let fSum : ℝ → ℝ := fun t =>
    (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * analyticSeries (1 + t)
  have hsum_analytic {t : ℝ} (ht : 0 < t) :
      Summable (fun q : {q : ℕ // 2 ≤ q} =>
        ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    let full : ℕ → ℝ := fun n =>
      if n = 0 then 0 else ArithmeticFunction.vonMangoldt n / Real.rpow (n : ℝ) (1 + t)
    have hLs :
        LSeriesSummable (fun n => ↑(ArithmeticFunction.vonMangoldt n)) (1 + t : ℂ) :=
      ArithmeticFunction.LSeriesSummable_vonMangoldt (by simpa using add_lt_add_left ht 1)
    have hsum_full : Summable full := by
      simpa [full, LSeries.norm_term_eq, Real.norm_eq_abs,
        abs_of_nonneg ArithmeticFunction.vonMangoldt_nonneg] using hLs.norm
    have hfull_zero :
        ∀ n ∉ Set.range (Subtype.val : {q : ℕ // 2 ≤ q} → ℕ), full n = 0 := by
      intro n hn
      have hnlt2 : n < 2 := by
        by_contra h
        exact hn ⟨⟨n, not_lt.mp h⟩, rfl⟩
      interval_cases n <;> simp [full]
    have hsub : Summable (full ∘ Subtype.val) :=
      (Function.Injective.summable_iff Subtype.val_injective hfull_zero).2 hsum_full
    refine hsub.congr ?_
    intro q
    simp [full, show ((q : ℕ) ≠ 0) by omega]
  have hHas_analytic {t : ℝ} (ht : 0 < t) :
      HasSum
        (fun q : {q : ℕ // 2 ≤ q} =>
          ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
        (analyticSeries (1 + t)) := by
    simpa [analyticSeries] using (hsum_analytic ht).hasSum
  have hF_term {t : ℝ} (ht : 0 < t) (q : {q : ℕ // 2 ≤ q}) :
      F q t = ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
        (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    dsimp [F]
    rw [Nat.cast_mul, div_eq_mul_inv, div_eq_mul_inv]
    rw [show -((L + Real.log q.1) * t) = -L * t + -(Real.log q.1 * t) by ring, Real.exp_add]
    have hmul : -(Real.log (q.1 : ℝ) * t) = Real.log (q.1 : ℝ) * (-t) := by ring
    rw [hmul, ← Real.rpow_def_of_pos hqpos (-t)]
    rw [Real.rpow_neg (le_of_lt hqpos), ← mul_assoc]
    have hrpow : (q.1 : ℝ) ^ (1 + t) = (q.1 : ℝ) * (q.1 : ℝ) ^ t := by
      simpa using (Real.rpow_add hqpos (1 : ℝ) t)
    rw [hrpow, div_eq_mul_inv]
    field_simp [hN0, hqpos.ne', (Real.rpow_pos_of_pos hqpos t).ne']
  have hF_hasSum {t : ℝ} (ht : 0 < t) :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => F q t) (fSum t) := by
    have hconst :
        HasSum
          (fun q : {q : ℕ // 2 ≤ q} =>
            ((1 / (N : ℝ)) * (t * Real.exp (-L * t))) *
              (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t)))
          (((1 / (N : ℝ)) * (t * Real.exp (-L * t))) * analyticSeries (1 + t)) := by
      simpa [mul_assoc] using
        (hHas_analytic ht).mul_left ((1 / (N : ℝ)) * (t * Real.exp (-L * t)))
    exact hconst.congr_fun fun q => hF_term ht q
  have hF_int (q : {q : ℕ // 2 ≤ q}) :
      ∫ t in Set.Ioi (0 : ℝ), F q t =
        ArithmeticFunction.vonMangoldt q.1 /
          (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
    have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
    have hqpos : 0 < (q.1 : ℝ) := by exact_mod_cast hqnatpos
    have hqgt1 : (1 : ℝ) < q.1 := by
      have hqge2 : (2 : ℝ) ≤ q.1 := by exact_mod_cast q.2
      linarith
    have hb : 0 < L + Real.log q.1 := by
      exact add_pos hLpos (Real.log_pos hqgt1)
    calc
      ∫ t in Set.Ioi (0 : ℝ), F q t
          = ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
              ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t)) := by
                simp [F, MeasureTheory.integral_const_mul]
      _ = ArithmeticFunction.vonMangoldt q.1 / (((N * q.1 : ℕ) : ℝ)) *
            (L + Real.log q.1) ^ (-2 : ℝ) := by
              congr 1
              calc
                ∫ t in Set.Ioi (0 : ℝ), t * Real.exp (-((L + Real.log q.1) * t))
                    = (L + Real.log q.1) ^ (-(1 + 1) / (1 : ℝ)) *
                        (1 / (1 : ℝ)) * Real.Gamma ((1 + 1) / (1 : ℝ)) := by
                          convert
                            (integral_rpow_mul_exp_neg_mul_rpow (p := 1) (q := 1)
                              zero_lt_one (by norm_num) hb) using 1
                          · refine MeasureTheory.setIntegral_congr_fun measurableSet_Ioi ?_
                            intro t ht
                            have hlin : -((L + Real.log q.1) * t) = (-Real.log q.1 + -L) * t := by
                              ring
                            simp [hlin]
                _ = (L + Real.log q.1) ^ (-2 : ℝ) := by
                      have htwo : ((1 + 1 : ℝ) / (1 : ℝ)) = 2 := by norm_num
                      rw [htwo, Real.Gamma_two]
                      norm_num
      _ = ArithmeticFunction.vonMangoldt q.1 /
            (((N * q.1 : ℕ) : ℝ) * (L + Real.log q.1) ^ 2) := by
              have hNq0 : (((N * q.1 : ℕ) : ℝ)) ≠ 0 := by
                exact_mod_cast (Nat.mul_pos hN_pos hqnatpos).ne'
              rw [show (-2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg (le_of_lt hb)]
              field_simp [hNq0, hb.ne']
              have hsquare :
                  (L + Real.log q.1) ^ 2 =
                    L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2 := by
                ring
              have hsquareR :
                  (L + Real.log q.1) ^ (2 : ℝ) =
                    L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2 := by
                simpa [Real.rpow_natCast] using hsquare
              have haux :
                ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                    ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                    ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                    = ArithmeticFunction.vonMangoldt q.1 *
                      (L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2) := by
                        ring
              have hcalc :
                ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                    ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                    ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                    = ArithmeticFunction.vonMangoldt q.1 * (L + Real.log q.1) ^ (2 : ℝ) := by
                      calc
                        ArithmeticFunction.vonMangoldt q.1 * L * Real.log q.1 * 2 +
                            ArithmeticFunction.vonMangoldt q.1 * L ^ 2 +
                            ArithmeticFunction.vonMangoldt q.1 * Real.log q.1 ^ 2
                            = ArithmeticFunction.vonMangoldt q.1 *
                              (L ^ 2 + 2 * L * Real.log q.1 + (Real.log q.1) ^ 2) := haux
                        _ = ArithmeticFunction.vonMangoldt q.1 * (L + Real.log q.1) ^ (2 : ℝ) := by
                              rw [hsquareR]
              simp
  have hF_meas : ∀ q : {q : ℕ // 2 ≤ q}, MeasureTheory.AEStronglyMeasurable (F q) μ := by
    intro q
    dsimp [F]
    fun_prop
  have h_bound :
      ∀ q : {q : ℕ // 2 ≤ q}, ∀ᵐ t : ℝ ∂μ, ‖F q t‖ ≤ F q t := by
    intro q
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hF_nonneg : 0 ≤ F q t := by
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      dsimp [F]
      apply mul_nonneg
      · apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
        positivity
      · exact mul_nonneg ht.le (le_of_lt (Real.exp_pos _))
    simp [Real.norm_eq_abs, abs_of_nonneg hF_nonneg]
  have h_bound_summable :
      ∀ᵐ t : ℝ ∂μ, Summable (fun q : {q : ℕ // 2 ≤ q} => F q t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact (hF_hasSum ht).summable
  have h_hasSum_ae :
      ∀ᵐ t : ℝ ∂μ, HasSum (fun q : {q : ℕ // 2 ≤ q} => F q t) (fSum t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    exact hF_hasSum ht
  have h_tsum_eq :
      ∀ᵐ t : ℝ ∂μ, (∑' q : {q : ℕ // 2 ≤ q}, F q t) = fSum t := by
    filter_upwards [h_hasSum_ae] with t ht
    exact ht.tsum_eq
  have hanalytic_meas :
      AEMeasurable (fun t : ℝ => analyticSeries (1 + t)) μ := by
    let Aq : {q : ℕ // 2 ≤ q} → ℝ → NNReal := fun q t =>
      Real.toNNReal (ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t))
    have hAq_meas : ∀ q : {q : ℕ // 2 ≤ q}, Measurable (Aq q) := by
      intro q
      have hq0 : (q.1 : ℝ) ≠ 0 := by
        exact_mod_cast (show q.1 ≠ 0 by omega)
      have hpow_meas : Measurable (fun t : ℝ => (q.1 : ℝ) ^ (1 + t)) :=
        ((Real.continuous_const_rpow hq0).comp (continuous_const.add continuous_id)).measurable
      exact (measurable_const.div hpow_meas).real_toNNReal
    have htsum : Measurable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, Aq q t) :=
      Measurable.nnreal_tsum hAq_meas
    refine htsum.coe_nnreal_real.aemeasurable.congr ?_
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have hnonneg :
        ∀ q : {q : ℕ // 2 ≤ q},
          0 ≤ ArithmeticFunction.vonMangoldt q.1 / (q.1 : ℝ) ^ (1 + t) := by
      intro q
      apply div_nonneg ArithmeticFunction.vonMangoldt_nonneg
      have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
      exact le_of_lt (Real.rpow_pos_of_pos (by exact_mod_cast hqnatpos) _)
    calc
      ↑(∑' q : {q : ℕ // 2 ≤ q}, Aq q t)
          = ∑' q : {q : ℕ // 2 ≤ q}, (Aq q t : ℝ) := by
              rw [NNReal.coe_tsum]
      _ = ∑' q : {q : ℕ // 2 ≤ q},
            ArithmeticFunction.vonMangoldt q.1 / Real.rpow (q.1 : ℝ) (1 + t) := by
              refine tsum_congr ?_
              intro q
              dsimp [Aq]
              simp [max_eq_left (hnonneg q)]
      _ = analyticSeries (1 + t) := by
            simp [analyticSeries]
  have hfSum_meas : AEMeasurable fSum μ := by
    have hfactor_meas : AEMeasurable (fun t : ℝ => (1 / (N : ℝ)) * (t * Real.exp (-L * t))) μ := by
      fun_prop
    simpa [fSum] using hfactor_meas.mul hanalytic_meas
  have hsimple_int :
      MeasureTheory.Integrable (fun t : ℝ => (1 / (N : ℝ)) * Real.exp (-L * t)) μ := by
    simpa [μ, MeasureTheory.IntegrableOn, mul_assoc, mul_left_comm, mul_comm] using
      (exp_neg_integrableOn_Ioi 0 hLpos).const_mul (1 / (N : ℝ))
  have hfSum_bound :
      ∀ᵐ t : ℝ ∂μ, ‖fSum t‖ ≤ (1 / (N : ℝ)) * Real.exp (-L * t) := by
    filter_upwards [MeasureTheory.ae_restrict_mem measurableSet_Ioi] with t ht
    have ht0 : 0 < t := ht
    have hA_nonneg : 0 ≤ analyticSeries (1 + t) := by
      rw [analyticSeries]
      exact tsum_nonneg fun q =>
        div_nonneg ArithmeticFunction.vonMangoldt_nonneg <|
          le_of_lt <| Real.rpow_pos_of_pos (by
            have hqnatpos : 0 < q.1 := lt_of_lt_of_le Nat.zero_lt_two q.2
            exact_mod_cast hqnatpos) _
    have hcorr_nonneg :
        0 ≤ Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
      have hlog2 : 0 < Real.log (2 : ℝ) := Real.log_pos (by norm_num)
      exact div_nonneg hlog2.le (le_of_lt (Real.rpow_pos_of_pos (by norm_num) _))
    have hA_le : analyticSeries (1 + t) ≤ 1 / t := by
      have hs : 1 < 1 + t := by linarith
      have hmain :
          analyticSeries (1 + t) + Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) ≤ 1 / t := by
        simpa using (analyticSeries_add_log_term_le hs Nat.prime_two)
      calc
        analyticSeries (1 + t)
            ≤ analyticSeries (1 + t) + Real.log (2 : ℝ) / Real.rpow (2 : ℝ) (1 + t) := by
              linarith
        _ ≤ 1 / t := hmain
    have hf_nonneg : 0 ≤ fSum t := by
      dsimp [fSum]
      exact mul_nonneg
        (by positivity)
        hA_nonneg
    rw [Real.norm_eq_abs, abs_of_nonneg hf_nonneg]
    dsimp [fSum]
    have hfac_nonneg : 0 ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) := by
      apply mul_nonneg
      · positivity
      · exact mul_nonneg ht0.le (le_of_lt (Real.exp_pos _))
    calc
      (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * analyticSeries (1 + t)
          ≤ (1 / (N : ℝ)) * (t * Real.exp (-L * t)) * (1 / t) := by
            gcongr
      _ = (1 / (N : ℝ)) * Real.exp (-L * t) := by
            field_simp [ht0.ne']
  have hfSum_int : MeasureTheory.Integrable fSum μ :=
    hsimple_int.mono' hfSum_meas.aestronglyMeasurable hfSum_bound
  have h_bound_integrable :
      MeasureTheory.Integrable (fun t : ℝ => ∑' q : {q : ℕ // 2 ≤ q}, F q t) μ :=
    hfSum_int.congr (h_tsum_eq.mono fun t ht => ht.symm)
  have hIntHasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => ∫ t, F q t ∂μ) (∫ t, fSum t ∂μ) :=
    MeasureTheory.hasSum_integral_of_dominated_convergence
      (bound := F) hF_meas h_bound h_bound_summable h_bound_integrable h_hasSum_ae
  have hsub_hasSum :
      HasSum (fun q : {q : ℕ // 2 ≤ q} => baseFlow (N * q.1) N) (∫ t, fSum t ∂μ) := by
    exact hIntHasSum.congr_fun fun q => (hbase_mul q).trans (hF_int q).symm
  have hbase_hasSum :
      HasSum (fun K : ℕ => baseFlow K N) (∫ t, fSum t ∂μ) :=
    (Function.Injective.hasSum_iff he hbase_zero).mp hsub_hasSum
  have hmodified_hasSum : HasSum (fun K : ℕ => modifiedFlow K N) (∫ t, fSum t ∂μ) := by
    simpa [hmodified_eq_base] using hbase_hasSum
  exact hmodified_hasSum.summable

lemma summable_modifiedFlow_col2 {N : ℕ} (hN : 2 ≤ N) :
    Summable (fun K : ℕ => modifiedFlow K N) := by
  have hN' : 1 < N := lt_of_lt_of_le Nat.one_lt_two hN
  by_cases hPrimePow : IsPrimePow N
  · exact summable_modifiedFlow_col_of_isPrimePow hN' hPrimePow
  · exact summable_modifiedFlow_col_of_not_isPrimePow hN' hPrimePow

lemma primitiveWeightSum_le_primeWeightSum_of_finite {A : Set ℕ}
    (hA : PrimitiveSet A) (hfin : A.Finite) :
    primitiveWeightSum A ≤ primeWeightSum := by
  classical
  let Ω := primitiveDivisorClosure A
  have hΩspec := primitiveDivisorClosure_spec_of_finite hA hfin
  rcases hΩspec with ⟨hΩfin, hAΩ, hΩdown⟩
  have hΩ_ge_two : ∀ {d : ℕ}, d ∈ primitiveDivisorClosure A → 2 ≤ d := by
    intro d hd
    have hd' : 2 ≤ d ∧ ∃ a ∈ A, d ∣ a := by
      simpa [primitiveDivisorClosure] using hd
    exact hd'.1
  have hOut :      boundaryOutflow modifiedFlow (primitiveDivisorClosure A) ≤ primeWeightSum := by
    exact boundaryOutflow_le_primeWeightSum_of_downwardClosed hΩ_ge_two hΩdown
  have hBoundary :
      boundaryInflow modifiedFlow Ω +
        (∑' a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) ≤
          boundaryOutflow modifiedFlow Ω := by
    exact
      boundaryOutflow_ge_boundaryInflow_add_tsum_divergence_of_subset hΩfin hΩ_ge_two hAΩ
  have hIn :
      ∀ {a m : ℕ}, a ∈ A → modifiedFlow m a ≠ 0 → m ∉ Ω := by
    intro a m ha hflow
    exact flow_into_primitive_member_from_outside_divisorClosure hA ha hflow
  have hcol_summable :
      ∀ {N : ℕ}, 2 ≤ N → Summable (fun K : ℕ => modifiedFlow K N) := by
    intro N hN
    exact summable_modifiedFlow_col2 hN
  have hOut_eq :
      ∀ a : A, outflow modifiedFlow (a : ℕ) = erdosWeight (a : ℕ) := by
    intro a
    exact outflow_modifiedFlow_eq_erdosWeight (lt_of_lt_of_le Nat.one_lt_two (hA.1 a.2))
  have hWeight :
      primitiveWeightSum A = ∑' a : A, outflow modifiedFlow (a : ℕ) := by
    unfold primitiveWeightSum
    apply tsum_congr
    intro a
    simpa using (hOut_eq a).symm
  have hIn_nonneg : ∀ a : A, 0 ≤ inflow modifiedFlow (a : ℕ) := by
    intro a
    unfold inflow
    exact tsum_nonneg fun m => modifiedFlow_nonneg m a
  have hIn_le :
      (∑' a : A, inflow modifiedFlow (a : ℕ)) ≤ boundaryInflow modifiedFlow Ω := by
    let G : boundaryInPairs Ω → ℝ := fun mn => modifiedFlow mn.1.1 mn.1.2
    let T : A → Set (boundaryInPairs Ω) := fun a => { mn | mn.1.2 = (a : ℕ) }
    have hfiber :
        ∀ a : A, inflow modifiedFlow (a : ℕ) = ∑' mn : T a, G mn := by
      intro a
      let S : Set {m : ℕ // m ∉ Ω} := { m | (a : ℕ) ∣ m.1 ∧ (a : ℕ) < m.1 }
      have hOutside :
          inflow modifiedFlow (a : ℕ) =
            ∑' m : {m : ℕ // m ∉ Ω}, modifiedFlow m.1 (a : ℕ) := by
        have hsupport :
            Function.support (fun m : ℕ => modifiedFlow m (a : ℕ)) ⊆ { m | m ∉ Ω } := by
          intro m hm
          exact hIn a.2 hm
        symm
        simpa [inflow, Ω] using (tsum_subtype_eq_of_support_subset hsupport)
      have hSupportS :
          Function.support (fun m : {m : ℕ // m ∉ Ω} => modifiedFlow m.1 (a : ℕ)) ⊆ S := by
        intro m hm
        change (a : ℕ) ∣ m.1 ∧ (a : ℕ) < m.1
        by_contra hnot
        exact hm (by
          apply modifiedFlow_eq_zero_of_not_dvd_lt
          exact hnot)
      have hS :
          (∑' m : {m : ℕ // m ∉ Ω}, modifiedFlow m.1 (a : ℕ)) =
            ∑' m : S, modifiedFlow m.1.1 (a : ℕ) := by
        symm
        simpa [S] using (tsum_subtype_eq_of_support_subset hSupportS)
      let f : S → T a := fun m =>
        ⟨⟨(m.1.1, a.1), by
          exact ⟨m.1.2, hAΩ a.2, m.2.1, m.2.2⟩⟩, rfl⟩
      have hf_inj : Function.Injective f := by
        intro m₁ m₂ h
        apply Subtype.ext
        apply Subtype.ext
        simpa using congrArg (fun z : T a => z.1.1.1) h
      have hf_surj : Function.Surjective f := by
        intro mn
        rcases mn with ⟨⟨⟨m, n⟩, hmn⟩, hna⟩
        rcases hmn with ⟨hm, _, hdiv, hlt⟩
        cases hna
        refine ⟨⟨⟨m, hm⟩, ?_⟩, ?_⟩
        · simpa [S] using And.intro hdiv hlt
        · apply Subtype.ext
          apply Subtype.ext
          rfl
      let e : S ≃ T a := Equiv.ofBijective f ⟨hf_inj, hf_surj⟩
      have hT :
          (∑' m : S, modifiedFlow m.1.1 (a : ℕ)) =
            ∑' mn : T a, G mn := by
        simpa [e, G] using
          (Equiv.tsum_eq e (fun mn : T a => G mn))
      exact hOutside.trans (hS.trans hT)
    have hnonnegT : ∀ a : A, 0 ≤ ∑' mn : T a, G mn := by
      intro a
      rw [← hfiber a]
      exact hIn_nonneg a
    have hpairwise : Set.PairwiseDisjoint (Set.univ : Set A) T := by
      intro a _ b _ hab
      refine Set.disjoint_left.2 ?_
      intro mn hma hmb
      exact hab <| Subtype.ext (hma.symm.trans hmb)
    have hunion :
        (∑' mn : ⋃ a : A, T a, ENNReal.ofReal (G mn)) =
          ∑' a : A, ∑' mn : T a, ENNReal.ofReal (G mn) := by
      simpa using (ENNReal.tsum_biUnion hpairwise (f := fun mn => ENNReal.ofReal (G mn)))
    have hsub :
        (∑' mn : ⋃ a : A, T a, ENNReal.ofReal (G mn)) ≤
          ∑' mn : boundaryInPairs Ω, ENNReal.ofReal (G mn) := by
      simpa using
        (ENNReal.tsum_comp_le_tsum_of_injective
          (f := (Subtype.val : (⋃ a : A, T a) → boundaryInPairs Ω))
          Subtype.val_injective
          (fun mn : boundaryInPairs Ω => ENNReal.ofReal (G mn)))
    have hfiberENN :
        ∀ a : A, ENNReal.ofReal (inflow modifiedFlow (a : ℕ)) =
          ∑' mn : T a, ENNReal.ofReal (G mn) := by
      intro a
      rw [hfiber a]
      refine ENNReal.ofReal_tsum_of_nonneg ?_ ?_
      · intro mn
        exact modifiedFlow_nonneg mn.1.1.1 mn.1.1.2
      · have hscol := hcol_summable (hA.1 a.2)
        have hsource_inj :
            Function.Injective (fun mn : T a => mn.1.1.1) := by
          intro x y hxy
          apply Subtype.ext
          apply Subtype.ext
          apply Prod.ext
          · exact hxy
          · exact x.2.trans y.2.symm
        have hscol' : Summable (fun mn : T a => modifiedFlow mn.1.1.1 (a : ℕ)) := by
          simpa using hscol.comp_injective hsource_inj
        have hEq :
            (fun mn : T a => modifiedFlow mn.1.1.1 (a : ℕ)) =
              fun mn : T a => modifiedFlow mn.1.1.1 mn.1.1.2 := by
          funext mn
          rcases mn with ⟨⟨⟨m, n⟩, hmn⟩, hna⟩
          cases hna
          rfl
        exact hEq ▸ hscol'
    have hleft :
        ENNReal.ofReal (∑' a : A, inflow modifiedFlow (a : ℕ)) ≤
          ∑' mn : boundaryInPairs Ω, ENNReal.ofReal (G mn) := by
      calc
        ENNReal.ofReal (∑' a : A, inflow modifiedFlow (a : ℕ))
            = ∑' a : A, ENNReal.ofReal (inflow modifiedFlow (a : ℕ)) := by
                refine ENNReal.ofReal_tsum_of_nonneg ?_ ?_
                · intro a
                  exact hIn_nonneg a
                · letI := hfin.fintype
                  apply Summable.of_finite
        _ = ∑' a : A, ∑' mn : T a, ENNReal.ofReal (G mn) := by
              apply tsum_congr
              intro a
              exact hfiberENN a
        _ = ∑' mn : ⋃ a : A, T a, ENNReal.ofReal (G mn) := by
              rw [hunion]
        _ ≤ ∑' mn : boundaryInPairs Ω, ENNReal.ofReal (G mn) := hsub
    have hright :
        ∑' mn : boundaryInPairs Ω, ENNReal.ofReal (G mn) =
          ENNReal.ofReal (boundaryInflow modifiedFlow Ω) := by
      unfold boundaryInflow G
      refine (ENNReal.ofReal_tsum_of_nonneg ?_ ?_).symm
      · intro mn
        exact modifiedFlow_nonneg mn.1.1 mn.1.2
      · let U : Ω → Set (boundaryInPairs Ω) := fun r => { mn | mn.1.2 = (r : ℕ) }
        have hpart : ∀ mn : boundaryInPairs Ω, ∃! r : Ω, mn ∈ U r := by
          intro mn
          refine ⟨⟨mn.1.2, ?_⟩, by simp [U], ?_⟩
          · rcases mn.2 with ⟨_, hn, _, _⟩
            exact hn
          · intro r hr
            apply Subtype.ext
            simpa [U] using hr.symm
        have hU_summable : ∀ r : Ω, Summable (fun mn : U r => modifiedFlow mn.1.1.1 mn.1.1.2) := by
          intro r
          have hscol := hcol_summable (hΩ_ge_two r.2)
          have hsource_inj :
              Function.Injective (fun mn : U r => mn.1.1.1) := by
            intro x y hxy
            apply Subtype.ext
            apply Subtype.ext
            apply Prod.ext
            · exact hxy
            · exact x.2.trans y.2.symm
          have hscol' : Summable (fun mn : U r => modifiedFlow mn.1.1.1 (r : ℕ)) := by
            simpa using hscol.comp_injective hsource_inj
          have hEq :
              (fun mn : U r => modifiedFlow mn.1.1.1 (r : ℕ)) =
                fun mn : U r => modifiedFlow mn.1.1.1 mn.1.1.2 := by
            funext mn
            rcases mn with ⟨⟨⟨m, n⟩, hmn⟩, hnr⟩
            cases hnr
            rfl
          exact hEq ▸ hscol'
        have houter :
            Summable (fun r : Ω => ∑' mn : U r, modifiedFlow mn.1.1.1 mn.1.1.2) := by
          letI := hΩfin.fintype
          apply Summable.of_finite
        exact
          (summable_partition
            (f := fun mn : boundaryInPairs Ω => modifiedFlow mn.1.1 mn.1.2)
            (hf := fun mn => modifiedFlow_nonneg mn.1.1 mn.1.2)
            (s := U) hpart).2 ⟨hU_summable, houter⟩
    have hleft' := hleft.trans_eq hright
    have hboundary_nonneg : 0 ≤ boundaryInflow modifiedFlow Ω := by
      unfold boundaryInflow
      exact tsum_nonneg fun mn => modifiedFlow_nonneg mn.1.1 mn.1.2
    exact (ENNReal.ofReal_le_ofReal_iff hboundary_nonneg).mp hleft'
  have hmain :
      primitiveWeightSum A ≤ boundaryInflow modifiedFlow Ω +
        (∑' a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) := by
    letI := hfin.fintype
    have hIn_le' : ∑ a : A, inflow modifiedFlow (a : ℕ) ≤ boundaryInflow modifiedFlow Ω := by
      simpa [tsum_fintype] using hIn_le
    rw [hWeight, tsum_fintype, tsum_fintype]
    calc
      ∑ a : A, outflow modifiedFlow (a : ℕ)
          = ∑ a : A, inflow modifiedFlow (a : ℕ) +
              ∑ a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ)) := by
                calc
                  ∑ a : A, outflow modifiedFlow (a : ℕ)
                      = ∑ a : A,
                          (inflow modifiedFlow (a : ℕ) +
                            (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) := by
                              apply Finset.sum_congr rfl
                              intro a ha
                              ring
                  _ = _ := by rw [Finset.sum_add_distrib]
      _ ≤ boundaryInflow modifiedFlow Ω +
            ∑ a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ)) := by
              gcongr
  calc
    primitiveWeightSum A
        ≤ boundaryInflow modifiedFlow Ω +
            (∑' a : A, (outflow modifiedFlow (a : ℕ) - inflow modifiedFlow (a : ℕ))) := hmain
    _ ≤ boundaryOutflow modifiedFlow Ω := hBoundary
    _ ≤ primeWeightSum := hOut

lemma primitiveWeightSum_le_primeWeightSum_of_finite_subsets {A : Set ℕ}
    (hfinite :
      ∀ A₀ : Set ℕ, A₀ ⊆ A → A₀.Finite → primitiveWeightSum A₀ ≤ primeWeightSum) :
    primitiveWeightSum A ≤ primeWeightSum := by
  classical
  have htsum : ∑' a : A, erdosWeight (a : ℕ) ≤ primeWeightSum := by
    refine Real.tsum_le_of_sum_le ?_ ?_
    · intro a
      by_cases ha : 1 < (a : ℕ)
      · have hlog : 0 < Real.log (a : ℕ) := Real.log_pos (Nat.one_lt_cast.2 ha)
        have hden : 0 < ((a : ℕ) : ℝ) * Real.log (a : ℕ) := by
          refine mul_pos ?_ hlog
          exact Nat.cast_pos.mpr (lt_trans Nat.zero_lt_one ha)
        simpa [erdosWeight] using one_div_nonneg.mpr hden.le
      · have ha' : (a : ℕ) = 0 ∨ (a : ℕ) = 1 := by omega
        rcases ha' with h0 | h1
        · simp [erdosWeight, h0]
        · simp [erdosWeight, h1]
    · intro u
      let s : Finset ℕ := u.image (fun a : A => (a : ℕ))
      have hs_subset : (↑s : Set ℕ) ⊆ A := by
        intro n hn
        rcases Finset.mem_image.mp hn with ⟨a, ha, rfl⟩
        exact a.2
      have hs_eq :
          primitiveWeightSum (↑s : Set ℕ) = ∑ n ∈ s, erdosWeight n := by
        simpa [primitiveWeightSum, s] using (Finset.tsum_subtype' s erdosWeight)
      have hu_eq : ∑ n ∈ s, erdosWeight n = ∑ a ∈ u, erdosWeight (a : ℕ) := by
        dsimp [s]
        exact
          Finset.sum_image
            (s := u)
            (g := fun a : A => (a : ℕ))
            (f := erdosWeight)
            Subtype.val_injective.injOn
      calc
        ∑ a ∈ u, erdosWeight (a : ℕ) = primitiveWeightSum (↑s : Set ℕ) := by
          rw [← hu_eq, ← hs_eq]
        _ ≤ primeWeightSum := hfinite (↑s : Set ℕ) hs_subset s.finite_toSet
  simpa [primitiveWeightSum] using htsum

theorem primitiveWeightSum_le_primeWeightSum {A : Set ℕ} (hA : PrimitiveSet A) :
    primitiveWeightSum A ≤ primeWeightSum := by
  refine primitiveWeightSum_le_primeWeightSum_of_finite_subsets ?_
  intro A₀ hA₀ hA₀fin
  have hA₀_primitive : PrimitiveSet A₀ := by
    refine ⟨?_, ?_⟩
    · intro a ha
      exact hA.1 (hA₀ ha)
    · intro a b ha hb hab
      exact hA.2 (hA₀ ha) (hA₀ hb) hab
  exact primitiveWeightSum_le_primeWeightSum_of_finite hA₀_primitive hA₀fin

theorem erdos164 :
    PrimitiveSet primeSet ∧
      primitiveWeightSum primeSet = primeWeightSum ∧
      ∀ A : Set ℕ, PrimitiveSet A → primitiveWeightSum A ≤ primitiveWeightSum primeSet := by
  refine ⟨?_, ?_, ?_⟩
  · constructor
    · intro a ha
      have hPrime : a.Prime := by
        simpa [primeSet] using ha
      exact hPrime.two_le
    · intro a b ha hb hab
      have haPrime : a.Prime := by
        simpa [primeSet] using ha
      have hbPrime : b.Prime := by
        simpa [primeSet] using hb
      have ha_ne_one : a ≠ 1 := by
        exact ne_of_gt <| lt_of_lt_of_le (by decide : 1 < 2) haPrime.two_le
      have hEq : b = a := (hbPrime.dvd_iff_eq ha_ne_one).mp hab
      simpa using hEq.symm
  · rfl
  · intro A hA
    simpa [primitiveWeightSum, primeWeightSum, primeSet] using
      primitiveWeightSum_le_primeWeightSum hA

#print axioms erdos164
-- 'Erdos164.erdos164' depends on axioms: [propext, Classical.choice, Quot.sound]

end Erdos164
