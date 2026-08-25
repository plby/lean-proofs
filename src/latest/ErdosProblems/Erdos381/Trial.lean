import ErdosProblems.Erdos381.Core

namespace Erdos381

open Filter Asymptotics
open scoped Topology BigOperators

theorem criticalParameter_succ_lt {p k : ℕ} (hp : p.Prime) (hk : 0 < k) :
    criticalParameter p (k + 1) < criticalParameter p k := by
  rw [criticalParameter, criticalParameter]
  apply (div_lt_div_iff_of_pos_right
    (Real.log_pos (by exact_mod_cast hp.one_lt))).2
  exact log_one_add_inv_nat_strictAnti hk (Nat.lt_succ_self k)

theorem criticalParameter_one_strictAnti_prime {p q : ℕ}
    (hp : p.Prime) (hpq : p < q) :
    criticalParameter q 1 < criticalParameter p 1 := by
  rw [criticalParameter, criticalParameter]
  norm_num only [Nat.cast_one, div_one, one_add_one_eq_two]
  apply div_lt_div_of_pos_left (Real.log_pos (by norm_num))
  · exact Real.log_pos (by exact_mod_cast hp.one_lt)
  · exact Real.strictMonoOn_log
      (Set.mem_Ioi.mpr (by exact_mod_cast hp.pos))
      (Set.mem_Ioi.mpr (by exact_mod_cast (hp.pos.trans hpq)))
      (by exact_mod_cast hpq)

/-- The first pending prime-exponent transition produces a new superior
integer no larger than multiplication by any prime above the first
threshold. -/
theorem exists_superior_mul_prime_above_threshold
    {ε : ℝ} {N P : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hP : P.Prime) (hxP : thresholdScale ε 1 < P) :
    ∃ p : ℕ, p.Prime ∧ p ≤ P ∧ SuperiorNumber (N * p) ∧
      nextSuperior N ≤ N * p := by
  have hPmem : P ∈ Nat.primesLE P := Nat.mem_primesLE.mpr ⟨le_rfl, hP⟩
  obtain ⟨p, hpMem, hpMax⟩ := Finset.exists_max_image
    (Nat.primesLE P)
    (fun q ↦ criticalParameter q (N.factorization q + 1))
    ⟨P, hPmem⟩
  have hp : p.Prime := Nat.prime_of_mem_primesLE hpMem
  have hpP : p ≤ P := Nat.le_of_mem_primesLE hpMem
  let a : ℕ := N.factorization p
  let η : ℝ := criticalParameter p (a + 1)
  have hη : 0 < η := criticalParameter_pos hp (by omega)
  have hηε : η ≤ ε := by
    have hraise := (hN.primeExponentOptimal hp).raise_threshold
    have hlogp : 0 < Real.log (p : ℝ) :=
      Real.log_pos (by exact_mod_cast hp.one_lt)
    rw [← criticalParameter_mul_log hp] at hraise
    dsimp [η, a]
    nlinarith
  have hPexp : N.factorization P = 0 := by
    rcases hN.factorization_eq_canonical_or_tiedLower hε hP with hcanonical | htied
    · rw [hcanonical]
      have hnot : ¬0 < canonicalExponent ε P := by
        rw [canonicalExponent_pos_iff_le_thresholdScale_one hε hP]
        exact not_le_of_gt hxP
      omega
    · have hnot : ¬0 < canonicalExponent ε P := by
        rw [canonicalExponent_pos_iff_le_thresholdScale_one hε hP]
        exact not_le_of_gt hxP
      omega
  have hPtransition : criticalParameter P 1 ≤ η := by
    have hmax := hpMax P hPmem
    simpa [η, hPexp] using hmax
  have hNoptimalη : ∀ q : ℕ, q.Prime →
      PrimeExponentOptimal η q (N.factorization q) := by
    intro q hq
    let b : ℕ := N.factorization q
    have hnext : criticalParameter q (b + 1) ≤ η := by
      by_cases hqP : q ≤ P
      · have hqMem : q ∈ Nat.primesLE P :=
          Nat.mem_primesLE.mpr ⟨hqP, hq⟩
        simpa [η, a, b] using hpMax q hqMem
      · have hPq : P < q := Nat.lt_of_not_ge hqP
        have hb : b = 0 := by
          rcases hN.factorization_eq_canonical_or_tiedLower hε hq with
            hcanonical | htied
          · dsimp [b]
            rw [hcanonical]
            have hnot : ¬0 < canonicalExponent ε q := by
              rw [canonicalExponent_pos_iff_le_thresholdScale_one hε hq]
              exact not_le_of_gt (hxP.trans (by exact_mod_cast hPq))
            omega
          · have hnot : ¬0 < canonicalExponent ε q := by
              rw [canonicalExponent_pos_iff_le_thresholdScale_one hε hq]
              exact not_le_of_gt (hxP.trans (by exact_mod_cast hPq))
            omega
        rw [hb]
        exact (criticalParameter_one_strictAnti_prime hP hPq).le.trans
          hPtransition
    have hbCanonicalε : b ≤ canonicalExponent ε q := by
      rcases hN.factorization_eq_canonical_or_tiedLower hε hq with
        hcanonical | htied
      · simpa [b] using hcanonical.le
      · dsimp [b]
        omega
    have hbCanonicalη : b ≤ canonicalExponent η q :=
      hbCanonicalε.trans (canonicalExponent_antitone hη hηε hq)
    have hCanonicalη : canonicalExponent η q ≤ b + 1 := by
      by_contra hnot
      have htwo : b + 2 ≤ canonicalExponent η q := by omega
      have hparameter : η ≤ criticalParameter q (b + 2) :=
        (le_canonicalExponent_iff_le_criticalParameter hη hq (by omega)).1 htwo
      have hstrict := criticalParameter_succ_lt hq (by omega : 0 < b + 1)
      exact (not_lt_of_ge hparameter) (hstrict.trans_le hnext)
    have hcases : canonicalExponent η q = b ∨
        canonicalExponent η q = b + 1 := by omega
    rcases hcases with hcanon | hcanon
    · exact (primeExponentOptimal_iff_canonical_or_tiedLower hη hq).2
        (Or.inl hcanon.symm)
    · have hηcrit : η = criticalParameter q (b + 1) := by
        apply le_antisymm
        · apply (le_canonicalExponent_iff_le_criticalParameter hη hq (by omega)).1
          rw [hcanon]
        · exact hnext
      apply (primeExponentOptimal_iff_canonical_or_tiedLower hη hq).2
      right
      refine ⟨hcanon.symm, ?_⟩
      rw [hηcrit, criticalParameter_mul_log hq]
      rw [canonicalExponent_criticalParameter hq (by omega : 0 < b + 1)]
  let f : ℕ →₀ ℕ := N.factorization.update p (a + 1)
  have hfPrime : ∀ q ∈ f.support, q.Prime := by
    intro q hq
    have hmem : q ∈ insert p N.factorization.support :=
      Finsupp.support_update_subset
        (f := N.factorization) (a := p) (b := a + 1) hq
    rcases Finset.mem_insert.mp hmem with rfl | hqN
    · exact hp
    · exact Nat.prime_of_mem_primeFactors (by
        rwa [← Nat.support_factorization N])
  have hfOptimal : ∀ q : ℕ, q.Prime → PrimeExponentOptimal η q (f q) := by
    intro q hq
    by_cases hqp : q = p
    · subst q
      have hcanon : canonicalExponent η p = a + 1 := by
        simpa [η] using canonicalExponent_criticalParameter hp (by omega : 0 < a + 1)
      simpa [f, hcanon] using canonicalExponent_primewiseOptimal hη hp
    · simpa [f, hqp] using hNoptimalη q hq
  have hSuperiorF : Superior η (fromFactorization f) :=
    superior_from_primewise_optimal hfPrime hfOptimal
  have hfAdd : f = N.factorization + Finsupp.single p 1 := by
    ext q
    by_cases hqp : q = p
    · subst q
      simp [f, a]
    · simp [f, hqp]
  have hfrom : fromFactorization f = N * p := by
    rw [hfAdd, fromFactorization_add,
      fromFactorization_factorization hN.1.ne', fromFactorization_single,
      pow_one]
  have hNpSuperior : SuperiorNumber (N * p) := by
    refine ⟨η, hη, ?_⟩
    rwa [← hfrom]
  have hNNp : N < N * p := lt_mul_of_one_lt_right hN.1 hp.one_lt
  exact ⟨p, hp, hpP, hNpSuperior, nextSuperior_le hNNp hNpSuperior⟩

/-- The first pending prime-exponent transition produces a new superior
integer no larger than multiplication by any prime above the first
threshold. -/
theorem nextSuperior_le_mul_prime_above_threshold
    {ε : ℝ} {N P : ℕ} (hε : 0 < ε) (hN : Superior ε N)
    (hP : P.Prime) (hxP : thresholdScale ε 1 < P) :
    nextSuperior N ≤ N * P := by
  obtain ⟨p, hp, hpP, hsuperior, hnext⟩ :=
    exists_superior_mul_prime_above_threshold hε hN hP hxP
  exact hnext.trans (Nat.mul_le_mul_left N hpP)

end Erdos381
