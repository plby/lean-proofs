import ErdosProblems.Erdos285.PrimePowers

/-!
# LCM increments and the small-prime-power telescope

For a prime power `q = p ^ e`, the least common multiple of `1, ..., q`
acquires exactly one new factor `p` at `q`.  At every other positive integer
the least common multiple is unchanged.  These two facts turn the cost of
Martin's small-prime-power eliminations into an exact telescoping sum.
-/

namespace Erdos285.LcmTelescope

open Finset
open scoped BigOperators

noncomputable section

open PrimePowers

private lemma prime_log_pow_sub_one {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    p.log (p ^ e - 1) = e - 1 := by
  apply Nat.log_eq_of_pow_le_of_lt_pow
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 < e := Nat.sub_lt hepos (by omega)
    have hpows : p ^ (e - 1) < p ^ e := Nat.pow_lt_pow_right hp.one_lt hexp
    omega
  · have hepos : 0 < e := Nat.pos_of_ne_zero he
    have hexp : e - 1 + 1 = e := by omega
    rw [hexp]
    exact Nat.sub_lt (pow_pos hp.pos e) (by omega)

private lemma prime_log_pow_eq_log_pred_of_ne {p e r : ℕ}
    (hp : p.Prime) (he : e ≠ 0) (hr : r.Prime) (hrp : r ≠ p) :
    r.log (p ^ e) = r.log (p ^ e - 1) := by
  have hq2 : 2 ≤ p ^ e := by
    exact IsPrimePow.two_le (hp.isPrimePow.pow he)
  have hpred : p ^ e - 1 ≠ 0 := by omega
  have hsucc : p ^ e - 1 + 1 = p ^ e := by omega
  symm
  rw [← hsucc]
  apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
  intro hpow
  rw [hsucc] at hpow
  have hlog : r.log (p ^ e) ≠ 0 := by
    intro hz
    simp [hz] at hpow
    omega
  have hrdiv : r ∣ p ^ e := by
    rw [← hpow]
    exact dvd_pow_self r hlog
  exact hrp (Nat.prime_eq_prime_of_dvd_pow hr hp hrdiv)

/-- At a prime power `p ^ e`, the initial LCM acquires exactly one new factor
`p`. -/
theorem initialLcm_prime_pow {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    initialLcm (p ^ e) = p * initialLcm (p ^ e - 1) := by
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · exact mul_ne_zero hp.ne_zero (by simp [initialLcm])
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm (p ^ e) = Nat.lcmUpto (p ^ e) by rfl]
      rw [show initialLcm (p ^ e - 1) = Nat.lcmUpto (p ^ e - 1) by rfl]
      rw [Nat.factorization_lcmUpto (p ^ e) hr,
        Nat.factorization_mul hp.ne_zero (Nat.lcmUpto_ne_zero (p ^ e - 1))]
      simp only [Finsupp.add_apply]
      rw [Nat.factorization_lcmUpto (p ^ e - 1) hr]
      by_cases hrp : r = p
      · subst r
        rw [Nat.log_pow hp.one_lt, prime_log_pow_sub_one hp he]
        simp [hp]
        omega
      · rw [prime_log_pow_eq_log_pred_of_ne hp he hr hrp]
        simp [hp.factorization, hrp]
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- Away from prime powers, adjoining the right endpoint does not change the
initial LCM. -/
theorem initialLcm_eq_pred_of_not_isPrimePow {q : ℕ} (hq : ¬ IsPrimePow q) :
    initialLcm q = initialLcm (q - 1) := by
  by_cases hq0 : q = 0
  · subst q
    simp [initialLcm]
  by_cases hq1 : q = 1
  · subst q
    simp [initialLcm]
  have hq2 : 2 ≤ q := by omega
  have hpred : q - 1 ≠ 0 := by omega
  have hsucc : q - 1 + 1 = q := by omega
  apply Nat.eq_of_factorization_eq
  · simp [initialLcm]
  · simp [initialLcm]
  · intro r
    by_cases hr : r.Prime
    · rw [show initialLcm q = Nat.lcmUpto q by rfl]
      rw [show initialLcm (q - 1) = Nat.lcmUpto (q - 1) by rfl]
      rw [Nat.factorization_lcmUpto q hr,
        Nat.factorization_lcmUpto (q - 1) hr]
      symm
      rw [← hsucc]
      apply (Nat.log_eq_log_succ_iff hr.one_lt hpred).2
      intro hpow
      rw [hsucc] at hpow
      have hlog : r.log q ≠ 0 := by
        intro hz
        simp [hz] at hpow
        omega
      apply hq
      rw [← hpow]
      exact hr.isPrimePow.pow hlog
    · simp [Nat.factorization_eq_zero_of_not_prime, hr]

/-- The LCM increment at `p ^ e` is equivalently a difference of two unit
fractions. -/
theorem prime_pow_cost_identity {p e : ℕ} (hp : p.Prime) (he : e ≠ 0) :
    (((p - 1 : ℕ) : ℚ) / initialLcm (p ^ e)) =
      (1 : ℚ) / initialLcm (p ^ e - 1) -
        (1 : ℚ) / initialLcm (p ^ e) := by
  rw [initialLcm_prime_pow hp he]
  have hp0 : (p : ℚ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have hL0 : (initialLcm (p ^ e - 1) : ℚ) ≠ 0 := by
    exact_mod_cast (show initialLcm (p ^ e - 1) ≠ 0 by simp [initialLcm])
  push_cast [Nat.cast_sub hp.one_le]
  field_simp

/-- The cost attached to a prime power.  It will only be summed at arguments
which satisfy `IsPrimePow`. -/
def primePowerCost (q : ℕ) : ℚ :=
  ((q.minFac - 1 : ℕ) : ℚ) / initialLcm q

/-- The accumulated cost of the prime powers at most `lo`. -/
def smallPrimePowerCost (lo : ℕ) : ℚ :=
  (primePowersUpTo lo).sum primePowerCost

lemma primePowerCost_eq_sub {q : ℕ} (hq : IsPrimePow q) :
    primePowerCost q =
      (1 : ℚ) / initialLcm (q - 1) - (1 : ℚ) / initialLcm q := by
  obtain ⟨p, e, hp, he, rfl⟩ := (isPrimePow_nat_iff _).mp hq
  simpa [primePowerCost, hp.pow_minFac he.ne'] using
    prime_pow_cost_identity hp he.ne'

private lemma primePowersUpTo_eq_insert_pred {q : ℕ} (hq : IsPrimePow q) :
    primePowersUpTo q = insert q (primePowersUpTo (q - 1)) := by
  have hqnot : q ∉ primePowersUpTo (q - 1) := by
    intro hmem
    have hle := (mem_primePowersUpTo.mp hmem).2
    have hqpos := hq.pos
    omega
  ext t
  simp only [mem_primePowersUpTo, Finset.mem_insert]
  constructor
  · rintro ⟨htpp, htq⟩
    by_cases ht : t = q
    · exact Or.inl ht
    · exact Or.inr ⟨htpp, by omega⟩
  · rintro (rfl | ⟨htpp, htq⟩)
    · exact ⟨hq, le_rfl⟩
    · exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

private lemma primePowersUpTo_eq_pred {q : ℕ} (hq : ¬ IsPrimePow q) :
    primePowersUpTo q = primePowersUpTo (q - 1) := by
  ext t
  simp only [mem_primePowersUpTo]
  constructor
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, by
      by_cases ht : t = q
      · exact False.elim (hq (ht ▸ htpp))
      · omega⟩
  · rintro ⟨htpp, htq⟩
    exact ⟨htpp, htq.trans (Nat.sub_le q 1)⟩

/-- Exact telescope for all small-prime-power costs. -/
theorem smallPrimePowerCost_eq (lo : ℕ) :
    smallPrimePowerCost lo =
      1 - (1 : ℚ) / initialLcm lo := by
  induction lo with
  | zero => simp [smallPrimePowerCost, primePowersUpTo, initialLcm]
  | succ n ih =>
      by_cases hq : IsPrimePow (n + 1)
      · have hnot : n + 1 ∉ primePowersUpTo n := by
          rw [mem_primePowersUpTo]
          omega
        have hset : primePowersUpTo (n + 1) =
            insert (n + 1) (primePowersUpTo n) := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_insert_pred hq
        rw [smallPrimePowerCost, hset, Finset.sum_insert hnot]
        rw [← smallPrimePowerCost, ih, primePowerCost_eq_sub hq]
        simp only [Nat.add_sub_cancel]
        ring
      · have hset : primePowersUpTo (n + 1) = primePowersUpTo n := by
          simpa only [Nat.add_sub_cancel] using primePowersUpTo_eq_pred hq
        rw [smallPrimePowerCost, hset]
        rw [← smallPrimePowerCost, ih,
          initialLcm_eq_pred_of_not_isPrimePow hq]
        simp only [Nat.add_sub_cancel]

/-- The one-step form of the telescope, arranged for direct use in a strong
induction which descends from a prime power `q` to a value below `q`. -/
theorem primePowerCost_add_smallPrimePowerCost_pred {q : ℕ}
    (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost (q - 1) =
      smallPrimePowerCost q := by
  rw [primePowerCost_eq_sub hq, smallPrimePowerCost_eq,
    smallPrimePowerCost_eq]
  ring

lemma primePowerCost_nonneg (q : ℕ) : 0 ≤ primePowerCost q := by
  rw [primePowerCost]
  exact div_nonneg (by positivity) (by positivity)

theorem smallPrimePowerCost_mono : Monotone smallPrimePowerCost := by
  intro x y hxy
  rw [smallPrimePowerCost, smallPrimePowerCost]
  exact Finset.sum_le_sum_of_subset_of_nonneg (primePowersUpTo_mono hxy)
    (fun q _ _ ↦ primePowerCost_nonneg q)

/-- Budget inequality for a strict descent `q' < q`. -/
theorem primePowerCost_add_smallPrimePowerCost_of_lt {q' q : ℕ}
    (hq' : q' < q) (hq : IsPrimePow q) :
    primePowerCost q + smallPrimePowerCost q' ≤
      smallPrimePowerCost q := by
  calc
    primePowerCost q + smallPrimePowerCost q' ≤
        primePowerCost q + smallPrimePowerCost (q - 1) := by
      have hmono : smallPrimePowerCost q' ≤ smallPrimePowerCost (q - 1) :=
        smallPrimePowerCost_mono (show q' ≤ q - 1 by omega)
      linarith
    _ = smallPrimePowerCost q :=
      primePowerCost_add_smallPrimePowerCost_pred hq

/-- The total small-prime-power cost is strictly less than one. -/
theorem smallPrimePowerCost_lt_one (lo : ℕ) :
    smallPrimePowerCost lo < 1 := by
  rw [smallPrimePowerCost_eq]
  have hLpos : (0 : ℚ) < initialLcm lo := by
    exact_mod_cast (Nat.pos_of_ne_zero (by simp [initialLcm] : initialLcm lo ≠ 0))
  have hinvpos : (0 : ℚ) < 1 / initialLcm lo := div_pos zero_lt_one hLpos
  linarith

/-- Any collection of distinct prime powers below the cutoff has total cost
strictly below one.  This is the subset form useful when a descent visits only
some of the available prime powers. -/
theorem sum_primePowerCost_lt_one {A : Finset ℕ} {lo : ℕ}
    (hA : A ⊆ primePowersUpTo lo) :
    A.sum primePowerCost < 1 := by
  have hle : A.sum primePowerCost ≤ smallPrimePowerCost lo := by
    rw [smallPrimePowerCost]
    exact Finset.sum_le_sum_of_subset_of_nonneg hA
      (fun q _ _ ↦ primePowerCost_nonneg q)
  exact hle.trans_lt (smallPrimePowerCost_lt_one lo)

end

end Erdos285.LcmTelescope
