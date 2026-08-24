/- leanprover/lean4:v4.33.0  mathlib v4.33.0 -/
/-
This is a Lean formalization of a solution to Erdős Problem 405.
https://www.erdosproblems.com/forum/thread/405

Informal authors:
- Béla Brindza
- Paul Erdős
- Kunrui Yu
- Dehua Liu
- Maohua Le

Formal authors:
- Codex
- GPT-5.6 Sol

URLs:
- https://github.com/plby/lean-proofs/blob/main/ErdosProblems/Erdos405.md
-/
/-
This is a Lean formalization of the resolution of Erdős Problem 405.
https://www.erdosproblems.com/405

Informal authors:
- Béla Brindza
- Paul Erdős
- Kunrui Yu
- Dehua Liu
- Maohua Le

Formal authors:
- Codex

The main theorem `erdos_405` classifies all positive-integer solutions of

  (p - 1)! + a^(p - 1) = p^k

with `p` an odd prime.
-/

import Mathlib

namespace Erdos405

/-- A positive-integer solution of the equation in Erdős Problem 405. -/
def IsSolution (p a k : ℕ) : Prop :=
  p.Prime ∧ p ≠ 2 ∧ 0 < a ∧ 0 < k ∧
    (p - 1).factorial + a ^ (p - 1) = p ^ k

/-- The three triples found by Yu--Liu and Le. -/
def exceptionalSolutions : Finset (ℕ × ℕ × ℕ) :=
  {(3, 1, 1), (3, 5, 3), (5, 1, 2)}

@[simp] theorem isSolution_three_one_one : IsSolution 3 1 1 := by
  norm_num [IsSolution, Nat.factorial]

@[simp] theorem isSolution_three_five_three : IsSolution 3 5 3 := by
  norm_num [IsSolution, Nat.factorial]

@[simp] theorem isSolution_five_one_two : IsSolution 5 1 2 := by
  norm_num [IsSolution, Nat.factorial]

theorem isSolution_of_mem_exceptionalSolutions {p a k : ℕ}
    (h : (p, a, k) ∈ exceptionalSolutions) : IsSolution p a k := by
  simp only [exceptionalSolutions, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h | h <;> simp_all

/-- The right-to-left direction of the final classification. -/
theorem isSolution_of_eq_exceptional {p a k : ℕ}
    (h : (p = 3 ∧ a = 1 ∧ k = 1) ∨
      (p = 3 ∧ a = 5 ∧ k = 3) ∨
      (p = 5 ∧ a = 1 ∧ k = 2)) :
    IsSolution p a k := by
  rcases h with h | h | h <;> rcases h with ⟨rfl, rfl, rfl⟩ <;> simp

section ElementaryReductions

variable {p a k : ℕ}

theorem IsSolution.prime (h : IsSolution p a k) : p.Prime := h.1

theorem IsSolution.ne_two (h : IsSolution p a k) : p ≠ 2 := h.2.1

theorem IsSolution.a_pos (h : IsSolution p a k) : 0 < a := h.2.2.1

theorem IsSolution.k_pos (h : IsSolution p a k) : 0 < k := h.2.2.2.1

theorem IsSolution.equation (h : IsSolution p a k) :
    (p - 1).factorial + a ^ (p - 1) = p ^ k := h.2.2.2.2

theorem IsSolution.p_odd (h : IsSolution p a k) : Odd p :=
  h.prime.odd_of_ne_two h.ne_two

theorem IsSolution.three_le_p (h : IsSolution p a k) : 3 ≤ p := by
  exact Nat.succ_le_iff.mpr (lt_of_le_of_ne h.prime.two_le (Ne.symm h.ne_two))

/-- Wilson's theorem forces the base to be coprime to `p`. -/
theorem IsSolution.coprime (h : IsSolution p a k) : p.Coprime a := by
  rw [h.prime.coprime_iff_not_dvd]
  intro hpa
  let _ : Fact p.Prime := ⟨h.prime⟩
  have ha0 : (a : ZMod p) = 0 := by
    exact (ZMod.natCast_eq_zero_iff a p).mpr hpa
  have heq := congrArg (fun n : ℕ ↦ (n : ZMod p)) h.equation
  simp only [Nat.cast_add, Nat.cast_pow] at heq
  have hp3 := h.three_le_p
  have hp_sub_one_ne : p - 1 ≠ 0 := by omega
  have hneg : (-1 : ZMod p) = 0 := by
    simpa [ZMod.wilsons_lemma, ha0, hp_sub_one_ne, h.k_pos.ne'] using heq
  exact one_ne_zero (neg_eq_zero.mp hneg)

/-- Every prime factor of a nontrivial base is larger than `p`. -/
theorem IsSolution.lt_primeFactor_of_dvd_a (h : IsSolution p a k)
    {q : ℕ} (hq : q.Prime) (hqa : q ∣ a) : p < q := by
  by_contra hnlt
  have hqp : q ≤ p := Nat.le_of_not_gt hnlt
  have hq_ne_p : q ≠ p := by
    intro hEq
    subst q
    exact (h.prime.coprime_iff_not_dvd.mp h.coprime) hqa
  have hq_lt_p : q < p := lt_of_le_of_ne hqp hq_ne_p
  have hq_fac : q ∣ (p - 1).factorial := by
    apply Nat.dvd_factorial hq.pos
    omega
  have hp3 := h.three_le_p
  have hp_sub_one_ne : p - 1 ≠ 0 := by omega
  have hq_pow_a : q ∣ a ^ (p - 1) := dvd_pow hqa hp_sub_one_ne
  have hq_rhs : q ∣ p ^ k := by
    rw [← h.equation]
    exact dvd_add hq_fac hq_pow_a
  have hq_dvd_p : q ∣ p := hq.dvd_of_dvd_pow hq_rhs
  rcases (Nat.dvd_prime h.prime).mp hq_dvd_p with hq1 | hqp
  · exact hq.ne_one hq1
  · exact hq_ne_p hqp

theorem IsSolution.p_add_two_le_a (h : IsSolution p a k) (ha1 : a ≠ 1) :
    p + 2 ≤ a := by
  have ha_pos := h.a_pos
  have ha_gt_one : 1 < a := by omega
  let q := a.minFac
  have ha_ne_one : a ≠ 1 := ha1
  have hq_prime : q.Prime := Nat.minFac_prime (by omega)
  have hq_dvd : q ∣ a := Nat.minFac_dvd a
  have hpq := h.lt_primeFactor_of_dvd_a hq_prime hq_dvd
  have hq_le_a : q ≤ a := Nat.le_of_dvd h.a_pos hq_dvd
  have hp_odd := h.p_odd
  have hq_odd := hq_prime.odd_of_ne_two (by
    intro hq2
    subst q
    have hp3 := h.three_le_p
    omega)
  rcases hp_odd with ⟨hp_half, hp_half_eq⟩
  rcases hq_odd with ⟨hq_half, hq_half_eq⟩
  omega

/-- The defining equation reduced modulo `p - 1`. -/
theorem IsSolution.pow_modEq_one_pred (h : IsSolution p a k) :
    a ^ (p - 1) ≡ 1 [MOD p - 1] := by
  have hpred_pos : 0 < p - 1 := by have := h.prime.two_le; omega
  have hfac_dvd : p - 1 ∣ (p - 1).factorial :=
    Nat.dvd_factorial hpred_pos le_rfl
  have hfac_mod : (p - 1).factorial ≡ 0 [MOD p - 1] :=
    Nat.modEq_zero_iff_dvd.mpr hfac_dvd
  have hp_mod : p ≡ 1 [MOD p - 1] := by
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr (by simp)).symm
  calc
    a ^ (p - 1) ≡ 0 + a ^ (p - 1) [MOD p - 1] :=
      by
        simp only [Nat.ModEq, zero_add]
    _ ≡ (p - 1).factorial + a ^ (p - 1) [MOD p - 1] :=
      (hfac_mod.add_right _).symm
    _ = p ^ k := h.equation
    _ ≡ 1 ^ k [MOD p - 1] := hp_mod.pow k
    _ = 1 := one_pow k

/-- The valuation step in Le's reduction: every odd prime divisor of `p - 1`
also divides the exponent `k`. -/
theorem IsSolution.odd_prime_dvd_k_of_dvd_pred (h : IsSolution p a k)
    (ha1 : a ≠ 1) {q : ℕ} (hq : q.Prime) (hqodd : Odd q)
    (hqpred : q ∣ p - 1) : q ∣ k := by
  let _ : Fact q.Prime := ⟨hq⟩
  let e := padicValNat q (p - 1)
  have hpred_pos : 0 < p - 1 := by have := h.prime.two_le; omega
  have hq_le_pred : q ≤ p - 1 := Nat.le_of_dvd hpred_pos hqpred
  have hq_lt_p : q < p := by omega
  have hq_le_predpred : q ≤ p - 2 := by
    have hq_ne_pred : q ≠ p - 1 := by
      intro heq
      subst q
      exact hqodd.not_two_dvd_nat (by
        rcases h.p_odd with ⟨u, hu⟩
        refine ⟨u, ?_⟩
        omega)
    omega
  have hq_not_dvd_a : ¬ q ∣ a := by
    intro hqa
    have := h.lt_primeFactor_of_dvd_a hq hqa
    omega
  have he_pos : 0 < e := by
    exact one_le_padicValNat_of_dvd (by omega) hqpred
  have hqe_dvd_pred : q ^ e ∣ p - 1 := pow_padicValNat_dvd
  have hq_dvd_smallfac : q ∣ (p - 2).factorial :=
    Nat.dvd_factorial hq.pos hq_le_predpred
  have hfac_succ : (p - 1).factorial = (p - 1) * (p - 2).factorial := by
    simpa [show p - 2 + 1 = p - 1 by omega] using Nat.factorial_succ (p - 2)
  have hqe_succ_dvd_fac : q ^ (e + 1) ∣ (p - 1).factorial := by
    rw [hfac_succ, pow_succ]
    exact Nat.mul_dvd_mul hqe_dvd_pred hq_dvd_smallfac

  have haq_mod_pred := h.pow_modEq_one_pred
  have haq_mod : a ^ (p - 1) ≡ 1 [MOD q] :=
    haq_mod_pred.of_dvd hqpred
  have hqe_le_pred : q ^ e ≤ p - 1 := Nat.le_of_dvd hpred_pos hqe_dvd_pred
  let r := (p - 1) / q ^ e
  have hr_pos : 0 < r := Nat.div_pos hqe_le_pred (pow_pos hq.pos e)
  have hdecomp : q ^ e * r = p - 1 := Nat.mul_div_cancel' hqe_dvd_pred
  have hzfull : (a : ZMod q) ^ (p - 1) = 1 := by
    simpa using (ZMod.natCast_eq_natCast_iff (a ^ (p - 1)) 1 q).mpr haq_mod
  have hzbase : (a : ZMod q) ^ r = 1 := by
    rw [← hdecomp, mul_comm, pow_mul, ZMod.pow_card_pow] at hzfull
    exact hzfull
  have har_mod : a ^ r ≡ 1 [MOD q] := by
    rw [← ZMod.natCast_eq_natCast_iff]
    simpa using hzbase
  have hq_dvd_ar_sub : q ∣ a ^ r - 1 := har_mod.symm.dvd'
  have ha_lower := h.p_add_two_le_a ha1
  have har_gt_one : 1 < a ^ r := by
    exact one_lt_pow₀ (by omega) hr_pos.ne'
  have hq_not_dvd_ar : ¬ q ∣ a ^ r := fun hqar ↦
    hq_not_dvd_a (hq.dvd_of_dvd_pow hqar)
  have har_sub_ne : a ^ r - 1 ≠ 0 := by omega
  have hval_ar : 1 ≤ padicValNat q (a ^ r - 1) :=
    one_le_padicValNat_of_dvd har_sub_ne hq_dvd_ar_sub
  have hlte_a := padicValNat.pow_sub_pow (p := q) hqodd har_gt_one
    hq_dvd_ar_sub hq_not_dvd_ar (n := q ^ e) (pow_ne_zero e hq.ne_zero)
  have hlte_a' :
      padicValNat q ((a ^ r) ^ (q ^ e) - 1) =
        padicValNat q (a ^ r - 1) + padicValNat q (q ^ e) := by
    simpa only [one_pow] using hlte_a
  have hpow_rewrite : (a ^ r) ^ (q ^ e) = a ^ (p - 1) := by
    rw [← pow_mul, mul_comm, hdecomp]
  have hapow_sub_ne : a ^ (p - 1) - 1 ≠ 0 := by
    have hp_sub_ne : p - 1 ≠ 0 := by omega
    have := one_lt_pow₀ (by omega : 1 < a) hp_sub_ne
    omega
  have hval_apow : e + 1 ≤ padicValNat q (a ^ (p - 1) - 1) := by
    rw [← hpow_rewrite, hlte_a', padicValNat.prime_pow]
    omega
  have hqe_succ_dvd_apow : q ^ (e + 1) ∣ a ^ (p - 1) - 1 :=
    (padicValNat_dvd_iff_le hapow_sub_ne).mpr hval_apow

  have hpk_sub_eq : p ^ k - 1 =
      (p - 1).factorial + (a ^ (p - 1) - 1) := by
    have hapow_pos : 0 < a ^ (p - 1) := pow_pos h.a_pos _
    have heq := h.equation
    omega
  have hqe_succ_dvd_pk : q ^ (e + 1) ∣ p ^ k - 1 := by
    rw [hpk_sub_eq]
    exact dvd_add hqe_succ_dvd_fac hqe_succ_dvd_apow
  have hq_not_dvd_p : ¬ q ∣ p := by
    intro hqp
    rcases (Nat.dvd_prime h.prime).mp hqp with hq1 | hqp
    · exact hq.ne_one hq1
    · omega
  have hpk_sub_ne : p ^ k - 1 ≠ 0 := by
    have := one_lt_pow₀ h.prime.one_lt h.k_pos.ne'
    omega
  have hval_pk : e + 1 ≤ padicValNat q (p ^ k - 1) :=
    (padicValNat_dvd_iff_le hpk_sub_ne).mp hqe_succ_dvd_pk
  have hlte_p := padicValNat.pow_sub_pow (p := q) hqodd h.prime.one_lt
    hqpred hq_not_dvd_p h.k_pos.ne'
  have hlte_p' : padicValNat q (p ^ k - 1) =
      padicValNat q (p - 1) + padicValNat q k := by
    simpa only [one_pow] using hlte_p
  have hval_k : 1 ≤ padicValNat q k := by
    rw [hlte_p'] at hval_pk
    dsimp [e] at hval_pk
    omega
  have : q ^ 1 ∣ k := (padicValNat_dvd_iff_le h.k_pos.ne').mpr hval_k
  simpa using this

/-- An odd prime divisor of `p - 1` turns the original equation into the
forbidden Erdős--Obláth shape `X^q - Y^q = (p - 1)!`. -/
theorem IsSolution.exists_factorial_odd_prime_power_difference
    (h : IsSolution p a k) (ha1 : a ≠ 1) {q : ℕ}
    (hq : q.Prime) (hqodd : Odd q) (hqpred : q ∣ p - 1) :
    ∃ X Y : ℕ, 0 < X ∧ 0 < Y ∧ X.Coprime Y ∧
      X ^ q - Y ^ q = (p - 1).factorial := by
  have hqk : q ∣ k := h.odd_prime_dvd_k_of_dvd_pred ha1 hq hqodd hqpred
  refine ⟨p ^ (k / q), a ^ ((p - 1) / q), pow_pos h.prime.pos _, pow_pos h.a_pos _,
    Nat.Coprime.pow _ _ h.coprime, ?_⟩
  have hk_decomp : q * (k / q) = k := Nat.mul_div_cancel' hqk
  have hp_decomp : q * ((p - 1) / q) = p - 1 := Nat.mul_div_cancel' hqpred
  have hrewrite_p : (p ^ (k / q)) ^ q = p ^ k := by
    rw [← pow_mul, mul_comm, hk_decomp]
  have hrewrite_a : (a ^ ((p - 1) / q)) ^ q = a ^ (p - 1) := by
    rw [← pow_mul, mul_comm, hp_decomp]
  rw [hrewrite_p, hrewrite_a]
  have heq := h.equation
  omega

/-- If `p - 1` has no odd prime factor, it is a power of two. -/
theorem pred_eq_two_pow_of_no_odd_prime_dvd (h : IsSolution p a k)
    (hno : ∀ q : ℕ, q.Prime → Odd q → ¬ q ∣ p - 1) :
    ∃ t : ℕ, p - 1 = 2 ^ t := by
  rcases (p - 1).eq_two_pow_or_exists_odd_prime_and_dvd with hpow | hodd
  · exact hpow
  · rcases hodd with ⟨q, hq, hqpred, hqodd⟩
    exact (hno q hq hqodd hqpred).elim

/-- The elementary final step of the Fermat-prime reduction. -/
theorem IsSolution.eq_fermatNumber_of_no_odd_prime_dvd (h : IsSolution p a k)
    (hno : ∀ q : ℕ, q.Prime → Odd q → ¬ q ∣ p - 1) :
    ∃ m : ℕ, p = Nat.fermatNumber m := by
  obtain ⟨t, ht⟩ := pred_eq_two_pow_of_no_odd_prime_dvd h hno
  have hp_eq : p = 2 ^ t + 1 := by
    calc
      p = (p - 1) + 1 := (Nat.sub_add_cancel (by exact h.prime.one_le)).symm
      _ = 2 ^ t + 1 := by rw [ht]
  have ht_ne : t ≠ 0 := by
    intro ht0
    subst t
    norm_num at hp_eq
    exact h.ne_two hp_eq
  have hprime_form : (2 ^ t + 1).Prime := by simpa [← hp_eq] using h.prime
  obtain ⟨m, hm⟩ := Nat.pow_of_pow_add_prime (by norm_num : 1 < 2) ht_ne hprime_form
  refine ⟨m, ?_⟩
  rw [hp_eq, hm, Nat.fermatNumber]

/-- For odd `p ≥ 7`, the number `p - 1` already divides `(p - 2)!`. -/
private theorem pred_dvd_pred_pred_factorial (hp : 7 ≤ p) (hpodd : Odd p) :
    p - 1 ∣ (p - 2).factorial := by
  rcases hpodd with ⟨r, hr⟩
  have htwo : 2 ∣ p - 1 := by
    refine ⟨r, ?_⟩
    omega
  have hhalf_pos : 0 < (p - 1) / 2 := by omega
  have hhalf_le : (p - 1) / 2 ≤ p - 4 := by omega
  have hhalf_dvd : (p - 1) / 2 ∣ (p - 4).factorial :=
    Nat.dvd_factorial hhalf_pos hhalf_le
  have htwo_half : 2 * ((p - 1) / 2) = p - 1 :=
    Nat.mul_div_cancel' htwo
  have hsmall : p - 1 ∣ (Nat.factorial 2) * (p - 4).factorial := by
    rcases hhalf_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    norm_num [Nat.factorial]
    calc
      2 * (p - 4).factorial = 2 * (((p - 1) / 2) * c) := by rw [hc]
      _ = (p - 1) * c := by rw [← mul_assoc, htwo_half]
  have hlarge : (Nat.factorial 2) * (p - 4).factorial ∣ (p - 2).factorial := by
    simpa [show 2 + (p - 4) = p - 2 by omega] using
      Nat.factorial_mul_factorial_dvd_factorial_add 2 (p - 4)
  exact dvd_trans hsmall hlarge

/-- The geometric sum obtained after cancelling `p - 1` in the `a = 1` equation. -/
private theorem geom_sum_eq_pred_pred_factorial
    (h : IsSolution p 1 k) :
    ∑ i ∈ Finset.range k, p ^ i = (p - 2).factorial := by
  have hp2 : 2 ≤ p := h.prime.two_le
  have hfac_succ : (p - 1).factorial = (p - 1) * (p - 2).factorial := by
    simpa [show p - 2 + 1 = p - 1 by omega] using Nat.factorial_succ (p - 2)
  have heq_sub : (p - 1).factorial = p ^ k - 1 := by
    have heq := h.equation
    simp only [one_pow] at heq
    have hp_pow_pos : 0 < p ^ k := pow_pos h.prime.pos k
    omega
  have hgeom :
      (∑ i ∈ Finset.range k, p ^ i) * (p - 1) = p ^ k - 1 :=
    geom_sum_mul_of_one_le (by omega) k
  have hmul :
      (p - 1) * (p - 2).factorial =
        (p - 1) * (∑ i ∈ Finset.range k, p ^ i) := by
    rw [← hfac_succ, heq_sub, ← hgeom, mul_comm]
  exact (Nat.mul_left_cancel (by omega : 0 < p - 1) hmul).symm

/-- Liouville's special factorial-power theorem, proved here directly. -/
theorem IsSolution.eq_small_of_a_eq_one (h : IsSolution p a k) (ha : a = 1) :
    (p = 3 ∧ k = 1) ∨ (p = 5 ∧ k = 2) := by
  subst a
  by_cases hp3 : p = 3
  · left
    refine ⟨hp3, ?_⟩
    subst p
    apply Nat.pow_right_injective (by decide : 2 ≤ 3)
    norm_num [IsSolution, Nat.factorial] at h ⊢
    omega
  by_cases hp5 : p = 5
  · right
    refine ⟨hp5, ?_⟩
    subst p
    apply Nat.pow_right_injective (by decide : 2 ≤ 5)
    norm_num [IsSolution, Nat.factorial] at h ⊢
    omega
  have hp7 : 7 ≤ p := by
    have hp3le := h.three_le_p
    rcases h.p_odd with ⟨r, hr⟩
    omega
  have hsum_eq := geom_sum_eq_pred_pred_factorial h
  have hpred_dvd_sum : p - 1 ∣ ∑ i ∈ Finset.range k, p ^ i := by
    rw [hsum_eq]
    exact pred_dvd_pred_pred_factorial hp7 h.p_odd
  have hp_mod : p ≡ 1 [MOD p - 1] := by
    exact ((Nat.modEq_iff_dvd' (by omega : 1 ≤ p)).mpr (by simp)).symm
  have hsum_mod :
      (∑ i ∈ Finset.range k, p ^ i) ≡ k [MOD p - 1] := by
    have := Nat.ModEq.sum (s := Finset.range k)
      (fun i _hi ↦ hp_mod.pow i)
    simpa using this
  have hk_dvd : p - 1 ∣ k := by
    rw [← Nat.modEq_zero_iff_dvd]
    exact hsum_mod.symm.trans hpred_dvd_sum.modEq_zero_nat
  have hk_lower : p - 1 ≤ k := Nat.le_of_dvd h.k_pos hk_dvd
  have hfac_bound : (p - 1).factorial + 1 < p ^ (p - 1) := by
    have hfac_le : (p - 1).factorial ≤ (p - 1) ^ (p - 1) :=
      Nat.factorial_le_pow (p - 1)
    have hpow_le : (p - 1) ^ (p - 2) ≤ p ^ (p - 2) :=
      Nat.pow_le_pow_left (Nat.sub_le p 1) (p - 2)
    have hpow_gt_one : 1 < p ^ (p - 2) := by
      exact one_lt_pow₀ h.prime.one_lt (by omega)
    calc
      (p - 1).factorial + 1 ≤ (p - 1) ^ (p - 1) + 1 :=
        Nat.add_le_add_right hfac_le 1
      _ = (p - 1) * (p - 1) ^ (p - 2) + 1 := by
        rw [show p - 1 = (p - 2) + 1 by omega, pow_succ']
      _ ≤ (p - 1) * p ^ (p - 2) + 1 := by gcongr
      _ < p * p ^ (p - 2) := by
        calc
          (p - 1) * p ^ (p - 2) + 1 <
              (p - 1) * p ^ (p - 2) + p ^ (p - 2) :=
            Nat.add_lt_add_left hpow_gt_one _
          _ = p * p ^ (p - 2) := by
            calc
              (p - 1) * p ^ (p - 2) + p ^ (p - 2) =
                  ((p - 1) + 1) * p ^ (p - 2) := by rw [add_mul, one_mul]
              _ = p * p ^ (p - 2) := by
                congr 1
                omega
      _ = p ^ (p - 1) := by
        rw [show p - 1 = (p - 2) + 1 by omega, pow_succ']
  have hk_upper : k < p - 1 := by
    apply (Nat.pow_lt_pow_iff_right h.prime.one_lt).mp
    rw [← h.equation]
    simpa using hfac_bound
  omega

/-- The nontrivial `p = 5` branch is impossible.  Modulo `3` the exponent is
even; the resulting difference of squares has a factor larger than `24`. -/
theorem not_isSolution_five_of_ne_one {a k : ℕ}
    (h : IsSolution 5 a k) (ha1 : a ≠ 1) : False := by
  have h3_not_dvd_a : ¬ 3 ∣ a := by
    intro h3a
    have hlt := h.lt_primeFactor_of_dvd_a (by norm_num : Nat.Prime 3) h3a
    omega
  have ha0 : (a : ZMod 3) ≠ 0 := by
    intro hz
    exact h3_not_dvd_a ((ZMod.natCast_eq_zero_iff a 3).mp hz)
  have ha2 : (a : ZMod 3) ^ 2 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one ha0
  have ha4 : (a : ZMod 3) ^ 4 = 1 := by
    rw [show 4 = 2 * 2 by norm_num, pow_mul, ha2, one_pow]
  have heq := congrArg (fun n : ℕ ↦ (n : ZMod 3)) h.equation
  norm_num [Nat.factorial] at heq
  have h24z : (24 : ZMod 3) = 0 := by decide
  have h5z : (5 : ZMod 3) = -1 := by decide
  rw [h24z, zero_add, h5z] at heq
  have hneg : (-1 : ZMod 3) ^ k = 1 := by
    calc
      (-1 : ZMod 3) ^ k = (a : ZMod 3) ^ 4 := heq.symm
      _ = 1 := ha4
  have hk_even : Even k :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ZMod 3) ≠ 1)).mp hneg
  rcases hk_even with ⟨t, rfl⟩
  have heq_nat := h.equation
  norm_num [Nat.factorial, pow_add] at heq_nat
  have hsq : (a ^ 2) ^ 2 < (5 ^ t) ^ 2 := by
    nlinarith [heq_nat]
  have hlt : a ^ 2 < 5 ^ t :=
    (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
  have hsub : 5 ^ t - a ^ 2 + a ^ 2 = 5 ^ t :=
    Nat.sub_add_cancel hlt.le
  have hfactor : (5 ^ t - a ^ 2) * (5 ^ t + a ^ 2) = 24 := by
    nlinarith [heq_nat, hsub]
  have hbig_dvd : 5 ^ t + a ^ 2 ∣ 24 := by
    refine ⟨5 ^ t - a ^ 2, ?_⟩
    simpa [mul_comm] using hfactor.symm
  have hbig_le : 5 ^ t + a ^ 2 ≤ 24 := Nat.le_of_dvd (by norm_num) hbig_dvd
  have ha7 : 7 ≤ a := by
    have := h.p_add_two_le_a ha1
    norm_num at this ⊢
    exact this
  nlinarith [Nat.pow_le_pow_left ha7 2]

/-- Complete classification when the odd prime is `5`. -/
theorem IsSolution.eq_of_p_eq_five (h : IsSolution p a k) (hp : p = 5) :
    a = 1 ∧ k = 2 := by
  subst p
  by_cases ha1 : a = 1
  · refine ⟨ha1, ?_⟩
    rcases h.eq_small_of_a_eq_one ha1 with h3 | h5
    · omega
    · exact h5.2
  · exact (not_isSolution_five_of_ne_one h ha1).elim

/-- At `p = 3` the original equation is exactly the fixed-base Nagell
equation. -/
theorem IsSolution.equation_of_p_eq_three (h : IsSolution p a k) (hp : p = 3) :
    a ^ 2 + 2 = 3 ^ k := by
  subst p
  have heq := h.equation
  norm_num [Nat.factorial] at heq ⊢
  omega

/-- Every exponent in the `p = 3` branch is odd.  This elementary part of
Nagell's argument follows by factoring a hypothetical difference of squares. -/
theorem IsSolution.k_odd_of_p_eq_three (h : IsSolution p a k) (hp : p = 3) :
    Odd k := by
  subst p
  rcases Nat.even_or_odd k with hk_even | hk_odd
  · rcases hk_even with ⟨t, rfl⟩
    have heq := h.equation
    norm_num [Nat.factorial, pow_add] at heq
    have hsq : a ^ 2 < (3 ^ t) ^ 2 := by
      nlinarith [heq]
    have hlt : a < 3 ^ t :=
      (pow_lt_pow_iff_left₀ (by positivity) (by positivity) (by norm_num)).mp hsq
    have hsub : 3 ^ t - a + a = 3 ^ t := Nat.sub_add_cancel hlt.le
    have hfactor : (3 ^ t - a) * (3 ^ t + a) = 2 := by
      nlinarith [heq, hsub]
    have hbig_dvd : 3 ^ t + a ∣ 2 := by
      refine ⟨3 ^ t - a, ?_⟩
      simpa [mul_comm] using hfactor.symm
    have hbig_le : 3 ^ t + a ≤ 2 := Nat.le_of_dvd (by norm_num) hbig_dvd
    have ht_pos : 0 < t := by
      have := h.k_pos
      omega
    have hthree_le : 3 ≤ 3 ^ t := by
      simpa using (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mpr ht_pos
    omega
  · exact hk_odd

/-- In the `p = 17` branch, reduction modulo `5` forces the exponent to be a
multiple of four. -/
theorem IsSolution.four_dvd_k_of_p_eq_seventeen (h : IsSolution p a k)
    (hp : p = 17) : 4 ∣ k := by
  subst p
  let _ : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h5_not_dvd_a : ¬ 5 ∣ a := by
    intro h5a
    have hlt := h.lt_primeFactor_of_dvd_a (by norm_num : Nat.Prime 5) h5a
    omega
  have ha0 : (a : ZMod 5) ≠ 0 := by
    intro hz
    exact h5_not_dvd_a ((ZMod.natCast_eq_zero_iff a 5).mp hz)
  have ha4 : (a : ZMod 5) ^ 4 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one ha0
  have ha16 : (a : ZMod 5) ^ 16 = 1 := by
    rw [show 16 = 4 * 4 by norm_num, pow_mul, ha4, one_pow]
  have heq_nat : Nat.factorial 16 + a ^ 16 = 17 ^ k := by
    have heq' := h.equation
    norm_num only at heq'
    exact heq'
  have heq := congrArg (fun n : ℕ ↦ (n : ZMod 5)) heq_nat
  simp only [Nat.cast_add, Nat.cast_pow] at heq
  change ((Nat.factorial 16 : ℕ) : ZMod 5) + (a : ZMod 5) ^ 16 =
    (17 : ZMod 5) ^ k at heq
  have hfacz : ((Nat.factorial 16 : ℕ) : ZMod 5) = 0 := by
    exact (ZMod.natCast_eq_zero_iff (Nat.factorial 16) 5).mpr
      (Nat.dvd_factorial (by norm_num) (by norm_num))
  rw [hfacz, zero_add, ha16] at heq
  have hpow : (17 : ZMod 5) ^ k = 1 := heq.symm
  have hpow4 : (17 : ZMod 5) ^ 4 = 1 := by decide
  have hk_decomp : k = 4 * (k / 4) + k % 4 := by omega
  have hpow_rem : (17 : ZMod 5) ^ (k % 4) = 1 := by
    rw [hk_decomp, pow_add, pow_mul, hpow4, one_pow, one_mul] at hpow
    exact hpow
  have hrem_lt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hrem_zero : k % 4 = 0 := by
    interval_cases hrem : k % 4
    · rfl
    · exact ((by decide : (17 : ZMod 5) ^ 1 ≠ 1) hpow_rem).elim
    · exact ((by decide : (17 : ZMod 5) ^ 2 ≠ 1) hpow_rem).elim
    · exact ((by decide : (17 : ZMod 5) ^ 3 ≠ 1) hpow_rem).elim
  exact Nat.dvd_iff_mod_eq_zero.mpr hrem_zero

/-- The remaining small Fermat-prime case `p = 17` is elementary.  The
sum-of-two-squares factor of `16!` can contain only the primes `5` and `13`,
and therefore is far too small for a nontrivial base. -/
theorem not_isSolution_seventeen_of_ne_one {a k : ℕ}
    (h : IsSolution 17 a k) (ha1 : a ≠ 1) : False := by
  have hk4 : 4 ∣ k := h.four_dvd_k_of_p_eq_seventeen rfl
  obtain ⟨t, ht⟩ := hk4
  let u := 17 ^ t
  let v := a ^ 4
  let T := u ^ 2 + v ^ 2
  let N := T / 2
  have heq := h.equation
  change Nat.factorial 16 + a ^ 16 = 17 ^ k at heq
  rw [ht] at heq
  have heq_uv : Nat.factorial 16 + v ^ 4 = u ^ 4 := by
    dsimp [u, v]
    simpa [← pow_mul, mul_comm, mul_left_comm, mul_assoc] using heq
  have hu4 : u ^ 4 = (u ^ 2) ^ 2 := by ring
  have hv4 : v ^ 4 = (v ^ 2) ^ 2 := by ring
  have hv2_lt_u2 : v ^ 2 < u ^ 2 := by
    rw [hu4, hv4] at heq_uv
    have hfac_pos := Nat.factorial_pos 16
    nlinarith [heq_uv]
  have hsub : u ^ 2 - v ^ 2 + v ^ 2 = u ^ 2 :=
    Nat.sub_add_cancel hv2_lt_u2.le
  have hfactor : (u ^ 2 - v ^ 2) * T = Nat.factorial 16 := by
    dsimp [T]
    nlinarith [heq_uv, hsub]
  have hT_dvd_fac : T ∣ Nat.factorial 16 := by
    refine ⟨u ^ 2 - v ^ 2, ?_⟩
    simpa [mul_comm] using hfactor.symm

  have htwo_not_dvd_a : ¬ 2 ∣ a := by
    intro h2a
    have hlt := h.lt_primeFactor_of_dvd_a (by norm_num : Nat.Prime 2) h2a
    omega
  have haodd : Odd a := by
    rw [← Nat.not_even_iff_odd, even_iff_two_dvd]
    exact htwo_not_dvd_a
  have huodd : Odd u := by
    dsimp [u]
    exact (by norm_num : Odd 17).pow
  have hvodd : Odd v := by
    dsimp [v]
    exact haodd.pow
  have h2T : 2 ∣ T := by
    exact (huodd.pow.add_odd hvodd.pow).two_dvd
  have hT_eq : 2 * N = T := by
    exact Nat.mul_div_cancel' h2T
  have hu_mod8 : u ^ 2 ≡ 1 [MOD 8] := by
    exact ((Nat.modEq_iff_dvd' (by exact pow_pos huodd.pos 2)).mpr
      (Nat.eight_dvd_sq_sub_one_of_odd huodd)).symm
  have hv_mod8 : v ^ 2 ≡ 1 [MOD 8] := by
    exact ((Nat.modEq_iff_dvd' (by exact pow_pos hvodd.pos 2)).mpr
      (Nat.eight_dvd_sq_sub_one_of_odd hvodd)).symm
  have hT_mod8 : T ≡ 2 [MOD 8] := by
    simpa [T] using hu_mod8.add hv_mod8
  have h4_not_dvd_T : ¬ 4 ∣ T := by
    intro h4T
    have hT_mod4 : T ≡ 2 [MOD 4] :=
      hT_mod8.of_dvd (by norm_num : 4 ∣ 8)
    have hzero : T ≡ 0 [MOD 4] := h4T.modEq_zero_nat
    have hbad : 2 ≡ 0 [MOD 4] := hT_mod4.symm.trans hzero
    norm_num [Nat.ModEq] at hbad
  have hNodd : Odd N := by
    rw [← Nat.not_even_iff_odd]
    intro hNeven
    apply h4_not_dvd_T
    rcases hNeven.two_dvd with ⟨c, hc⟩
    refine ⟨c, ?_⟩
    omega
  have hN_dvd_T : N ∣ T := by
    refine ⟨2, ?_⟩
    omega
  have hN_dvd_fac : N ∣ Nat.factorial 16 := hN_dvd_T.trans hT_dvd_fac
  have hN_pos : 0 < N := by
    have hT_pos : 0 < T := by dsimp [T, u]; positivity
    exact Nat.pos_of_dvd_of_pos hN_dvd_T hT_pos

  have hprime_class : ∀ {q : ℕ}, q.Prime → q ∣ N → q = 5 ∨ q = 13 := by
    intro q hq hqN
    let _ : Fact q.Prime := ⟨hq⟩
    have hq_fac : q ∣ Nat.factorial 16 := hqN.trans hN_dvd_fac
    have hq_le : q ≤ 16 := (hq.dvd_factorial).mp hq_fac
    have hq_ne_two : q ≠ 2 := by
      intro hq2
      subst q
      exact hNodd.not_two_dvd_nat hqN
    have hqT : q ∣ T := hqN.trans hN_dvd_T
    have hq_not_dvd_v : ¬ q ∣ v := by
      intro hqv
      have hqa : q ∣ a := by
        dsimp [v] at hqv
        exact hq.dvd_of_dvd_pow hqv
      have hlt := h.lt_primeFactor_of_dvd_a hq hqa
      omega
    have hvz : (v : ZMod q) ≠ 0 := by
      intro hv0
      exact hq_not_dvd_v ((ZMod.natCast_eq_zero_iff v q).mp hv0)
    have hsumz : (u : ZMod q) ^ 2 + (v : ZMod q) ^ 2 = 0 := by
      have hz := (ZMod.natCast_eq_zero_iff T q).mpr hqT
      simpa [T] using hz
    have hsquare : IsSquare (-1 : ZMod q) := by
      refine ⟨(u : ZMod q) / (v : ZMod q), ?_⟩
      field_simp [hvz]
      linear_combination -hsumz
    have hqmod : q % 4 ≠ 3 := ZMod.exists_sq_eq_neg_one_iff.mp hsquare
    interval_cases q
    all_goals try norm_num at hq
    all_goals try contradiction
    all_goals try norm_num at hqmod
    all_goals simp

  have hN_dvd_bound : N ∣ 5 ^ 3 * 13 := by
    rw [Nat.dvd_iff_prime_pow_dvd_dvd]
    intro q j hq hqjN
    by_cases hj0 : j = 0
    · subst j
      simp
    have hqN : q ∣ N := (dvd_pow_self q hj0).trans hqjN
    rcases hprime_class hq hqN with hq5 | hq13
    · subst q
      have hj_fac : 5 ^ j ∣ Nat.factorial 16 := hqjN.trans hN_dvd_fac
      have hj_le : j ≤ 3 := by
        by_contra hj
        have hfour_le : 4 ≤ j := by omega
        have hbad : 5 ^ 4 ∣ Nat.factorial 16 :=
          (pow_dvd_pow 5 hfour_le).trans hj_fac
        have : ¬ 5 ^ 4 ∣ Nat.factorial 16 := by decide
        exact this hbad
      exact (pow_dvd_pow 5 hj_le).trans (dvd_mul_right (5 ^ 3) 13)
    · subst q
      have hj_fac : 13 ^ j ∣ Nat.factorial 16 := hqjN.trans hN_dvd_fac
      have hj_le : j ≤ 1 := by
        by_contra hj
        have htwo_le : 2 ≤ j := by omega
        have hbad : 13 ^ 2 ∣ Nat.factorial 16 :=
          (pow_dvd_pow 13 htwo_le).trans hj_fac
        have : ¬ 13 ^ 2 ∣ Nat.factorial 16 := by decide
        exact this hbad
      have hj13 : 13 ^ j ∣ 13 := by
        simpa using (pow_dvd_pow 13 hj_le : 13 ^ j ∣ 13 ^ 1)
      exact hj13.trans (dvd_mul_left 13 (5 ^ 3))
  have hN_le : N ≤ 5 ^ 3 * 13 := Nat.le_of_dvd (by norm_num) hN_dvd_bound
  have hT_le : T ≤ 2 * (5 ^ 3 * 13) := by omega
  have ha8_le_T : a ^ 8 ≤ T := by
    dsimp [T, v]
    rw [show 8 = 4 * 2 by norm_num, pow_mul]
    exact Nat.le_add_left _ _
  have ha19 : 19 ≤ a := by
    have := h.p_add_two_le_a ha1
    norm_num at this
    exact this
  have h19pow : 19 ^ 8 ≤ a ^ 8 := Nat.pow_le_pow_left ha19 8
  norm_num at hN_le hT_le h19pow ⊢
  omega

/-- For every Fermat-number branch after `17`, reduction modulo `17` forces
the exponent on the Fermat number to be a multiple of eight. -/
theorem IsSolution.eight_dvd_k_of_eq_fermatNumber (h : IsSolution p a k)
    {m : ℕ} (hm : 3 ≤ m) (hp : p = Nat.fermatNumber m) : 8 ∣ k := by
  subst p
  let _ : Fact (Nat.Prime 17) := ⟨by norm_num⟩
  have hp257 : 257 ≤ Nat.fermatNumber m := by
    have hmono := Nat.fermatNumber_mono hm
    norm_num at hmono ⊢
    exact hmono
  have h17_not_dvd_a : ¬ 17 ∣ a := by
    intro h17a
    have hlt := h.lt_primeFactor_of_dvd_a (by norm_num : Nat.Prime 17) h17a
    omega
  have ha0 : (a : ZMod 17) ≠ 0 := by
    intro hz
    exact h17_not_dvd_a ((ZMod.natCast_eq_zero_iff a 17).mp hz)
  have ha16 : (a : ZMod 17) ^ 16 = 1 := by
    simpa using ZMod.pow_card_sub_one_eq_one ha0
  have h8_exp : 8 ∣ 2 ^ m := by
    simpa using (pow_dvd_pow 2 hm : 2 ^ 3 ∣ 2 ^ m)
  obtain ⟨s, hs⟩ := h8_exp
  have hpz : (Nat.fermatNumber m : ZMod 17) = 2 := by
    rw [Nat.fermatNumber, hs]
    simp only [Nat.cast_add, Nat.cast_pow, Nat.cast_ofNat, Nat.cast_one]
    rw [pow_mul]
    have h2pow8 : (2 : ZMod 17) ^ 8 = 1 := by decide
    rw [h2pow8, one_pow]
    norm_num
  have hpow3_le : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hfour_le_exp : 4 ≤ 2 ^ m := by
    norm_num at hpow3_le ⊢
    omega
  have h16_full_exp : 16 ∣ 2 ^ (2 ^ m) := by
    simpa using (pow_dvd_pow 2 hfour_le_exp : 2 ^ 4 ∣ 2 ^ (2 ^ m))
  obtain ⟨r, hr⟩ := h16_full_exp
  have ha_full : (a : ZMod 17) ^ (Nat.fermatNumber m - 1) = 1 := by
    rw [Nat.fermatNumber, Nat.add_sub_cancel, hr, pow_mul, ha16, one_pow]
  have hfac17 : 17 ∣ (Nat.fermatNumber m - 1).factorial :=
    Nat.dvd_factorial (by norm_num) (by omega)
  have hfacz : (((Nat.fermatNumber m - 1).factorial : ℕ) : ZMod 17) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hfac17
  have heq := congrArg (fun n : ℕ ↦ (n : ZMod 17)) h.equation
  simp only [Nat.cast_add, Nat.cast_pow] at heq
  rw [hfacz, zero_add, ha_full, hpz] at heq
  have hpow : (2 : ZMod 17) ^ k = 1 := heq.symm
  have hpow8 : (2 : ZMod 17) ^ 8 = 1 := by decide
  have hk_decomp : k = 8 * (k / 8) + k % 8 := by omega
  have hpow_rem : (2 : ZMod 17) ^ (k % 8) = 1 := by
    rw [hk_decomp, pow_add, pow_mul, hpow8, one_pow, one_mul] at hpow
    exact hpow
  have hrem_lt : k % 8 < 8 := Nat.mod_lt _ (by norm_num)
  have hrem_zero : k % 8 = 0 := by
    interval_cases hrem : k % 8
    · rfl
    · exact ((by decide : (2 : ZMod 17) ^ 1 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 2 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 3 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 4 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 5 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 6 ≠ 1) hpow_rem).elim
    · exact ((by decide : (2 : ZMod 17) ^ 7 ≠ 1) hpow_rem).elim
  exact Nat.dvd_iff_mod_eq_zero.mpr hrem_zero

/-- A solution on a Fermat-number branch `F_m`, `m ≥ 3`, would make a
factorial the difference of two positive coprime eighth powers. -/
theorem IsSolution.exists_factorial_eighth_power_difference
    (h : IsSolution p a k) {m : ℕ} (hm : 3 ≤ m)
    (hp : p = Nat.fermatNumber m) :
    ∃ X Y : ℕ, 0 < X ∧ 0 < Y ∧ X.Coprime Y ∧
      X ^ 8 - Y ^ 8 = (p - 1).factorial := by
  have h8k : 8 ∣ k := h.eight_dvd_k_of_eq_fermatNumber hm hp
  have hpow3_le : 2 ^ 3 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  have hthree_le_exp : 3 ≤ 2 ^ m := by omega
  have h8pred : 8 ∣ p - 1 := by
    rw [hp, Nat.fermatNumber, Nat.add_sub_cancel]
    simpa using (pow_dvd_pow 2 hthree_le_exp : 2 ^ 3 ∣ 2 ^ (2 ^ m))
  refine ⟨p ^ (k / 8), a ^ ((p - 1) / 8), pow_pos h.prime.pos _, pow_pos h.a_pos _,
    Nat.Coprime.pow _ _ h.coprime, ?_⟩
  have hk_decomp : 8 * (k / 8) = k := Nat.mul_div_cancel' h8k
  have hp_decomp : 8 * ((p - 1) / 8) = p - 1 := Nat.mul_div_cancel' h8pred
  have hrewrite_p : (p ^ (k / 8)) ^ 8 = p ^ k := by
    rw [← pow_mul, mul_comm, hk_decomp]
  have hrewrite_a : (a ^ ((p - 1) / 8)) ^ 8 = a ^ (p - 1) := by
    rw [← pow_mul, mul_comm, hp_decomp]
  rw [hrewrite_p, hrewrite_a]
  have heq := h.equation
  omega

end ElementaryReductions

section Nagell

/-! The fixed-base Nagell equation needed for `p = 3`.  We use the
quadratic ring `ℤ[√-2]`, but prove the only factorization statement that is
needed by an explicit descent on the norm; no unproved unique-factorization
assumption is introduced. -/

private abbrev ZsqrtNegTwo := Zsqrtd (-2)

private def nagellBeta : ZsqrtNegTwo := ⟨1, 1⟩

private def nagellBetaBar : ZsqrtNegTwo := ⟨1, -1⟩

@[simp] private theorem nagellBeta_re : nagellBeta.re = 1 := rfl
@[simp] private theorem nagellBeta_im : nagellBeta.im = 1 := rfl
@[simp] private theorem nagellBetaBar_re : nagellBetaBar.re = 1 := rfl
@[simp] private theorem nagellBetaBar_im : nagellBetaBar.im = -1 := rfl

private theorem nagellBeta_mul_bar : nagellBeta * nagellBetaBar = 3 := by
  ext <;> norm_num [nagellBeta, nagellBetaBar]

private theorem nagellBetaBar_mul_beta : nagellBetaBar * nagellBeta = 3 := by
  rw [mul_comm, nagellBeta_mul_bar]

private theorem isCoprime_three_dvd_both_false {A B : ℤ}
    (hcop : IsCoprime A B) (hA : (3 : ℤ) ∣ A) (hB : (3 : ℤ) ∣ B) : False := by
  rcases hcop with ⟨u, v, huv⟩
  have hthree_one : (3 : ℤ) ∣ 1 := by
    rw [← huv]
    exact dvd_add (dvd_mul_of_dvd_right hA u) (dvd_mul_of_dvd_right hB v)
  norm_num at hthree_one

/-- Primitive representations by the quadratic form `A² + 2B²` of a
power of three are obtained by taking a power of one of the two conjugate
elements of norm three, up to sign. -/
private theorem primitive_norm_three_pow_representation :
    ∀ (n : ℕ) (A B : ℤ), IsCoprime A B →
      A * A + 2 * B * B = (3 : ℤ) ^ n →
      (⟨A, B⟩ : ZsqrtNegTwo) = nagellBeta ^ n ∨
      (⟨A, B⟩ : ZsqrtNegTwo) = -(nagellBeta ^ n) ∨
      (⟨A, B⟩ : ZsqrtNegTwo) = nagellBetaBar ^ n ∨
      (⟨A, B⟩ : ZsqrtNegTwo) = -(nagellBetaBar ^ n) := by
  intro n
  induction n with
  | zero =>
      intro A B _hcop hnorm
      simp only [pow_zero] at hnorm ⊢
      have hBsq : B * B = 0 := by
        nlinarith [mul_self_nonneg A, mul_self_nonneg B]
      have hB : B = 0 := (mul_self_eq_zero.mp hBsq)
      have hAsq : A * A = 1 := by simpa [hB] using hnorm
      rcases (mul_self_eq_one_iff.mp hAsq) with hA | hA
      · left
        ext
        · simp [hA]
        · exact hB
      · right; left
        ext
        · simp [hA]
        · exact hB
  | succ n ih =>
      intro A B hcop hnorm
      have hthree_norm : (3 : ℤ) ∣ A * A + 2 * B * B := by
        refine ⟨3 ^ n, ?_⟩
        rw [hnorm, pow_succ']
      have hthree_diff : (3 : ℤ) ∣ (A - B) * (A + B) := by
        rcases hthree_norm with ⟨c, hc⟩
        refine ⟨c - B * B, ?_⟩
        nlinarith
      rcases Int.prime_three.dvd_mul.mp hthree_diff with hminus | hplus
      · rcases hminus with ⟨t, ht⟩
        let C : ℤ := t + B
        let D : ℤ := -t
        have hA : A = C - 2 * D := by dsimp [C, D]; omega
        have hB : B = C + D := by dsimp [C, D]; ring
        have hnormCD : C * C + 2 * D * D = (3 : ℤ) ^ n := by
          have h := hnorm
          rw [hA, hB, pow_succ'] at h
          nlinarith
        have hcopCD : IsCoprime C D := by
          rcases hcop with ⟨u, v, huv⟩
          refine ⟨u + v, -2 * u + v, ?_⟩
          rw [hA, hB] at huv
          nlinarith
        have hzmul : (⟨A, B⟩ : ZsqrtNegTwo) =
            nagellBeta * (⟨C, D⟩ : ZsqrtNegTwo) := by
          ext <;> simp [nagellBeta, hA, hB] <;> ring
        have hthreeA_B_of_mixed (hneg : Bool) {r : ℕ}
            (hw : (⟨C, D⟩ : ZsqrtNegTwo) =
              if hneg then -(nagellBetaBar ^ (r + 1))
              else nagellBetaBar ^ (r + 1)) : False := by
          have hzdiv : ∃ w : ZsqrtNegTwo,
              (⟨A, B⟩ : ZsqrtNegTwo) = 3 * w := by
            refine ⟨if hneg then -(nagellBetaBar ^ r) else nagellBetaBar ^ r, ?_⟩
            rw [hzmul, hw, pow_succ']
            cases hneg <;> simp only [Bool.false_eq_true, if_false, if_true, mul_neg] <;>
              rw [← mul_assoc, nagellBeta_mul_bar] <;> ring
          rcases hzdiv with ⟨w, hw⟩
          have h3A : (3 : ℤ) ∣ A := by
            refine ⟨w.re, ?_⟩
            have := congrArg Zsqrtd.re hw
            simpa using this
          have h3B : (3 : ℤ) ∣ B := by
            refine ⟨w.im, ?_⟩
            have := congrArg Zsqrtd.im hw
            simpa using this
          exact isCoprime_three_dvd_both_false hcop h3A h3B
        rcases ih C D hcopCD hnormCD with hw | hw | hw | hw
        · left
          rw [hzmul, hw, pow_succ']
        · right; left
          rw [hzmul, hw, pow_succ', mul_neg, neg_inj]
        · cases n with
          | zero =>
              left
              simpa using hzmul.trans (congrArg (nagellBeta * ·) hw)
          | succ r => exact (hthreeA_B_of_mixed false hw).elim
        · cases n with
          | zero =>
              right; left
              simpa using hzmul.trans (congrArg (nagellBeta * ·) hw)
          | succ r => exact (hthreeA_B_of_mixed true hw).elim
      · rcases hplus with ⟨t, ht⟩
        let C : ℤ := t - B
        let D : ℤ := t
        have hA : A = C + 2 * D := by dsimp [C, D]; omega
        have hB : B = -C + D := by dsimp [C, D]; ring
        have hnormCD : C * C + 2 * D * D = (3 : ℤ) ^ n := by
          have h := hnorm
          rw [hA, hB, pow_succ'] at h
          nlinarith
        have hcopCD : IsCoprime C D := by
          rcases hcop with ⟨u, v, huv⟩
          refine ⟨u - v, 2 * u + v, ?_⟩
          rw [hA, hB] at huv
          nlinarith
        have hzmul : (⟨A, B⟩ : ZsqrtNegTwo) =
            nagellBetaBar * (⟨C, D⟩ : ZsqrtNegTwo) := by
          ext <;> simp [nagellBetaBar, hA, hB] <;> ring
        have hthreeA_B_of_mixed (hneg : Bool) {r : ℕ}
            (hw : (⟨C, D⟩ : ZsqrtNegTwo) =
              if hneg then -(nagellBeta ^ (r + 1))
              else nagellBeta ^ (r + 1)) : False := by
          have hzdiv : ∃ w : ZsqrtNegTwo,
              (⟨A, B⟩ : ZsqrtNegTwo) = 3 * w := by
            refine ⟨if hneg then -(nagellBeta ^ r) else nagellBeta ^ r, ?_⟩
            rw [hzmul, hw, pow_succ']
            cases hneg <;> simp only [Bool.false_eq_true, if_false, if_true, mul_neg] <;>
              rw [← mul_assoc, nagellBetaBar_mul_beta] <;> ring
          rcases hzdiv with ⟨w, hw⟩
          have h3A : (3 : ℤ) ∣ A := by
            refine ⟨w.re, ?_⟩
            have := congrArg Zsqrtd.re hw
            simpa using this
          have h3B : (3 : ℤ) ∣ B := by
            refine ⟨w.im, ?_⟩
            have := congrArg Zsqrtd.im hw
            simpa using this
          exact isCoprime_three_dvd_both_false hcop h3A h3B
        rcases ih C D hcopCD hnormCD with hw | hw | hw | hw
        · cases n with
          | zero =>
              right; right; left
              simpa using hzmul.trans (congrArg (nagellBetaBar * ·) hw)
          | succ r => exact (hthreeA_B_of_mixed false hw).elim
        · cases n with
          | zero =>
              right; right; right
              simpa using hzmul.trans (congrArg (nagellBetaBar * ·) hw)
          | succ r => exact (hthreeA_B_of_mixed true hw).elim
        · right; right; left
          rw [hzmul, hw, pow_succ']
        · right; right; right
          rw [hzmul, hw, pow_succ', mul_neg, neg_inj]

/-- The key 2-adic approximation from the elementary proof of Nagell's
theorem. -/
private theorem nagellBeta_two_pow_expansion (t : ℕ) (ht : 2 ≤ t) :
    ∃ μ : ZsqrtNegTwo,
      nagellBeta ^ (2 ^ t) =
        1 + (2 : ZsqrtNegTwo) ^ t * (1 + nagellBeta) +
          (2 : ZsqrtNegTwo) ^ (t + 1) * μ := by
  induction t, ht using Nat.le_induction with
  | base =>
      refine ⟨⟨-2, -1⟩, ?_⟩
      ext <;> norm_num [nagellBeta, pow_succ]
  | succ t ht ih =>
      rcases ih with ⟨μ, hμ⟩
      let c : ZsqrtNegTwo := (2 : ZsqrtNegTwo) ^ t
      let d : ZsqrtNegTwo := (2 : ZsqrtNegTwo) ^ (t - 2)
      have hc : c = 4 * d := by
        dsimp [c, d]
        calc
          (2 : ZsqrtNegTwo) ^ t = (2 : ZsqrtNegTwo) ^ (2 + (t - 2)) := by
            congr 1
            omega
          _ = 4 * (2 : ZsqrtNegTwo) ^ (t - 2) := by rw [pow_add]; ring
      have h2c : (2 : ZsqrtNegTwo) ^ (t + 1) = 2 * c := by
        dsimp [c]
        rw [pow_succ']
      have h4c : (2 : ZsqrtNegTwo) ^ (t + 1 + 1) = 4 * c := by
        rw [pow_succ', h2c]
        ring
      rw [h2c] at hμ
      refine ⟨μ + d * (1 + nagellBeta) ^ 2 +
          c * (1 + nagellBeta) * μ + c * μ ^ 2, ?_⟩
      rw [show 2 ^ (t + 1) = (2 ^ t) * 2 by rw [pow_succ], pow_mul, hμ,
        h2c, h4c]
      change
        (1 + c * (1 + nagellBeta) + 2 * c * μ) ^ 2 =
          1 + (2 * c) * (1 + nagellBeta) +
            (4 * c) *
              (μ + d * (1 + nagellBeta) ^ 2 +
                c * (1 + nagellBeta) * μ + c * μ ^ 2)
      rw [hc]
      ring

/-- The preceding approximation remains first-order after raising to an
arbitrary power. -/
private theorem nagellBeta_two_pow_mul_expansion (t b : ℕ) (ht : 2 ≤ t) :
    ∃ μ : ZsqrtNegTwo,
      nagellBeta ^ (2 ^ t * b) =
        1 + (b : ZsqrtNegTwo) * (2 : ZsqrtNegTwo) ^ t * (1 + nagellBeta) +
          (2 : ZsqrtNegTwo) ^ (t + 1) * μ := by
  rcases nagellBeta_two_pow_expansion t ht with ⟨μ₀, hμ₀⟩
  induction b with
  | zero =>
      refine ⟨0, ?_⟩
      simp
  | succ b ih =>
      rcases ih with ⟨ν, hν⟩
      let c : ZsqrtNegTwo := (2 : ZsqrtNegTwo) ^ t
      let d : ZsqrtNegTwo := (2 : ZsqrtNegTwo) ^ (t - 1)
      have hc : c = 2 * d := by
        dsimp [c, d]
        calc
          (2 : ZsqrtNegTwo) ^ t = (2 : ZsqrtNegTwo) ^ (1 + (t - 1)) := by
            congr 1
            omega
          _ = 2 * (2 : ZsqrtNegTwo) ^ (t - 1) := by rw [pow_add]; ring
      have h2c : (2 : ZsqrtNegTwo) ^ (t + 1) = 2 * c := by
        dsimp [c]
        rw [pow_succ']
      rw [h2c] at hμ₀ hν
      refine ⟨μ₀ + ν + (b : ZsqrtNegTwo) * d * (1 + nagellBeta) ^ 2 +
          (b : ZsqrtNegTwo) * c * (1 + nagellBeta) * μ₀ +
          c * ν * (1 + nagellBeta) + 2 * c * ν * μ₀, ?_⟩
      rw [Nat.mul_succ, pow_add, hν, hμ₀, h2c, Nat.cast_succ]
      change
        (1 + (b : ZsqrtNegTwo) * c * (1 + nagellBeta) + 2 * c * ν) *
            (1 + c * (1 + nagellBeta) + 2 * c * μ₀) =
          1 + ((b : ZsqrtNegTwo) + 1) * c * (1 + nagellBeta) +
            2 * c *
              (μ₀ + ν + (b : ZsqrtNegTwo) * d * (1 + nagellBeta) ^ 2 +
                (b : ZsqrtNegTwo) * c * (1 + nagellBeta) * μ₀ +
                c * ν * (1 + nagellBeta) + 2 * c * ν * μ₀)
      rw [hc]
      ring

private theorem nagellBetaBar_eq_star : nagellBetaBar = star nagellBeta := by
  ext <;> simp [nagellBeta, nagellBetaBar]

private theorem nagellBetaBar_pow_im (n : ℕ) :
    (nagellBetaBar ^ n).im = -(nagellBeta ^ n).im := by
  rw [nagellBetaBar_eq_star, ← star_pow]
  exact Zsqrtd.im_star (nagellBeta ^ n)

/-- In a primitive solution with right-hand side `3^k`, the imaginary
coefficient of `(1 + √-2)^k` is `1` or `-1`. -/
private theorem nagellBeta_pow_im_eq_one_or_neg_one {x k : ℕ}
    (heq : x ^ 2 + 2 = 3 ^ k) :
    (nagellBeta ^ k).im = 1 ∨ (nagellBeta ^ k).im = -1 := by
  have hnorm : (x : ℤ) * (x : ℤ) + 2 * (1 : ℤ) * (1 : ℤ) = (3 : ℤ) ^ k := by
    have hi := congrArg (fun n : ℕ ↦ (n : ℤ)) heq
    norm_num [pow_two] at hi ⊢
    exact hi
  have hcop : IsCoprime (x : ℤ) (1 : ℤ) := isCoprime_one_right
  rcases primitive_norm_three_pow_representation k x 1 hcop hnorm with h | h | h | h
  · left
    have hi := congrArg Zsqrtd.im h
    simpa using hi.symm
  · right
    have hi := congrArg Zsqrtd.im h
    simp only [Zsqrtd.im_neg] at hi
    omega
  · right
    have hi := congrArg Zsqrtd.im h
    change (1 : ℤ) = (nagellBetaBar ^ k).im at hi
    rw [nagellBetaBar_pow_im] at hi
    omega
  · left
    have hi := congrArg Zsqrtd.im h
    change (1 : ℤ) = (-(nagellBetaBar ^ k)).im at hi
    simp only [Zsqrtd.im_neg] at hi
    rw [nagellBetaBar_pow_im] at hi
    omega

private theorem exists_two_pow_mul_odd_of_four_dvd {d : ℕ}
    (hd : d ≠ 0) (h4d : 4 ∣ d) :
    ∃ t b : ℕ, 2 ≤ t ∧ Odd b ∧ d = 2 ^ t * b := by
  obtain ⟨t, b, hb, hdb⟩ := Nat.exists_eq_two_pow_mul_odd hd
  have ht : 2 ≤ t := by
    by_contra htn
    have ht1 : t ≤ 1 := by omega
    rcases h4d with ⟨c, hc⟩
    rcases hb with ⟨w, hw⟩
    interval_cases t <;> norm_num at hdb <;> omega
  exact ⟨t, b, ht, hb, hdb⟩

/-- The fixed-base Nagell theorem needed in Erdős 405. -/
theorem nagell_three_power {x k : ℕ} (hx : 0 < x) (hk : Odd k)
    (heq : x ^ 2 + 2 = 3 ^ k) :
    (x = 1 ∧ k = 1) ∨ (x = 5 ∧ k = 3) := by
  by_cases hk1 : k = 1
  · left
    refine ⟨?_, hk1⟩
    subst k
    norm_num at heq
    nlinarith
  by_cases hk3 : k = 3
  · right
    refine ⟨?_, hk3⟩
    subst k
    norm_num at heq
    nlinarith
  have hkgt : 3 < k := by
    rcases hk with ⟨s, hs⟩
    omega
  have him := nagellBeta_pow_im_eq_one_or_neg_one heq
  have hrem_lt : k % 4 < 4 := Nat.mod_lt _ (by norm_num)
  have hrem : k % 4 = 1 ∨ k % 4 = 3 := by
    rcases hk with ⟨s, hs⟩
    omega
  rcases hrem with hrem | hrem
  · let d := k - 1
    have hd : d ≠ 0 := by dsimp [d]; omega
    have h4d : 4 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero]
      dsimp [d]
      omega
    obtain ⟨t, b, ht, hb, hdb⟩ := exists_two_pow_mul_odd_of_four_dvd hd h4d
    rcases nagellBeta_two_pow_mul_expansion t b ht with ⟨μ, hμ⟩
    let c : ℤ := (2 : ℤ) ^ t
    have hcast_t : (2 : ZsqrtNegTwo) ^ t = ((2 ^ t : ℕ) : ZsqrtNegTwo) := by
      norm_cast
    have hcast_succ : (2 : ZsqrtNegTwo) ^ (t + 1) =
        ((2 ^ (t + 1) : ℕ) : ZsqrtNegTwo) := by
      norm_cast
    rw [hcast_t, hcast_succ] at hμ
    have hk_decomp : k = d + 1 := by dsimp [d]; omega
    have him_formula : (nagellBeta ^ k).im =
        1 + 3 * (b : ℤ) * c + 2 * c * (μ.re + μ.im) := by
      rw [hk_decomp, hdb, pow_add, hμ]
      dsimp [c]
      simp [nagellBeta, pow_succ]
      ring
    rcases him with him | him
    · rw [him] at him_formula
      have hcpos : (0 : ℤ) < c := by dsimp [c]; positivity
      have hzero : 3 * (b : ℤ) + 2 * (μ.re + μ.im) = 0 := by
        nlinarith
      rcases hb with ⟨w, hw⟩
      rw [hw] at hzero
      push_cast at hzero
      omega
    · rw [him] at him_formula
      have hc_dvd_two : c ∣ (2 : ℤ) := by
        refine ⟨-(3 * (b : ℤ) + 2 * (μ.re + μ.im)), ?_⟩
        nlinarith
      have h4c : (4 : ℤ) ∣ c := by
        rcases (pow_dvd_pow 2 ht : 2 ^ 2 ∣ 2 ^ t) with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        dsimp [c]
        exact_mod_cast hz
      have : ¬ (4 : ℤ) ∣ 2 := by norm_num
      exact (this (h4c.trans hc_dvd_two)).elim
  · let d := k - 3
    have hd : d ≠ 0 := by dsimp [d]; omega
    have h4d : 4 ∣ d := by
      rw [Nat.dvd_iff_mod_eq_zero]
      dsimp [d]
      omega
    obtain ⟨t, b, ht, hb, hdb⟩ := exists_two_pow_mul_odd_of_four_dvd hd h4d
    rcases nagellBeta_two_pow_mul_expansion t b ht with ⟨μ, hμ⟩
    let c : ℤ := (2 : ℤ) ^ t
    have hcast_t : (2 : ZsqrtNegTwo) ^ t = ((2 ^ t : ℕ) : ZsqrtNegTwo) := by
      norm_cast
    have hcast_succ : (2 : ZsqrtNegTwo) ^ (t + 1) =
        ((2 ^ (t + 1) : ℕ) : ZsqrtNegTwo) := by
      norm_cast
    rw [hcast_t, hcast_succ] at hμ
    have hk_decomp : k = d + 3 := by dsimp [d]; omega
    have him_formula : (nagellBeta ^ k).im =
        1 - 3 * (b : ℤ) * c + 2 * c * (μ.re - 5 * μ.im) := by
      rw [hk_decomp, hdb, pow_add, hμ]
      dsimp [c]
      simp [nagellBeta, pow_succ]
      ring
    rcases him with him | him
    · rw [him] at him_formula
      have hcpos : (0 : ℤ) < c := by dsimp [c]; positivity
      have hzero : -3 * (b : ℤ) + 2 * (μ.re - 5 * μ.im) = 0 := by
        nlinarith
      rcases hb with ⟨w, hw⟩
      rw [hw] at hzero
      push_cast at hzero
      omega
    · rw [him] at him_formula
      have hc_dvd_two : c ∣ (2 : ℤ) := by
        refine ⟨-(-3 * (b : ℤ) + 2 * (μ.re - 5 * μ.im)), ?_⟩
        nlinarith
      have h4c : (4 : ℤ) ∣ c := by
        rcases (pow_dvd_pow 2 ht : 2 ^ 2 ∣ 2 ^ t) with ⟨z, hz⟩
        refine ⟨z, ?_⟩
        dsimp [c]
        exact_mod_cast hz
      have : ¬ (4 : ℤ) ∣ 2 := by norm_num
      exact (this (h4c.trans hc_dvd_two)).elim

/-- Complete classification when the odd prime is `3`. -/
theorem IsSolution.eq_of_p_eq_three {p a k : ℕ} (h : IsSolution p a k)
    (hp : p = 3) : (a = 1 ∧ k = 1) ∨ (a = 5 ∧ k = 3) := by
  have heq := h.equation_of_p_eq_three hp
  have hkodd := h.k_odd_of_p_eq_three hp
  exact nagell_three_power h.a_pos hkodd heq

end Nagell

section ErdosOblath

/-! Algebraic part of the Erdős--Obláth factorial power-difference
theorems. -/

/-- Every odd prime divisor of a sum of two coprime fourth powers is
`1 mod 8`. -/
theorem prime_mod_eight_of_dvd_coprime_fourth_power_sum
    {X Y r : ℕ} (hcop : X.Coprime Y) (hr : r.Prime) (hr2 : r ≠ 2)
    (hrsum : r ∣ X ^ 4 + Y ^ 4) : r % 8 = 1 := by
  let _ : Fact r.Prime := ⟨hr⟩
  have hr3 : 3 ≤ r := hr.odd_iff.mp (hr.odd_of_ne_two hr2)
  let _ : Fact (2 < r) := ⟨by omega⟩
  have hnot_both : ¬ (r ∣ X ∧ r ∣ Y) := by
    rintro ⟨hrX, hrY⟩
    exact (Nat.Prime.not_coprime_iff_dvd.mpr ⟨r, hr, hrX, hrY⟩) hcop
  have hr_not_dvd_X : ¬ r ∣ X := by
    intro hrX
    have hrY4 : r ∣ Y ^ 4 := by
      have hrX4 : r ∣ X ^ 4 := dvd_pow hrX (by norm_num)
      exact (Nat.dvd_add_iff_right hrX4).mpr hrsum
    exact hnot_both ⟨hrX, hr.dvd_of_dvd_pow hrY4⟩
  have hr_not_dvd_Y : ¬ r ∣ Y := by
    intro hrY
    have hrX4 : r ∣ X ^ 4 := by
      have hrY4 : r ∣ Y ^ 4 := dvd_pow hrY (by norm_num)
      exact (Nat.dvd_add_iff_left hrY4).mpr hrsum
    exact hnot_both ⟨hr.dvd_of_dvd_pow hrX4, hrY⟩
  have hX0 : (X : ZMod r) ≠ 0 := by
    intro h
    exact hr_not_dvd_X ((ZMod.natCast_eq_zero_iff X r).mp h)
  have hY0 : (Y : ZMod r) ≠ 0 := by
    intro h
    exact hr_not_dvd_Y ((ZMod.natCast_eq_zero_iff Y r).mp h)
  let z : ZMod r := (X : ZMod r) / (Y : ZMod r)
  have hsum0 : (X : ZMod r) ^ 4 + (Y : ZMod r) ^ 4 = 0 := by
    simpa using (ZMod.natCast_eq_zero_iff (X ^ 4 + Y ^ 4) r).mpr hrsum
  have hz4 : z ^ 4 = -1 := by
    dsimp [z]
    field_simp [hY0]
    linear_combination hsum0
  have hz8 : z ^ 8 = 1 := by
    rw [show 8 = 4 * 2 by norm_num, pow_mul, hz4]
    norm_num
  have hz4ne : z ^ 4 ≠ 1 := by
    rw [hz4]
    exact ZMod.neg_one_ne_one
  have horder_dvd8 : orderOf z ∣ 8 := orderOf_dvd_of_pow_eq_one hz8
  have horder_not_dvd4 : ¬ orderOf z ∣ 4 := by
    rwa [orderOf_dvd_iff_pow_eq_one]
  obtain ⟨j, hj, horder⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (show orderOf z ∣ 2 ^ 3 by simpa using horder_dvd8)
  have hj3 : j = 3 := by
    interval_cases j <;> simp_all
  have horder8 : orderOf z = 8 := by simp [horder, hj3]
  have hz0 : z ≠ 0 := div_ne_zero hX0 hY0
  have h8pred : 8 ∣ r - 1 := by
    rw [← horder8]
    exact ZMod.orderOf_dvd_card_sub_one hz0
  rcases h8pred with ⟨w, hw⟩
  omega

/-- The full prime-power part of `n!` supported on one residue class. -/
def factorialPrimeClassPart (n modulus residue : ℕ) : ℕ :=
  ∏ r ∈ n.factorial.factorization.support.filter (fun r ↦ r % modulus = residue),
    r ^ n.factorial.factorization r

private theorem factorialPrimeClassPart_pos (n modulus residue : ℕ) :
    0 < factorialPrimeClassPart n modulus residue := by
  unfold factorialPrimeClassPart
  exact Finset.prod_pos fun r hr ↦ pow_pos
    (Nat.Prime.pos (Nat.prime_of_mem_primeFactors (Finset.mem_filter.mp hr).1)) _

/-- A finite arithmetic-progression product, with indices `0, ..., m - 1`. -/
def arithmeticProgressionProduct (a b m : ℕ) : ℕ :=
  ∏ i ∈ Finset.range m, (a * i + b)

private theorem arithmeticProgressionProduct_ne_zero {a b m : ℕ} (hb : 0 < b) :
    arithmeticProgressionProduct a b m ≠ 0 := by
  apply Finset.prod_ne_zero_iff.mpr
  intro i hi
  exact (add_pos_of_nonneg_of_pos (Nat.zero_le _) hb).ne'

private theorem exists_progression_root_mod_prime {r a b : ℕ}
    (hr : r.Prime) (hra : ¬ r ∣ a) :
    ∃ c < r, r ∣ a * c + b := by
  let _ : Fact r.Prime := ⟨hr⟩
  have ha0 : (a : ZMod r) ≠ 0 := by
    intro ha0
    exact hra ((ZMod.natCast_eq_zero_iff a r).mp ha0)
  let z : ZMod r := -(a : ZMod r)⁻¹ * b
  refine ⟨z.val, z.val_lt, ?_⟩
  rw [← ZMod.natCast_eq_zero_iff]
  simp only [Nat.cast_add, Nat.cast_mul, ZMod.natCast_zmod_val]
  change (a : ZMod r) * z + b = 0
  simp [z, ha0]

private theorem progression_selected_product_dvd
    {r a b m : ℕ} (hr : r.Prime) (hb : 0 < b) (c : ℕ) (hc : c < r)
    (hrc : r ∣ a * c + b) :
    r ^ (m / r) * arithmeticProgressionProduct a ((a * c + b) / r) (m / r) ∣
      arithmeticProgressionProduct a b m := by
  let u := m / r
  let f : ℕ → ℕ := fun s ↦ c + r * s
  have hf_inj : Function.Injective f := by
    intro s t hst
    simp only [f] at hst
    exact Nat.eq_of_mul_eq_mul_left hr.pos (Nat.add_left_cancel hst)
  have hf_subset : (Finset.range u).image f ⊆ Finset.range m := by
    intro j hj
    simp only [Finset.mem_image, Finset.mem_range] at hj ⊢
    rcases hj with ⟨s, hs, rfl⟩
    have hmul : r * u ≤ m := Nat.mul_div_le m r
    simp only [f]
    calc
      c + r * s < r + r * s := Nat.add_lt_add_right hc (r * s)
      _ = r * (s + 1) := by ring
      _ ≤ r * u := Nat.mul_le_mul_left r (Nat.succ_le_iff.mpr hs)
      _ ≤ m := hmul
  have hselected :
      ∏ j ∈ (Finset.range u).image f, (a * j + b) =
        r ^ u * arithmeticProgressionProduct a ((a * c + b) / r) u := by
    rw [Finset.prod_image hf_inj.injOn]
    have hrc_eq : r * ((a * c + b) / r) = a * c + b := Nat.mul_div_cancel' hrc
    change Finset.prod (Finset.range u) (fun s ↦ a * f s + b) =
      r ^ u * Finset.prod (Finset.range u) (fun s ↦ a * s + (a * c + b) / r)
    calc
      Finset.prod (Finset.range u) (fun s ↦ a * f s + b) =
          Finset.prod (Finset.range u)
            (fun s ↦ r * (a * s + (a * c + b) / r)) := by
        apply Finset.prod_congr rfl
        intro s hs
        simp only [f]
        calc
          a * (c + r * s) + b = (a * c + b) + a * r * s := by ring
          _ = r * ((a * c + b) / r) + a * r * s := by rw [hrc_eq]
          _ = r * (a * s + (a * c + b) / r) := by ring
      _ = Finset.prod (Finset.range u) (fun _ ↦ r) *
          Finset.prod (Finset.range u) (fun s ↦ a * s + (a * c + b) / r) := by
        rw [Finset.prod_mul_distrib]
      _ = r ^ u * Finset.prod (Finset.range u)
          (fun s ↦ a * s + (a * c + b) / r) := by simp
  rw [← hselected]
  exact Finset.prod_dvd_prod_of_subset _ _ (fun j ↦ a * j + b) hf_subset

private theorem padicValNat_factorial_le_arithmeticProgressionProduct
    {r a : ℕ} (hr : r.Prime) (hra : ¬ r ∣ a) (m : ℕ) :
    ∀ {b : ℕ}, 0 < b → a.Coprime b →
      padicValNat r m.factorial ≤
        padicValNat r (arithmeticProgressionProduct a b m) := by
  let _ : Fact r.Prime := ⟨hr⟩
  induction m using Nat.strong_induction_on with
  | h m ih =>
      intro b hb hab
      by_cases hm0 : m = 0
      · subst m
        simp [arithmeticProgressionProduct]
      let u := m / r
      have hu_lt : u < m := Nat.div_lt_self (Nat.pos_of_ne_zero hm0) hr.one_lt
      obtain ⟨c, hc, hrc⟩ := exists_progression_root_mod_prime hr hra (b := b)
      let B := (a * c + b) / r
      have hnumpos : 0 < a * c + b := add_pos_of_nonneg_of_pos (Nat.zero_le _) hb
      have hBpos : 0 < B := by
        exact Nat.div_pos (Nat.le_of_dvd hnumpos hrc) hr.pos
      have hrc_eq : r * B = a * c + b := Nat.mul_div_cancel' hrc
      have hacb : a.Coprime (a * c + b) := by
        simpa [add_comm, mul_comm] using
          (Nat.coprime_add_mul_left_right a b c).mpr hab
      have harB : a.Coprime (r * B) := by simpa [hrc_eq] using hacb
      have haB : a.Coprime B := (Nat.coprime_mul_iff_right.mp harB).2
      have hrec : padicValNat r u.factorial ≤
          padicValNat r (arithmeticProgressionProduct a B u) :=
        ih u hu_lt hBpos haB
      have hselected_dvd :
          r ^ u * arithmeticProgressionProduct a B u ∣
            arithmeticProgressionProduct a b m := by
        exact progression_selected_product_dvd hr hb c hc hrc
      have hBprod0 : arithmeticProgressionProduct a B u ≠ 0 :=
        arithmeticProgressionProduct_ne_zero hBpos
      have hprod0 : arithmeticProgressionProduct a b m ≠ 0 :=
        arithmeticProgressionProduct_ne_zero hb
      have hselected0 : r ^ u * arithmeticProgressionProduct a B u ≠ 0 :=
        mul_ne_zero (pow_ne_zero _ hr.ne_zero) hBprod0
      have hval_selected :
          padicValNat r (r ^ u * arithmeticProgressionProduct a B u) =
            u + padicValNat r (arithmeticProgressionProduct a B u) := by
        rw [padicValNat.mul (pow_ne_zero _ hr.ne_zero) hBprod0,
          padicValNat.prime_pow]
      have hval_dvd :
          padicValNat r (r ^ u * arithmeticProgressionProduct a B u) ≤
            padicValNat r (arithmeticProgressionProduct a b m) := by
        exact (padicValNat_dvd_iff_le hprod0).mp
          (pow_padicValNat_dvd.trans hselected_dvd)
      calc
        padicValNat r m.factorial = padicValNat r (r * u).factorial := by
          simpa [u] using (padicValNat_mul_div_factorial (p := r) m).symm
        _ = padicValNat r u.factorial + u := padicValNat_factorial_mul u
        _ ≤ padicValNat r (arithmeticProgressionProduct a B u) + u :=
          Nat.add_le_add_right hrec u
        _ = u + padicValNat r (arithmeticProgressionProduct a B u) := by omega
        _ = padicValNat r (r ^ u * arithmeticProgressionProduct a B u) :=
          hval_selected.symm
        _ ≤ padicValNat r (arithmeticProgressionProduct a b m) := hval_dvd

private theorem factorial_dvd_two_pow_mul_eight_progression (m : ℕ) :
    m.factorial ∣ 2 ^ m * arithmeticProgressionProduct 8 9 m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  have hjle : j ≤ padicValNat r m.factorial :=
    (padicValNat_dvd_iff_le m.factorial_ne_zero).mp hrj
  by_cases hr2 : r = 2
  · subst r
    have hjm : j ≤ m := hjle.trans (padicValNat_factorial_le 2 m)
    exact (pow_dvd_pow 2 hjm).trans (dvd_mul_right _ _)
  · have hr8 : ¬ r ∣ 8 := by
      intro hr8
      have hrpow : r ∣ 2 ^ 3 := by
        convert hr8 using 1 <;> norm_num
      have hr2dvd : r ∣ 2 := hr.dvd_of_dvd_pow hrpow
      rcases (Nat.dvd_prime Nat.prime_two).mp hr2dvd with hr1 | hr2'
      · exact hr.ne_one hr1
      · exact hr2 hr2'
    have hval := padicValNat_factorial_le_arithmeticProgressionProduct
      hr hr8 m (b := 9) (by norm_num) (by norm_num)
    have hap0 : arithmeticProgressionProduct 8 9 m ≠ 0 :=
      arithmeticProgressionProduct_ne_zero (by norm_num)
    have hrjap : r ^ j ∣ arithmeticProgressionProduct 8 9 m :=
      (padicValNat_dvd_iff_le hap0).mpr (hjle.trans hval)
    exact hrjap.trans (dvd_mul_left _ _)

private theorem arithmeticProgressionProduct_self_succ_le (a m : ℕ) :
    arithmeticProgressionProduct a (a + 1) m ≤ (a + 1) ^ m * m.factorial := by
  unfold arithmeticProgressionProduct
  calc
    ∏ i ∈ Finset.range m, (a * i + (a + 1)) ≤
        ∏ i ∈ Finset.range m, ((a + 1) * (i + 1)) := by
      apply Finset.prod_le_prod
      · intro i hi
        positivity
      · intro i hi
        calc
          a * i + (a + 1) ≤ (a * i + (a + 1)) + i := Nat.le_add_right _ _
          _ = (a + 1) * (i + 1) := by ring
    _ = (∏ _i ∈ Finset.range m, (a + 1)) *
        ∏ i ∈ Finset.range m, (i + 1) := by
      rw [Finset.prod_mul_distrib]
    _ = (a + 1) ^ m * m.factorial := by
      simp [Finset.prod_range_add_one_eq_factorial]

/-- The corrected quotient used in the modulus-eight progression estimate. -/
def eightProgressionQuotient (m : ℕ) : ℕ :=
  (2 ^ m * arithmeticProgressionProduct 8 9 m) / m.factorial

private theorem factorial_mul_eightProgressionQuotient (m : ℕ) :
    m.factorial * eightProgressionQuotient m =
      2 ^ m * arithmeticProgressionProduct 8 9 m := by
  exact Nat.mul_div_cancel' (factorial_dvd_two_pow_mul_eight_progression m)

private theorem eightProgressionQuotient_le (m : ℕ) :
    eightProgressionQuotient m ≤ 18 ^ m := by
  have hmul : m.factorial * eightProgressionQuotient m ≤ m.factorial * 18 ^ m := by
    rw [factorial_mul_eightProgressionQuotient]
    calc
      2 ^ m * arithmeticProgressionProduct 8 9 m ≤
          2 ^ m * (9 ^ m * m.factorial) :=
        Nat.mul_le_mul_left _ (by simpa using arithmeticProgressionProduct_self_succ_le 8 m)
      _ = m.factorial * (2 ^ m * 9 ^ m) := by ac_rfl
      _ = m.factorial * (2 * 9) ^ m := by rw [mul_pow]
      _ = m.factorial * 18 ^ m := by norm_num
  exact Nat.le_of_mul_le_mul_left hmul m.factorial_pos

/-- The squarefree product of primes at most `n` in one residue class. -/
def primeClassPrimorial (n modulus residue : ℕ) : ℕ :=
  ((Finset.range (n + 1)).filter
    (fun r ↦ r.Prime ∧ r % modulus = residue)).prod id

private theorem primeClassPrimorial_pos (n modulus residue : ℕ) :
    0 < primeClassPrimorial n modulus residue := by
  unfold primeClassPrimorial
  exact Finset.prod_pos fun r hr ↦ Nat.Prime.pos (Finset.mem_filter.mp hr).2.1

private theorem eightProgressionQuotient_pos (m : ℕ) :
    0 < eightProgressionQuotient m := by
  have hright : 0 < 2 ^ m * arithmeticProgressionProduct 8 9 m :=
    mul_pos (pow_pos (by norm_num) m)
      (Nat.pos_of_ne_zero (arithmeticProgressionProduct_ne_zero (by norm_num)))
  have heq := factorial_mul_eightProgressionQuotient m
  by_contra hzero
  have hq0 : eightProgressionQuotient m = 0 := Nat.eq_zero_of_not_pos hzero
  rw [hq0, mul_zero] at heq
  omega

private theorem primeClassPrimorial_eight_dvd_step (n : ℕ) :
    primeClassPrimorial n 8 1 ∣
      primeClassPrimorial ((n - 1) / 8) 8 1 *
        eightProgressionQuotient ((n - 1) / 8) := by
  let m := (n - 1) / 8
  let S := (Finset.range (n + 1)).filter
    (fun r ↦ r.Prime ∧ r % 8 = 1)
  change S.prod id ∣ primeClassPrimorial m 8 1 * eightProgressionQuotient m
  have htarget_pos :
      0 < primeClassPrimorial m 8 1 * eightProgressionQuotient m :=
    mul_pos (primeClassPrimorial_pos _ _ _) (eightProgressionQuotient_pos _)
  refine (Finset.prod_dvd_prod_of_subset S
    (primeClassPrimorial m 8 1 * eightProgressionQuotient m).primeFactors id ?_).trans
      (Nat.prod_primeFactors_dvd _)
  intro r hrS
  apply Nat.mem_primeFactors.mpr
  have hrmem := Finset.mem_filter.mp hrS
  have hrlt : r < n + 1 := Finset.mem_range.mp hrmem.1
  have hrle : r ≤ n := by omega
  have hrp : r.Prime := hrmem.2.1
  have hrmod : r % 8 = 1 := hrmem.2.2
  refine ⟨hrp, ?_, htarget_pos.ne'⟩
  by_cases hrm : r ≤ m
  · have hrold : r ∈ (Finset.range (m + 1)).filter
        (fun r ↦ r.Prime ∧ r % 8 = 1) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hrp, hrmod⟩
    exact (Finset.dvd_prod_of_mem id hrold).trans (dvd_mul_right _ _)
  · have hmr : m < r := Nat.lt_of_not_ge hrm
    have hreight : r = 8 * (r / 8) + 1 := by
      have hdecomp := Nat.mod_add_div r 8
      omega
    have hri : 0 < r / 8 := by
      by_contra hzero
      have hdiv0 : r / 8 = 0 := Nat.eq_zero_of_not_pos hzero
      rw [hdiv0] at hreight
      norm_num at hreight
      exact hrp.ne_one hreight
    have hrdiv_le : r / 8 ≤ m := by
      dsimp only [m]
      omega
    let i := r / 8 - 1
    have hi : i < m := by
      dsimp only [i]
      omega
    have hterm : 8 * i + 9 = r := by
      dsimp only [i]
      omega
    have hrAP : r ∣ arithmeticProgressionProduct 8 9 m := by
      unfold arithmeticProgressionProduct
      have himem : i ∈ Finset.range m := Finset.mem_range.mpr hi
      have hdvdterm : r ∣ 8 * i + 9 := by rw [hterm]
      exact hdvdterm.trans (Finset.dvd_prod_of_mem (fun i ↦ 8 * i + 9) himem)
    have hrfac : r.Coprime m.factorial := hrp.coprime_factorial_of_lt hmr
    have hrmul : r ∣ m.factorial * eightProgressionQuotient m := by
      rw [factorial_mul_eightProgressionQuotient]
      exact hrAP.trans (dvd_mul_left _ _)
    have hrquot : r ∣ eightProgressionQuotient m := hrfac.dvd_mul_left.mp hrmul
    exact hrquot.trans (dvd_mul_left _ _)

private theorem primeClassPrimorial_eight_step_le (n : ℕ) :
    primeClassPrimorial n 8 1 ≤
      primeClassPrimorial ((n - 1) / 8) 8 1 *
        eightProgressionQuotient ((n - 1) / 8) := by
  exact Nat.le_of_dvd
    (mul_pos (primeClassPrimorial_pos _ _ _) (eightProgressionQuotient_pos _))
    (primeClassPrimorial_eight_dvd_step n)

theorem primeClassPrimorial_eight_pow_seven_le (n : ℕ) :
    primeClassPrimorial n 8 1 ^ 7 ≤ 18 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hfilter : (Finset.range (0 + 1)).filter
            (fun r ↦ r.Prime ∧ r % 8 = 1) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          intro hr
          have hr0 : r = 0 := by omega
          subst r
          exact Nat.not_prime_zero hr.2.1
        unfold primeClassPrimorial
        rw [hfilter]
        norm_num
      let m := (n - 1) / 8
      have hm_lt : m < n := by
        dsimp only [m]
        omega
      have h8m : 8 * m ≤ n := by
        dsimp only [m]
        omega
      calc
        primeClassPrimorial n 8 1 ^ 7 ≤
            (primeClassPrimorial m 8 1 * eightProgressionQuotient m) ^ 7 :=
          Nat.pow_le_pow_left (by simpa [m] using primeClassPrimorial_eight_step_le n) 7
        _ = primeClassPrimorial m 8 1 ^ 7 * eightProgressionQuotient m ^ 7 :=
          mul_pow _ _ _
        _ ≤ 18 ^ m * (18 ^ m) ^ 7 :=
          Nat.mul_le_mul (ih m hm_lt) (Nat.pow_le_pow_left (eightProgressionQuotient_le m) 7)
        _ = 18 ^ (8 * m) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          omega
        _ ≤ 18 ^ n := Nat.pow_le_pow_right (by norm_num) h8m

private theorem factorialPrimeClassPart_dvd_factorial (n modulus residue : ℕ) :
    factorialPrimeClassPart n modulus residue ∣ n.factorial := by
  unfold factorialPrimeClassPart
  have hsub : n.factorial.factorization.support.filter
      (fun r ↦ r % modulus = residue) ⊆ n.factorial.factorization.support :=
    Finset.filter_subset _ _
  have hprod := Finset.prod_dvd_prod_of_subset
    (n.factorial.factorization.support.filter (fun r ↦ r % modulus = residue))
    n.factorial.factorization.support
    (fun r ↦ r ^ n.factorial.factorization r) hsub
  have hfull : (∏ r ∈ n.factorial.factorization.support,
      r ^ n.factorial.factorization r) = n.factorial := by
    simpa only [Finsupp.prod] using
      n.factorial.prod_factorization_pow_eq_self n.factorial_ne_zero
  exact hprod.trans (dvd_of_eq hfull)

/-- Product of the squarefree `1 mod 8` prime layers that occur in `n!`.
The upper limit `n / 17` is exact because the least possible prime is `17`. -/
def eightPrimeClassLayerProduct (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 17)).prod (fun s ↦ primeClassPrimorial (n / s) 8 1)

private theorem eightPrimeClassLayerProduct_pos (n : ℕ) :
    0 < eightPrimeClassLayerProduct n := by
  exact Finset.prod_pos fun s hs ↦ primeClassPrimorial_pos _ _ _

private theorem seventeen_le_of_prime_mod_eight_one {r : ℕ}
    (hr : r.Prime) (hrmod : r % 8 = 1) : 17 ≤ r := by
  by_contra hr17
  have hrlt : r < 17 := Nat.lt_of_not_ge hr17
  have hdecomp := Nat.mod_add_div r 8
  have hquot : r / 8 ≤ 1 := by omega
  rcases Nat.le_one_iff_eq_zero_or_eq_one.mp hquot with hq0 | hq1
  · have hr1 : r = 1 := by omega
    exact hr.ne_one hr1
  · have hr9 : r = 9 := by omega
    subst r
    norm_num at hr

private theorem prime_pow_divides_eightPrimeClassLayerProduct
    {r n : ℕ} (hr : r.Prime) (hrmod : r % 8 = 1) :
    r ^ (n / r) ∣ eightPrimeClassLayerProduct n := by
  let u := n / r
  have hr17 : 17 ≤ r := seventeen_le_of_prime_mod_eight_one hr hrmod
  have hu_bound : u ≤ n / 17 := Nat.div_le_div_left hr17 (by norm_num)
  have hsubset : Finset.Icc 1 u ⊆ Finset.Icc 1 (n / 17) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
      (Finset.mem_Icc.mp hs).2.trans hu_bound⟩
  have hpoint : ∀ s ∈ Finset.Icc 1 u,
      r ∣ primeClassPrimorial (n / s) 8 1 := by
    intro s hs
    have hsdata := Finset.mem_Icc.mp hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsdata.1
    have hrsn : r * s ≤ n := by
      have hu_mul : r * u ≤ n := Nat.mul_div_le n r
      exact (Nat.mul_le_mul_left r hsdata.2).trans hu_mul
    have hrle : r ≤ n / s := (Nat.le_div_iff_mul_le hspos).mpr hrsn
    unfold primeClassPrimorial
    apply Finset.dvd_prod_of_mem id
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hr, hrmod⟩
  calc
    r ^ u = (Finset.Icc 1 u).prod (fun _ ↦ r) := by simp
    _ ∣ (Finset.Icc 1 u).prod (fun s ↦ primeClassPrimorial (n / s) 8 1) :=
      Finset.prod_dvd_prod_of_dvd _ _ hpoint
    _ ∣ (Finset.Icc 1 (n / 17)).prod
        (fun s ↦ primeClassPrimorial (n / s) 8 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsubset

private theorem sixteen_mul_factorialVal_le_seventeen_mul_div
    {r n : ℕ} (hr : r.Prime) (hrmod : r % 8 = 1) :
    16 * padicValNat r n.factorial ≤ 17 * (n / r) := by
  let _ : Fact r.Prime := ⟨hr⟩
  let u := n / r
  have hr17 : 17 ≤ r := seventeen_le_of_prime_mod_eight_one hr hrmod
  have hvalfac : padicValNat r n.factorial = padicValNat r u.factorial + u := by
    calc
      padicValNat r n.factorial = padicValNat r (r * u).factorial := by
        simpa [u] using (padicValNat_mul_div_factorial (p := r) n).symm
      _ = padicValNat r u.factorial + u := padicValNat_factorial_mul u
  have htail : 16 * padicValNat r u.factorial ≤ u := by
    by_cases hu0 : u = 0
    · have hval0 : padicValNat r u.factorial = 0 := by
        rw [hu0]
        apply padicValNat.eq_zero_of_not_dvd
        simp [Nat.factorial, hr.ne_one]
      rw [hval0]
      omega
    have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero r hu0
    have hcoef : 16 ≤ r - 1 := by omega
    nlinarith
  rw [hvalfac]
  omega

private theorem factorialPrimeClassPart_eight_pow_sixteen_dvd_layer_pow_seventeen
    (n : ℕ) :
    factorialPrimeClassPart n 8 1 ^ 16 ∣ eightPrimeClassLayerProduct n ^ 17 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrTpow : r ∣ factorialPrimeClassPart n 8 1 ^ 16 :=
    (dvd_pow_self r hj0).trans hrj
  have hrT : r ∣ factorialPrimeClassPart n 8 1 := hr.dvd_of_dvd_pow hrTpow
  have hrmod : r % 8 = 1 := by
    unfold factorialPrimeClassPart at hrT
    obtain ⟨s, hs, hrs⟩ := (hr.prime.dvd_finsetProd_iff
      (fun s ↦ s ^ n.factorial.factorization s)).mp hrT
    have hsdata := Finset.mem_filter.mp hs
    have hrsbase : r ∣ s := hr.dvd_of_dvd_pow hrs
    rcases (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hsdata.1)).mp hrsbase with hr1 | hrsEq
    · exact (hr.ne_one hr1).elim
    · simpa [hrsEq] using hsdata.2
  have hTfac : factorialPrimeClassPart n 8 1 ^ 16 ∣ n.factorial ^ 16 :=
    pow_dvd_pow_of_dvd (factorialPrimeClassPart_dvd_factorial n 8 1) 16
  have hrjfacpow : r ^ j ∣ n.factorial ^ 16 := hrj.trans hTfac
  have hfacpow0 : n.factorial ^ 16 ≠ 0 := pow_ne_zero _ n.factorial_ne_zero
  have hjle : j ≤ 16 * padicValNat r n.factorial := by
    have := (padicValNat_dvd_iff_le hfacpow0).mp hrjfacpow
    simpa [padicValNat.pow] using this
  have hvalbound := sixteen_mul_factorialVal_le_seventeen_mul_div hr hrmod (n := n)
  have hjdiv : j ≤ 17 * (n / r) := hjle.trans hvalbound
  have hrlayer : r ^ (n / r) ∣ eightPrimeClassLayerProduct n :=
    prime_pow_divides_eightPrimeClassLayerProduct hr hrmod
  have hrbig : r ^ (17 * (n / r)) ∣ eightPrimeClassLayerProduct n ^ 17 := by
    calc
      r ^ (17 * (n / r)) = r ^ ((n / r) * 17) := by rw [mul_comm]
      _ = (r ^ (n / r)) ^ 17 := by rw [pow_mul]
      _ ∣ eightPrimeClassLayerProduct n ^ 17 := pow_dvd_pow_of_dvd hrlayer 17
  exact (pow_dvd_pow r hjdiv).trans hrbig

/-- The integer exponent appearing in the layered modulus-eight product. -/
def eightLayerExponent (n : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (n / 17), n / s

private theorem eightPrimeClassLayerProduct_pow_seven_le (n : ℕ) :
    eightPrimeClassLayerProduct n ^ 7 ≤ 18 ^ eightLayerExponent n := by
  unfold eightPrimeClassLayerProduct eightLayerExponent
  calc
    ((Finset.Icc 1 (n / 17)).prod
        (fun s ↦ primeClassPrimorial (n / s) 8 1)) ^ 7 =
        (Finset.Icc 1 (n / 17)).prod
          (fun s ↦ primeClassPrimorial (n / s) 8 1 ^ 7) := by
      rw [Finset.prod_pow]
    _ ≤ (Finset.Icc 1 (n / 17)).prod (fun s ↦ 18 ^ (n / s)) := by
      apply Finset.prod_le_prod
      · intro s hs
        positivity
      · intro s hs
        exact primeClassPrimorial_eight_pow_seven_le (n / s)
    _ = 18 ^ ∑ s ∈ Finset.Icc 1 (n / 17), n / s :=
      Finset.prod_pow_eq_pow_sum _ _ _

private theorem factorialPrimeClassPart_eight_pow_one_hundred_twelve_le (n : ℕ) :
    factorialPrimeClassPart n 8 1 ^ 112 ≤ 18 ^ (17 * eightLayerExponent n) := by
  have hdiv := factorialPrimeClassPart_eight_pow_sixteen_dvd_layer_pow_seventeen n
  have hbase : factorialPrimeClassPart n 8 1 ^ 16 ≤
      eightPrimeClassLayerProduct n ^ 17 :=
    Nat.le_of_dvd (pow_pos (eightPrimeClassLayerProduct_pos n) 17) hdiv
  calc
    factorialPrimeClassPart n 8 1 ^ 112 =
        (factorialPrimeClassPart n 8 1 ^ 16) ^ 7 := by norm_num [← pow_mul]
    _ ≤ (eightPrimeClassLayerProduct n ^ 17) ^ 7 :=
      Nat.pow_le_pow_left hbase 7
    _ = (eightPrimeClassLayerProduct n ^ 7) ^ 17 := by
      simp only [← pow_mul]
    _ ≤ (18 ^ eightLayerExponent n) ^ 17 :=
      Nat.pow_le_pow_left (eightPrimeClassLayerProduct_pow_seven_le n) 17
    _ = 18 ^ (17 * eightLayerExponent n) := by
      rw [← pow_mul]
      congr 1
      omega

private theorem eightLayerExponent_cast_le (n : ℕ) :
    (eightLayerExponent n : ℝ) ≤
      n * (1 + Real.log (n / 17 : ℕ)) := by
  unfold eightLayerExponent
  calc
    ((∑ s ∈ Finset.Icc 1 (n / 17), n / s : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc 1 (n / 17), ((n / s : ℕ) : ℝ) := by norm_cast
    _ ≤ ∑ s ∈ Finset.Icc 1 (n / 17), (n : ℝ) / s := by
      exact Finset.sum_le_sum fun s hs ↦ Nat.cast_div_le
    _ = (n : ℝ) * ∑ s ∈ Finset.Icc 1 (n / 17), ((s : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ = (n : ℝ) * (harmonic (n / 17) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (n : ℝ) * (1 + Real.log (n / 17 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (n / 17)) (Nat.cast_nonneg n)

private theorem erdosOblath_eight_log_inequality {n : ℕ} (hn : 256 ≤ n) :
    56 * Real.log n.factorial >
      56 * Real.log 4 + 17 * eightLayerExponent n * Real.log 18 := by
  have hn0 : n ≠ 0 := by omega
  have hnreal : (256 : ℝ) ≤ n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlogn_nonneg : 0 ≤ Real.log (n : ℝ) := Real.log_natCast_nonneg n
  have hlogtwo_lo : (69 : ℝ) / 100 < Real.log 2 := by
    nlinarith [Real.log_two_gt_d9]
  have hlogtwo_hi : Real.log 2 < (7 : ℝ) / 10 := by
    nlinarith [Real.log_two_lt_d9]
  have hlogthree_hi : Real.log 3 < (11 : ℝ) / 10 := by
    nlinarith [Real.log_three_lt_d9]
  have hlogfour : Real.log 4 = 2 * Real.log 2 := by
    calc
      Real.log 4 = Real.log ((2 : ℝ) ^ 2) := by norm_num
      _ = 2 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlogeighteen : Real.log 18 = Real.log 2 + 2 * Real.log 3 := by
    calc
      Real.log 18 = Real.log ((2 : ℝ) * 3 ^ 2) := by norm_num
      _ = Real.log 2 + Real.log ((3 : ℝ) ^ 2) := by
        rw [Real.log_mul (by norm_num : (2 : ℝ) ≠ 0) (by norm_num : (3 : ℝ) ^ 2 ≠ 0)]
      _ = Real.log 2 + 2 * Real.log 3 := by rw [Real.log_pow]; norm_num
  have hlogfour_hi : Real.log 4 < (7 : ℝ) / 5 := by nlinarith
  have hlogeighteen_pos : 0 < Real.log 18 := Real.log_pos (by norm_num)
  have hlogeighteen_hi : Real.log 18 < (29 : ℝ) / 10 := by nlinarith
  have hlogtwo_pow : Real.log 256 = 8 * Real.log 2 := by
    calc
      Real.log 256 = Real.log ((2 : ℝ) ^ 8) := by norm_num
      _ = 8 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlogn_lo : 8 * Real.log 2 ≤ Real.log (n : ℝ) := by
    rw [← hlogtwo_pow]
    exact Real.log_le_log (by norm_num) hnreal
  let m := n / 17
  have hmpos : 0 < m := by
    dsimp only [m]
    omega
  have hm_le : (m : ℝ) ≤ (n : ℝ) / 16 := by
    calc
      (m : ℝ) ≤ ((n / 16 : ℕ) : ℝ) := by
        exact_mod_cast (Nat.div_le_div_left (show 16 ≤ 17 by norm_num) (by norm_num))
      _ ≤ (n : ℝ) / 16 := Nat.cast_div_le
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - 4 * Real.log 2 := by
    have hmono : Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / 16) :=
      Real.log_le_log (Nat.cast_pos.mpr hmpos) hm_le
    have hncast0 : (n : ℝ) ≠ 0 := by positivity
    calc
      Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / 16) := hmono
      _ = Real.log (n : ℝ) - Real.log 16 := by
        rw [Real.log_div hncast0 (by norm_num : (16 : ℝ) ≠ 0)]
      _ = Real.log (n : ℝ) - 4 * Real.log 2 := by
        congr 1
        calc
          Real.log 16 = Real.log ((2 : ℝ) ^ 4) := by norm_num
          _ = 4 * Real.log 2 := by rw [Real.log_pow]; norm_num
  have hlogm_crude : 1 + Real.log (m : ℝ) ≤
      Real.log (n : ℝ) - (44 : ℝ) / 25 := by
    nlinarith
  have hbracket_nonneg : 0 ≤ Real.log (n : ℝ) - (44 : ℝ) / 25 := by
    nlinarith
  have hexp := eightLayerExponent_cast_le n
  change (eightLayerExponent n : ℝ) ≤
      (n : ℝ) * (1 + Real.log (m : ℝ)) at hexp
  have hexp_crude : (eightLayerExponent n : ℝ) ≤
      (n : ℝ) * (Real.log (n : ℝ) - (44 : ℝ) / 25) :=
    hexp.trans (mul_le_mul_of_nonneg_left hlogm_crude hnnonneg)
  have hupper_term :
      17 * (eightLayerExponent n : ℝ) * Real.log 18 ≤
        ((493 : ℝ) / 10) * (n : ℝ) *
          (Real.log (n : ℝ) - (44 : ℝ) / 25) := by
    calc
      17 * (eightLayerExponent n : ℝ) * Real.log 18 ≤
          17 * ((n : ℝ) * (Real.log (n : ℝ) - (44 : ℝ) / 25)) * Real.log 18 := by
        gcongr
      _ ≤ 17 * ((n : ℝ) * (Real.log (n : ℝ) - (44 : ℝ) / 25)) *
          ((29 : ℝ) / 10) := by
        gcongr
      _ = ((493 : ℝ) / 10) * (n : ℝ) *
          (Real.log (n : ℝ) - (44 : ℝ) / 25) := by ring
  have hstirling := Stirling.le_log_factorial_stirling hn0
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlower : (n : ℝ) * (Real.log (n : ℝ) - 1) ≤ Real.log n.factorial := by
    nlinarith
  have hnumeric :
      56 * (Real.log 4) + ((493 : ℝ) / 10) * (n : ℝ) *
          (Real.log (n : ℝ) - (44 : ℝ) / 25) <
        56 * ((n : ℝ) * (Real.log (n : ℝ) - 1)) := by
    nlinarith [mul_nonneg hnnonneg hlogn_nonneg]
  calc
    56 * Real.log 4 + 17 * eightLayerExponent n * Real.log 18 ≤
        56 * Real.log 4 + ((493 : ℝ) / 10) * (n : ℝ) *
          (Real.log (n : ℝ) - (44 : ℝ) / 25) := by
      gcongr
    _ < 56 * ((n : ℝ) * (Real.log (n : ℝ) - 1)) := hnumeric
    _ ≤ 56 * Real.log n.factorial := by gcongr

private theorem zmod_four_double_pow_four (z : ZMod 4) : (z + z) ^ 4 = 0 := by
  fin_cases z <;> decide

private theorem zmod_four_odd_pow_four (z : ZMod 4) : (2 * z + 1) ^ 4 = 1 := by
  fin_cases z <;> decide

private theorem not_four_dvd_coprime_fourth_power_sum
    {X Y : ℕ} (hcop : X.Coprime Y) : ¬ 4 ∣ X ^ 4 + Y ^ 4 := by
  have hnot_both_even : ¬ (Even X ∧ Even Y) := by
    rintro ⟨hX, hY⟩
    rw [even_iff_two_dvd] at hX hY
    exact (Nat.Prime.not_coprime_iff_dvd.mpr
      ⟨2, Nat.prime_two, hX, hY⟩) hcop
  rcases Nat.even_or_odd X with hXe | hXo <;>
    rcases Nat.even_or_odd Y with hYe | hYo
  · exact (hnot_both_even ⟨hXe, hYe⟩).elim
  · rcases hXe with ⟨u, rfl⟩
    rcases hYo with ⟨v, rfl⟩
    intro h4
    have hz := (ZMod.natCast_eq_zero_iff ((u + u) ^ 4 + (2 * v + 1) ^ 4) 4).mpr h4
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] at hz
    have he : ((u : ZMod 4) + u) ^ 4 = 0 := zmod_four_double_pow_four u
    have ho : (2 * (v : ZMod 4) + 1) ^ 4 = 1 := zmod_four_odd_pow_four v
    rw [he, ho] at hz
    exact (by decide : (1 : ZMod 4) ≠ 0) hz
  · rcases hXo with ⟨u, rfl⟩
    rcases hYe with ⟨v, rfl⟩
    intro h4
    have hz := (ZMod.natCast_eq_zero_iff ((2 * u + 1) ^ 4 + (v + v) ^ 4) 4).mpr h4
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] at hz
    have ho : (2 * (u : ZMod 4) + 1) ^ 4 = 1 := zmod_four_odd_pow_four u
    have he : ((v : ZMod 4) + v) ^ 4 = 0 := zmod_four_double_pow_four v
    rw [ho, he] at hz
    exact (by decide : (1 : ZMod 4) ≠ 0) hz
  · rcases hXo with ⟨u, rfl⟩
    rcases hYo with ⟨v, rfl⟩
    intro h4
    have hz := (ZMod.natCast_eq_zero_iff
      ((2 * u + 1) ^ 4 + (2 * v + 1) ^ 4) 4).mpr h4
    simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_one, Nat.cast_ofNat, Nat.cast_pow] at hz
    have hX : (2 * (u : ZMod 4) + 1) ^ 4 = 1 := zmod_four_odd_pow_four u
    have hY : (2 * (v : ZMod 4) + 1) ^ 4 = 1 := zmod_four_odd_pow_four v
    rw [hX, hY] at hz
    exact (by decide : (2 : ZMod 4) ≠ 0) hz

/-- The `X⁴ + Y⁴` factor of a coprime eighth-power difference is
supported, apart from one factor `2`, on primes `1 mod 8`. -/
theorem fourth_power_sum_dvd_two_mul_factorialPrimeClassPart
    {X Y n : ℕ} (hcop : X.Coprime Y)
    (hfac : X ^ 4 + Y ^ 4 ∣ n.factorial) :
    X ^ 4 + Y ^ 4 ∣ 2 * factorialPrimeClassPart n 8 1 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrB : r ∣ X ^ 4 + Y ^ 4 := (dvd_pow_self r hj0).trans hrj
  by_cases hr2 : r = 2
  · subst r
    have hjle : j ≤ 1 := by
      by_contra hj
      have h4j : 2 ^ 2 ∣ 2 ^ j := pow_dvd_pow 2 (by omega)
      exact not_four_dvd_coprime_fourth_power_sum hcop (h4j.trans hrj)
    exact (pow_dvd_pow 2 hjle).trans (dvd_mul_right 2 _)
  have hrmod : r % 8 = 1 :=
    prime_mod_eight_of_dvd_coprime_fourth_power_sum hcop hr hr2 hrB
  have hrjfac : r ^ j ∣ n.factorial := hrj.trans hfac
  have hjle : j ≤ n.factorial.factorization r := by
    rw [Nat.factorization_def n.factorial hr]
    exact (padicValNat_dvd_iff_le n.factorial_ne_zero).mp hrjfac
  have hrmem : r ∈ n.factorial.factorization.support.filter (fun r ↦ r % 8 = 1) := by
    simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq]
    refine ⟨?_, hrmod⟩
    rw [Nat.factorization_def n.factorial hr]
    have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
    have hjle' : j ≤ padicValNat r n.factorial :=
      (padicValNat_dvd_iff_le n.factorial_ne_zero).mp hrjfac
    exact ne_of_gt (lt_of_lt_of_le hjpos hjle')
  have hterm : r ^ n.factorial.factorization r ∣ factorialPrimeClassPart n 8 1 := by
    exact Finset.dvd_prod_of_mem (fun r ↦ r ^ n.factorial.factorization r) hrmem
  exact (pow_dvd_pow r hjle).trans (hterm.trans (dvd_mul_left _ 2))

/-- Erdős--Obláth's exponent-eight obstruction in the range needed for
Problem 405.  The application has `n = p - 1 ≥ 256`. -/
theorem erdosOblath_eighth_large {X Y n : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y) (hn : 256 ≤ n) :
    X ^ 8 - Y ^ 8 ≠ n.factorial := by
  intro heq
  have hpowlt : Y ^ 8 < X ^ 8 := by
    apply Nat.sub_pos_iff_lt.mp
    rw [heq]
    exact n.factorial_pos
  have hYX : Y < X :=
    (pow_lt_pow_iff_left₀ (Nat.zero_le Y) (Nat.zero_le X) (by norm_num : 8 ≠ 0)).mp hpowlt
  have h4le : Y ^ 4 ≤ X ^ 4 := Nat.pow_le_pow_left hYX.le 4
  have hfactor_identity :
      X ^ 8 - Y ^ 8 = (X ^ 4 - Y ^ 4) * (X ^ 4 + Y ^ 4) := by
    have hXpow : X ^ 8 = (X ^ 4) ^ 2 := by ring
    have hYpow : Y ^ 8 = (Y ^ 4) ^ 2 := by ring
    rw [hXpow, hYpow]
    let A := X ^ 4
    let B := Y ^ 4
    let C := A - B
    change A ^ 2 - B ^ 2 = C * (A + B)
    have hBA : B ≤ A := by simpa [A, B] using h4le
    have hCA : C + B = A := by
      dsimp only [C]
      exact Nat.sub_add_cancel hBA
    apply (Nat.sub_eq_iff_eq_add (Nat.pow_le_pow_left hBA 2)).mpr
    calc
      A ^ 2 = (C + B) ^ 2 := by rw [hCA]
      _ = C * (A + B) + B ^ 2 := by rw [← hCA]; ring
  have hfactor : n.factorial = (X ^ 4 - Y ^ 4) * (X ^ 4 + Y ^ 4) := by
    rw [← heq, hfactor_identity]
  have hsum_dvd : X ^ 4 + Y ^ 4 ∣ n.factorial := by
    refine ⟨X ^ 4 - Y ^ 4, ?_⟩
    rw [mul_comm]
    exact hfactor
  have hsum_class : X ^ 4 + Y ^ 4 ∣
      2 * factorialPrimeClassPart n 8 1 :=
    fourth_power_sum_dvd_two_mul_factorialPrimeClassPart hcop hsum_dvd
  have hsum_le : X ^ 4 + Y ^ 4 ≤ 2 * factorialPrimeClassPart n 8 1 :=
    Nat.le_of_dvd
      (mul_pos (by norm_num) (factorialPrimeClassPart_pos n 8 1)) hsum_class
  have hY4pos : 0 < Y ^ 4 := pow_pos hY 4
  have hdiff_lt_sum : X ^ 4 - Y ^ 4 < X ^ 4 + Y ^ 4 := by
    have hdiffle : X ^ 4 - Y ^ 4 ≤ X ^ 4 := Nat.sub_le _ _
    omega
  have hfac_lt_sum_sq : n.factorial < (X ^ 4 + Y ^ 4) ^ 2 := by
    rw [hfactor, pow_two]
    exact Nat.mul_lt_mul_of_pos_right hdiff_lt_sum
      (add_pos_of_pos_of_nonneg (pow_pos hX 4) (Nat.zero_le _))
  have hfac_lt_class : n.factorial < 4 * factorialPrimeClassPart n 8 1 ^ 2 := by
    calc
      n.factorial < (X ^ 4 + Y ^ 4) ^ 2 := hfac_lt_sum_sq
      _ ≤ (2 * factorialPrimeClassPart n 8 1) ^ 2 :=
        Nat.pow_le_pow_left hsum_le 2
      _ = 4 * factorialPrimeClassPart n 8 1 ^ 2 := by ring
  have hpow56 : n.factorial ^ 56 <
      4 ^ 56 * factorialPrimeClassPart n 8 1 ^ 112 := by
    calc
      n.factorial ^ 56 < (4 * factorialPrimeClassPart n 8 1 ^ 2) ^ 56 :=
        (pow_lt_pow_iff_left₀ (Nat.zero_le _) (Nat.zero_le _) (by norm_num : 56 ≠ 0)).mpr
          hfac_lt_class
      _ = 4 ^ 56 * factorialPrimeClassPart n 8 1 ^ 112 := by
        rw [mul_pow, ← pow_mul]
  have hclass := factorialPrimeClassPart_eight_pow_one_hundred_twelve_le n
  have hnat : n.factorial ^ 56 < 4 ^ 56 * 18 ^ (17 * eightLayerExponent n) :=
    hpow56.trans_le (Nat.mul_le_mul_left _ hclass)
  have hreal : (n.factorial : ℝ) ^ 56 <
      (4 : ℝ) ^ 56 * (18 : ℝ) ^ (17 * eightLayerExponent n) := by
    exact_mod_cast hnat
  have hlog := Real.log_lt_log (by positivity : (0 : ℝ) < (n.factorial : ℝ) ^ 56) hreal
  rw [Real.log_pow] at hlog
  rw [Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow] at hlog
  norm_num at hlog
  push_cast at hlog
  have hreverse := erdosOblath_eight_log_inequality hn
  exact (not_lt_of_ge hreverse.le) hlog

/-! ### The odd-prime-exponent estimate -/

private theorem factorial_dvd_modulus_pow_mul_progression {a : ℕ}
    (ha : 1 < a) (m : ℕ) :
    m.factorial ∣ a ^ m * arithmeticProgressionProduct a (a + 1) m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  have hjle : j ≤ padicValNat r m.factorial :=
    (padicValNat_dvd_iff_le m.factorial_ne_zero).mp hrj
  have hjm : j ≤ m := hjle.trans (padicValNat_factorial_le r m)
  by_cases hra : r ∣ a
  · have hrjaj : r ^ j ∣ a ^ j := pow_dvd_pow_of_dvd hra j
    have haja : a ^ j ∣ a ^ m := pow_dvd_pow a hjm
    exact (hrjaj.trans haja).trans (dvd_mul_right _ _)
  · have hval := padicValNat_factorial_le_arithmeticProgressionProduct
      hr hra m (b := a + 1) (by omega) (Nat.coprime_self_add_right.mpr (by simp))
    have hap0 : arithmeticProgressionProduct a (a + 1) m ≠ 0 :=
      arithmeticProgressionProduct_ne_zero (by omega)
    have hrjap : r ^ j ∣ arithmeticProgressionProduct a (a + 1) m :=
      (padicValNat_dvd_iff_le hap0).mpr (hjle.trans hval)
    exact hrjap.trans (dvd_mul_left _ _)

/-- The corrected progression quotient for a general modulus. -/
def modulusProgressionQuotient (a m : ℕ) : ℕ :=
  (a ^ m * arithmeticProgressionProduct a (a + 1) m) / m.factorial

private theorem factorial_mul_modulusProgressionQuotient {a : ℕ}
    (ha : 1 < a) (m : ℕ) :
    m.factorial * modulusProgressionQuotient a m =
      a ^ m * arithmeticProgressionProduct a (a + 1) m := by
  exact Nat.mul_div_cancel' (factorial_dvd_modulus_pow_mul_progression ha m)

private theorem modulusProgressionQuotient_pos {a : ℕ} (ha : 1 < a) (m : ℕ) :
    0 < modulusProgressionQuotient a m := by
  have hright : 0 < a ^ m * arithmeticProgressionProduct a (a + 1) m :=
    mul_pos (pow_pos (by omega) m)
      (Nat.pos_of_ne_zero (arithmeticProgressionProduct_ne_zero (by omega)))
  have heq := factorial_mul_modulusProgressionQuotient ha m
  by_contra hzero
  have hq0 := Nat.eq_zero_of_not_pos hzero
  rw [hq0, mul_zero] at heq
  omega

private theorem modulusProgressionQuotient_le {a : ℕ} (ha : 1 < a) (m : ℕ) :
    modulusProgressionQuotient a m ≤ (a * (a + 1)) ^ m := by
  have hmul : m.factorial * modulusProgressionQuotient a m ≤
      m.factorial * (a * (a + 1)) ^ m := by
    rw [factorial_mul_modulusProgressionQuotient ha]
    calc
      a ^ m * arithmeticProgressionProduct a (a + 1) m ≤
          a ^ m * ((a + 1) ^ m * m.factorial) :=
        Nat.mul_le_mul_left _ (arithmeticProgressionProduct_self_succ_le a m)
      _ = m.factorial * (a * (a + 1)) ^ m := by
        rw [mul_pow]
        ac_rfl
  exact Nat.le_of_mul_le_mul_left hmul m.factorial_pos

private theorem primeClassPrimorial_modulus_dvd_step {a n : ℕ} (ha : 1 < a) :
    primeClassPrimorial n a 1 ∣
      primeClassPrimorial ((n - 1) / a) a 1 *
        modulusProgressionQuotient a ((n - 1) / a) := by
  let m := (n - 1) / a
  let S := (Finset.range (n + 1)).filter (fun r ↦ r.Prime ∧ r % a = 1)
  change S.prod id ∣ primeClassPrimorial m a 1 * modulusProgressionQuotient a m
  have htarget_pos : 0 < primeClassPrimorial m a 1 * modulusProgressionQuotient a m :=
    mul_pos (primeClassPrimorial_pos _ _ _) (modulusProgressionQuotient_pos ha _)
  refine (Finset.prod_dvd_prod_of_subset S
    (primeClassPrimorial m a 1 * modulusProgressionQuotient a m).primeFactors id ?_).trans
      (Nat.prod_primeFactors_dvd _)
  intro r hrS
  apply Nat.mem_primeFactors.mpr
  have hrmem := Finset.mem_filter.mp hrS
  have hrlt : r < n + 1 := Finset.mem_range.mp hrmem.1
  have hrle : r ≤ n := by omega
  have hrp : r.Prime := hrmem.2.1
  have hrmod : r % a = 1 := hrmem.2.2
  refine ⟨hrp, ?_, htarget_pos.ne'⟩
  by_cases hrm : r ≤ m
  · have hrold : r ∈ (Finset.range (m + 1)).filter (fun r ↦ r.Prime ∧ r % a = 1) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hrp, hrmod⟩
    exact (Finset.dvd_prod_of_mem id hrold).trans (dvd_mul_right _ _)
  · have hmr : m < r := Nat.lt_of_not_ge hrm
    have hrform : r = a * (r / a) + 1 := by
      have hdecomp := Nat.mod_add_div r a
      omega
    have hri : 0 < r / a := by
      by_contra hzero
      have hdiv0 := Nat.eq_zero_of_not_pos hzero
      rw [hdiv0, mul_zero, zero_add] at hrform
      exact hrp.ne_one hrform
    have hrdiv_le : r / a ≤ m := by
      apply (Nat.le_div_iff_mul_le (by omega : 0 < a)).mpr
      have hmul : a * (r / a) ≤ n - 1 := by omega
      simpa [Nat.mul_comm] using hmul
    let i := r / a - 1
    have hi : i < m := by
      dsimp only [i]
      omega
    have hterm : a * i + (a + 1) = r := by
      dsimp only [i]
      have hi_eq : i + 1 = r / a := by omega
      calc
        a * i + (a + 1) = a * (i + 1) + 1 := by ring
        _ = a * (r / a) + 1 := by rw [hi_eq]
        _ = r := hrform.symm
    have hrAP : r ∣ arithmeticProgressionProduct a (a + 1) m := by
      unfold arithmeticProgressionProduct
      have himem : i ∈ Finset.range m := Finset.mem_range.mpr hi
      have hdvdterm : r ∣ a * i + (a + 1) := by rw [hterm]
      exact hdvdterm.trans (Finset.dvd_prod_of_mem (fun i ↦ a * i + (a + 1)) himem)
    have hrfac : r.Coprime m.factorial := hrp.coprime_factorial_of_lt hmr
    have hrmul : r ∣ m.factorial * modulusProgressionQuotient a m := by
      rw [factorial_mul_modulusProgressionQuotient ha]
      exact hrAP.trans (dvd_mul_left _ _)
    have hrquot : r ∣ modulusProgressionQuotient a m := hrfac.dvd_mul_left.mp hrmul
    exact hrquot.trans (dvd_mul_left _ _)

private theorem primeClassPrimorial_modulus_step_le {a n : ℕ} (ha : 1 < a) :
    primeClassPrimorial n a 1 ≤
      primeClassPrimorial ((n - 1) / a) a 1 *
        modulusProgressionQuotient a ((n - 1) / a) :=
  Nat.le_of_dvd
    (mul_pos (primeClassPrimorial_pos _ _ _) (modulusProgressionQuotient_pos ha _))
    (primeClassPrimorial_modulus_dvd_step ha)

theorem primeClassPrimorial_modulus_pow_pred_le {a n : ℕ} (ha : 1 < a) :
    primeClassPrimorial n a 1 ^ (a - 1) ≤ (a * (a + 1)) ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hfilter : (Finset.range (0 + 1)).filter
            (fun r ↦ r.Prime ∧ r % a = 1) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          intro hr
          have hr0 : r = 0 := by omega
          subst r
          exact Nat.not_prime_zero hr.2.1
        unfold primeClassPrimorial
        rw [hfilter]
        simp
      let m := (n - 1) / a
      have hm_lt : m < n := by
        change (n - 1) / a < n
        calc
          (n - 1) / a ≤ n - 1 := Nat.div_le_self _ _
          _ < n := Nat.sub_lt (Nat.pos_of_ne_zero hn0) (by omega)
      have ham : a * m ≤ n := by
        dsimp only [m]
        exact (Nat.mul_div_le (n - 1) a).trans (Nat.sub_le n 1)
      let B := a * (a + 1)
      calc
        primeClassPrimorial n a 1 ^ (a - 1) ≤
            (primeClassPrimorial m a 1 * modulusProgressionQuotient a m) ^ (a - 1) :=
          Nat.pow_le_pow_left (by simpa [m] using primeClassPrimorial_modulus_step_le ha (n := n)) _
        _ = primeClassPrimorial m a 1 ^ (a - 1) *
            modulusProgressionQuotient a m ^ (a - 1) := mul_pow _ _ _
        _ ≤ B ^ m * (B ^ m) ^ (a - 1) :=
          Nat.mul_le_mul (by simpa [B] using ih m hm_lt)
            (Nat.pow_le_pow_left (by simpa [B] using modulusProgressionQuotient_le ha m) _)
        _ = B ^ (m * a) := by
          rw [← pow_mul, ← pow_add]
          congr 1
          nth_rewrite 1 [← Nat.mul_one m]
          rw [← Nat.mul_add]
          congr 1
          omega
        _ = B ^ (a * m) := by rw [Nat.mul_comm]
        _ ≤ B ^ n := Nat.pow_le_pow_right (mul_pos ha.bot_lt (by omega)) ham
        _ = (a * (a + 1)) ^ n := by rfl

/-- Product of the squarefree `1 mod a` prime layers that occur in `n!`. -/
def modulusPrimeClassLayerProduct (a n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / (a + 1))).prod
    (fun s ↦ primeClassPrimorial (n / s) a 1)

private theorem modulusPrimeClassLayerProduct_pos (a n : ℕ) :
    0 < modulusPrimeClassLayerProduct a n := by
  exact Finset.prod_pos fun s hs ↦ primeClassPrimorial_pos _ _ _

private theorem modulus_add_one_le_of_prime_mod_one {a r : ℕ}
    (ha : 1 < a) (hr : r.Prime) (hrmod : r % a = 1) : a + 1 ≤ r := by
  by_contra hlt
  have hrle : r ≤ a := by omega
  by_cases hra : r = a
  · subst r
    simp at hrmod
  · have hrlt : r < a := lt_of_le_of_ne hrle hra
    rw [Nat.mod_eq_of_lt hrlt] at hrmod
    exact hr.ne_one hrmod

private theorem prime_pow_divides_modulusPrimeClassLayerProduct
    {a r n : ℕ} (ha : 1 < a) (hr : r.Prime) (hrmod : r % a = 1) :
    r ^ (n / r) ∣ modulusPrimeClassLayerProduct a n := by
  let u := n / r
  have hrmin : a + 1 ≤ r := modulus_add_one_le_of_prime_mod_one ha hr hrmod
  have hu_bound : u ≤ n / (a + 1) := Nat.div_le_div_left hrmin (by omega)
  have hsubset : Finset.Icc 1 u ⊆ Finset.Icc 1 (n / (a + 1)) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
      (Finset.mem_Icc.mp hs).2.trans hu_bound⟩
  have hpoint : ∀ s ∈ Finset.Icc 1 u,
      r ∣ primeClassPrimorial (n / s) a 1 := by
    intro s hs
    have hsdata := Finset.mem_Icc.mp hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsdata.1
    have hrsn : r * s ≤ n := by
      have hu_mul : r * u ≤ n := Nat.mul_div_le n r
      exact (Nat.mul_le_mul_left r hsdata.2).trans hu_mul
    have hrle : r ≤ n / s := (Nat.le_div_iff_mul_le hspos).mpr hrsn
    unfold primeClassPrimorial
    apply Finset.dvd_prod_of_mem id
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hr, hrmod⟩
  calc
    r ^ u = (Finset.Icc 1 u).prod (fun _ ↦ r) := by simp
    _ ∣ (Finset.Icc 1 u).prod (fun s ↦ primeClassPrimorial (n / s) a 1) :=
      Finset.prod_dvd_prod_of_dvd _ _ hpoint
    _ ∣ (Finset.Icc 1 (n / (a + 1))).prod
        (fun s ↦ primeClassPrimorial (n / s) a 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsubset

private theorem modulus_mul_factorialVal_le_succ_mul_div
    {a r n : ℕ} (ha : 1 < a) (hr : r.Prime) (hrmod : r % a = 1) :
    a * padicValNat r n.factorial ≤ (a + 1) * (n / r) := by
  let _ : Fact r.Prime := ⟨hr⟩
  let u := n / r
  have hrmin : a + 1 ≤ r := modulus_add_one_le_of_prime_mod_one ha hr hrmod
  have hvalfac : padicValNat r n.factorial = padicValNat r u.factorial + u := by
    calc
      padicValNat r n.factorial = padicValNat r (r * u).factorial := by
        simpa [u] using (padicValNat_mul_div_factorial (p := r) n).symm
      _ = padicValNat r u.factorial + u := padicValNat_factorial_mul u
  have htail : a * padicValNat r u.factorial ≤ u := by
    by_cases hu0 : u = 0
    · have hval0 : padicValNat r u.factorial = 0 := by
        rw [hu0]
        apply padicValNat.eq_zero_of_not_dvd
        simp [Nat.factorial, hr.ne_one]
      rw [hval0]
      omega
    have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero r hu0
    have hcoef : a ≤ r - 1 := by omega
    nlinarith
  rw [hvalfac]
  change a * (padicValNat r u.factorial + u) ≤ (a + 1) * u
  rw [Nat.mul_add, Nat.add_mul]
  omega

private theorem factorialPrimeClassPart_modulus_pow_dvd_layer_pow_succ
    {a : ℕ} (ha : 1 < a) (n : ℕ) :
    factorialPrimeClassPart n a 1 ^ a ∣
      modulusPrimeClassLayerProduct a n ^ (a + 1) := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrTpow : r ∣ factorialPrimeClassPart n a 1 ^ a :=
    (dvd_pow_self r hj0).trans hrj
  have hrT : r ∣ factorialPrimeClassPart n a 1 := hr.dvd_of_dvd_pow hrTpow
  have hrmod : r % a = 1 := by
    unfold factorialPrimeClassPart at hrT
    obtain ⟨s, hs, hrs⟩ := (hr.prime.dvd_finsetProd_iff
      (fun s ↦ s ^ n.factorial.factorization s)).mp hrT
    have hsdata := Finset.mem_filter.mp hs
    have hrsbase : r ∣ s := hr.dvd_of_dvd_pow hrs
    rcases (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hsdata.1)).mp hrsbase with hr1 | hrsEq
    · exact (hr.ne_one hr1).elim
    · simpa [hrsEq] using hsdata.2
  have hTfac : factorialPrimeClassPart n a 1 ^ a ∣ n.factorial ^ a :=
    pow_dvd_pow_of_dvd (factorialPrimeClassPart_dvd_factorial n a 1) a
  have hrjfacpow : r ^ j ∣ n.factorial ^ a := hrj.trans hTfac
  have hfacpow0 : n.factorial ^ a ≠ 0 := pow_ne_zero _ n.factorial_ne_zero
  have hjle : j ≤ a * padicValNat r n.factorial := by
    have hval := (padicValNat_dvd_iff_le hfacpow0).mp hrjfacpow
    simpa [padicValNat.pow] using hval
  have hvalbound := modulus_mul_factorialVal_le_succ_mul_div ha hr hrmod (n := n)
  have hjdiv : j ≤ (a + 1) * (n / r) := hjle.trans hvalbound
  have hrlayer : r ^ (n / r) ∣ modulusPrimeClassLayerProduct a n :=
    prime_pow_divides_modulusPrimeClassLayerProduct ha hr hrmod
  have hrbig : r ^ ((a + 1) * (n / r)) ∣
      modulusPrimeClassLayerProduct a n ^ (a + 1) := by
    calc
      r ^ ((a + 1) * (n / r)) = r ^ ((n / r) * (a + 1)) := by rw [mul_comm]
      _ = (r ^ (n / r)) ^ (a + 1) := by rw [pow_mul]
      _ ∣ modulusPrimeClassLayerProduct a n ^ (a + 1) :=
        pow_dvd_pow_of_dvd hrlayer (a + 1)
  exact (pow_dvd_pow r hjdiv).trans hrbig

/-- The integer exponent appearing in the layered `1 mod a` product. -/
def modulusLayerExponent (a n : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (n / (a + 1)), n / s

private theorem modulusPrimeClassLayerProduct_pow_pred_le
    {a : ℕ} (ha : 1 < a) (n : ℕ) :
    modulusPrimeClassLayerProduct a n ^ (a - 1) ≤
      (a * (a + 1)) ^ modulusLayerExponent a n := by
  unfold modulusPrimeClassLayerProduct modulusLayerExponent
  calc
    ((Finset.Icc 1 (n / (a + 1))).prod
        (fun s ↦ primeClassPrimorial (n / s) a 1)) ^ (a - 1) =
        (Finset.Icc 1 (n / (a + 1))).prod
          (fun s ↦ primeClassPrimorial (n / s) a 1 ^ (a - 1)) := by
      rw [Finset.prod_pow]
    _ ≤ (Finset.Icc 1 (n / (a + 1))).prod
        (fun s ↦ (a * (a + 1)) ^ (n / s)) := by
      apply Finset.prod_le_prod
      · intro s hs
        positivity
      · intro s hs
        exact primeClassPrimorial_modulus_pow_pred_le ha
    _ = (a * (a + 1)) ^ ∑ s ∈ Finset.Icc 1 (n / (a + 1)), n / s :=
      Finset.prod_pow_eq_pow_sum _ _ _

private theorem factorialPrimeClassPart_modulus_pow_product_le
    {a : ℕ} (ha : 1 < a) (n : ℕ) :
    factorialPrimeClassPart n a 1 ^ (a * (a - 1)) ≤
      (a * (a + 1)) ^ ((a + 1) * modulusLayerExponent a n) := by
  have hdiv := factorialPrimeClassPart_modulus_pow_dvd_layer_pow_succ ha n
  have hbase : factorialPrimeClassPart n a 1 ^ a ≤
      modulusPrimeClassLayerProduct a n ^ (a + 1) :=
    Nat.le_of_dvd (pow_pos (modulusPrimeClassLayerProduct_pos a n) (a + 1)) hdiv
  calc
    factorialPrimeClassPart n a 1 ^ (a * (a - 1)) =
        (factorialPrimeClassPart n a 1 ^ a) ^ (a - 1) := by rw [pow_mul]
    _ ≤ (modulusPrimeClassLayerProduct a n ^ (a + 1)) ^ (a - 1) :=
      Nat.pow_le_pow_left hbase (a - 1)
    _ = (modulusPrimeClassLayerProduct a n ^ (a - 1)) ^ (a + 1) := by
      simp only [← pow_mul]
      rw [Nat.mul_comm (a + 1) (a - 1)]
    _ ≤ ((a * (a + 1)) ^ modulusLayerExponent a n) ^ (a + 1) :=
      Nat.pow_le_pow_left (modulusPrimeClassLayerProduct_pow_pred_le ha n) (a + 1)
    _ = (a * (a + 1)) ^ ((a + 1) * modulusLayerExponent a n) := by
      rw [← pow_mul]
      rw [Nat.mul_comm (modulusLayerExponent a n) (a + 1)]

private theorem modulusLayerExponent_cast_le (a n : ℕ) :
    (modulusLayerExponent a n : ℝ) ≤
      n * (1 + Real.log (n / (a + 1) : ℕ)) := by
  unfold modulusLayerExponent
  calc
    ((∑ s ∈ Finset.Icc 1 (n / (a + 1)), n / s : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc 1 (n / (a + 1)), ((n / s : ℕ) : ℝ) := by norm_cast
    _ ≤ ∑ s ∈ Finset.Icc 1 (n / (a + 1)), (n : ℝ) / s := by
      exact Finset.sum_le_sum fun s hs ↦ Nat.cast_div_le
    _ = (n : ℝ) * ∑ s ∈ Finset.Icc 1 (n / (a + 1)), ((s : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ = (n : ℝ) * (harmonic (n / (a + 1)) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (n : ℝ) * (1 + Real.log (n / (a + 1) : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (n / (a + 1)))
        (Nat.cast_nonneg n)

/-! ### The homogeneous cyclotomic factor -/

/-- The homogeneous geometric factor `(X^q - Y^q) / (X - Y)`. -/
def primeCyclotomicFactor (q X Y : ℕ) : ℕ :=
  ∑ i ∈ Finset.range q, X ^ i * Y ^ (q - 1 - i)

private theorem primeCyclotomicFactor_mul_sub {q X Y : ℕ} (hYX : Y ≤ X) :
    primeCyclotomicFactor q X Y * (X - Y) = X ^ q - Y ^ q := by
  exact geom_sum₂_mul_of_ge hYX q

private theorem primeCyclotomicFactor_pos {q X Y : ℕ}
    (hq : 0 < q) (hX : 0 < X) : 0 < primeCyclotomicFactor q X Y := by
  unfold primeCyclotomicFactor
  have hmem : q - 1 ∈ Finset.range q := Finset.mem_range.mpr (by omega)
  have hterm : 0 < X ^ (q - 1) * Y ^ (q - 1 - (q - 1)) := by
    simp only [Nat.sub_self, pow_zero, mul_one]
    positivity
  exact lt_of_lt_of_le hterm
    (Finset.single_le_sum (f := fun i ↦ X ^ i * Y ^ (q - 1 - i))
      (fun i hi ↦ Nat.zero_le _) hmem)

private theorem sub_sq_le_primeCyclotomicFactor {q X Y : ℕ}
    (hq : q.Prime) (hqodd : Odd q) (hX : 0 < X) :
    (X - Y) ^ 2 ≤ primeCyclotomicFactor q X Y := by
  have hq3 : 3 ≤ q := by
    have hq2 := hq.two_le
    by_contra h
    have hqeq : q = 2 := by omega
    subst q
    norm_num at hqodd
  calc
    (X - Y) ^ 2 ≤ X ^ 2 := Nat.pow_le_pow_left (Nat.sub_le X Y) 2
    _ ≤ X ^ (q - 1) := Nat.pow_le_pow_right hX (by omega)
    _ = X ^ (q - 1) * Y ^ (q - 1 - (q - 1)) := by simp
    _ ≤ primeCyclotomicFactor q X Y := by
      unfold primeCyclotomicFactor
      exact Finset.single_le_sum (f := fun i ↦ X ^ i * Y ^ (q - 1 - i))
        (fun i hi ↦ Nat.zero_le _)
        (Finset.mem_range.mpr (by omega))

private theorem prime_dvd_primeCyclotomicFactor_class
    {q r X Y : ℕ} (hq : q.Prime) (hqodd : Odd q) (hr : r.Prime)
    (hYX : Y < X) (hcop : X.Coprime Y)
    (hrB : r ∣ primeCyclotomicFactor q X Y) :
    r = q ∨ r % (2 * q) = 1 := by
  let _ : Fact q.Prime := ⟨hq⟩
  let _ : Fact r.Prime := ⟨hr⟩
  have hfactor := primeCyclotomicFactor_mul_sub (q := q) hYX.le
  have hrD : r ∣ X ^ q - Y ^ q := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_left hrB _
  have hYpow_le : Y ^ q ≤ X ^ q := Nat.pow_le_pow_left hYX.le q
  have hrY : ¬ r ∣ Y := by
    intro hrY
    have hrYpow : r ∣ Y ^ q := dvd_pow hrY (by exact hq.ne_zero)
    have hrXpow : r ∣ X ^ q := by
      have hadd := dvd_add hrD hrYpow
      simpa [Nat.sub_add_cancel hYpow_le] using hadd
    have hrX : r ∣ X := hr.dvd_of_dvd_pow hrXpow
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrX hrY)
  have hrX : ¬ r ∣ X := by
    intro hrX
    have hrXpow : r ∣ X ^ q := dvd_pow hrX (by exact hq.ne_zero)
    have hrYpow : r ∣ Y ^ q := by
      have hsub := Nat.dvd_sub hrXpow hrD
      simpa [Nat.sub_sub_self hYpow_le] using hsub
    have hrY' : r ∣ Y := hr.dvd_of_dvd_pow hrYpow
    exact hr.ne_one (Nat.eq_one_of_dvd_coprimes hcop hrX hrY')
  by_cases hrq : r = q
  · exact Or.inl hrq
  right
  let x : ZMod r := X
  let y : ZMod r := Y
  let z : ZMod r := x / y
  have hx : x ≠ 0 := by
    dsimp only [x]
    exact mt (ZMod.natCast_eq_zero_iff X r).mp hrX
  have hy : y ≠ 0 := by
    dsimp only [y]
    exact mt (ZMod.natCast_eq_zero_iff Y r).mp hrY
  have hz : z ≠ 0 := div_ne_zero hx hy
  have hBzero : (primeCyclotomicFactor q X Y : ZMod r) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hrB
  unfold primeCyclotomicFactor at hBzero
  push_cast at hBzero
  have hhom : y ^ (q - 1) * (∑ i ∈ Finset.range q, z ^ i) =
      ∑ i ∈ Finset.range q, x ^ i * y ^ (q - 1 - i) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i ≤ q - 1 := by
      have := Finset.mem_range.mp hi
      omega
    dsimp only [z]
    rw [div_pow]
    rw [pow_sub₀ y hy hiq]
    dsimp only [x, y]
    ring
  have hsum : (∑ i ∈ Finset.range q, z ^ i) = 0 := by
    have hzero : y ^ (q - 1) * (∑ i ∈ Finset.range q, z ^ i) = 0 := by
      rw [hhom]
      exact hBzero
    exact (mul_eq_zero.mp hzero).resolve_left (pow_ne_zero _ hy)
  have hzpow : z ^ q = 1 := by
    have hgeom := geom_sum_mul z q
    rw [hsum, zero_mul] at hgeom
    exact sub_eq_zero.mp hgeom.symm
  have hzne : z ≠ 1 := by
    intro hz1
    have hqzero : (q : ZMod r) = 0 := by
      simpa [hz1] using hsum
    have hrqdvd : r ∣ q := (ZMod.natCast_eq_zero_iff q r).mp hqzero
    rcases (Nat.dvd_prime hq).mp hrqdvd with hr1 | hrq'
    · exact hr.ne_one hr1
    · exact hrq hrq'
  have horder : orderOf z = q := orderOf_eq_prime hzpow hzne
  have hqdvd : q ∣ r - 1 := by
    have horddvd := ZMod.orderOf_dvd_card_sub_one hz
    rwa [horder] at horddvd
  have hrne2 : r ≠ 2 := by
    intro hr2
    subst r
    norm_num at hqdvd
    exact hq.ne_one hqdvd
  have hreven : 2 ∣ r - 1 := by
    rcases hr.odd_of_ne_two hrne2 with ⟨s, hs⟩
    use s
    omega
  have htwoq : 2 * q ∣ r - 1 :=
    hqodd.coprime_two_left.mul_dvd_of_dvd_of_dvd hreven hqdvd
  have hmodEq : r ≡ 1 [MOD 2 * q] :=
    ((Nat.modEq_iff_dvd' (by exact hr.one_le)).mpr htwoq).symm
  exact Nat.mod_eq_of_modEq hmodEq (by have := hq.two_le; omega)

private theorem prime_dvd_sub_of_dvd_primeCyclotomicFactor
    {q X Y : ℕ} (hq : q.Prime) (hYX : Y < X)
    (hqB : q ∣ primeCyclotomicFactor q X Y) : q ∣ X - Y := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hfactor := primeCyclotomicFactor_mul_sub (q := q) hYX.le
  have hqD : q ∣ X ^ q - Y ^ q := by
    rw [← hfactor]
    exact dvd_mul_of_dvd_left hqB _
  have hpowle : Y ^ q ≤ X ^ q := Nat.pow_le_pow_left hYX.le q
  have hDzero : ((X ^ q - Y ^ q : ℕ) : ZMod q) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hqD
  have hsubzero : ((X - Y : ℕ) : ZMod q) = 0 := by
    simp only [Nat.cast_sub hpowle, Nat.cast_pow, ZMod.pow_card] at hDzero
    simpa [Nat.cast_sub hYX.le] using hDzero
  exact (ZMod.natCast_eq_zero_iff _ _).mp hsubzero

private theorem padicValNat_primeCyclotomicFactor_eq_one
    {q X Y : ℕ} (hq : q.Prime) (hqodd : Odd q) (hYX : Y < X)
    (hcop : X.Coprime Y) (hqB : q ∣ primeCyclotomicFactor q X Y) :
    padicValNat q (primeCyclotomicFactor q X Y) = 1 := by
  let _ : Fact q.Prime := ⟨hq⟩
  have hqsub : q ∣ X - Y :=
    prime_dvd_sub_of_dvd_primeCyclotomicFactor hq hYX hqB
  have hqX : ¬ q ∣ X := by
    intro hqX
    have hqY : q ∣ Y := by
      have hsub := Nat.dvd_sub hqX hqsub
      simpa [Nat.sub_sub_self hYX.le] using hsub
    exact hq.ne_one (Nat.eq_one_of_dvd_coprimes hcop hqX hqY)
  have hvalD := padicValNat.pow_sub_pow hqodd hYX hqsub hqX hq.ne_zero
  have hXpos : 0 < X := by omega
  have hBpos := primeCyclotomicFactor_pos (X := X) (Y := Y) hq.pos hXpos
  have hsubpos : 0 < X - Y := Nat.sub_pos_of_lt hYX
  have hfactor := primeCyclotomicFactor_mul_sub (q := q) hYX.le
  have hvalfactor : padicValNat q (X ^ q - Y ^ q) =
      padicValNat q (primeCyclotomicFactor q X Y) + padicValNat q (X - Y) := by
    rw [← hfactor]
    exact padicValNat.mul hBpos.ne' hsubpos.ne'
  rw [hvalfactor, padicValNat.self hq.one_lt] at hvalD
  omega

/-- The cyclotomic factor is supported, apart from one factor `q`, on the
full `1 mod 2q` part of `n!`. -/
private theorem primeCyclotomicFactor_dvd_prime_mul_factorialPrimeClassPart
    {q X Y n : ℕ} (hq : q.Prime) (hqodd : Odd q) (hYX : Y < X)
    (hcop : X.Coprime Y) (hfac : primeCyclotomicFactor q X Y ∣ n.factorial) :
    primeCyclotomicFactor q X Y ∣
      q * factorialPrimeClassPart n (2 * q) 1 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrB : r ∣ primeCyclotomicFactor q X Y := (dvd_pow_self r hj0).trans hrj
  rcases prime_dvd_primeCyclotomicFactor_class hq hqodd hr hYX hcop hrB with hrq | hrmod
  · subst r
    let _ : Fact q.Prime := ⟨hq⟩
    have hXpos : 0 < X := by omega
    have hB0 : primeCyclotomicFactor q X Y ≠ 0 :=
      (primeCyclotomicFactor_pos (X := X) (Y := Y) hq.pos hXpos).ne'
    have hjle : j ≤ 1 := by
      have hvalle := (padicValNat_dvd_iff_le hB0).mp hrj
      rw [padicValNat_primeCyclotomicFactor_eq_one hq hqodd hYX hcop hrB] at hvalle
      exact hvalle
    exact (pow_dvd_pow q hjle).trans (by simpa using
      (dvd_mul_right q (factorialPrimeClassPart n (2 * q) 1)))
  · have hrjfac : r ^ j ∣ n.factorial := hrj.trans hfac
    have hjle : j ≤ n.factorial.factorization r := by
      rw [Nat.factorization_def n.factorial hr]
      exact (padicValNat_dvd_iff_le n.factorial_ne_zero).mp hrjfac
    have hrmem : r ∈ n.factorial.factorization.support.filter
        (fun r ↦ r % (2 * q) = 1) := by
      simp only [Finset.mem_filter, Finsupp.mem_support_iff, ne_eq]
      refine ⟨?_, hrmod⟩
      rw [Nat.factorization_def n.factorial hr]
      have hjpos : 0 < j := Nat.pos_of_ne_zero hj0
      have hjle' : j ≤ padicValNat r n.factorial :=
        (padicValNat_dvd_iff_le n.factorial_ne_zero).mp hrjfac
      exact ne_of_gt (lt_of_lt_of_le hjpos hjle')
    have hterm : r ^ n.factorial.factorization r ∣
        factorialPrimeClassPart n (2 * q) 1 := by
      exact Finset.dvd_prod_of_mem (fun r ↦ r ^ n.factorial.factorization r) hrmem
    exact (pow_dvd_pow r hjle).trans (hterm.trans (dvd_mul_left _ q))

private theorem oddPrimePowerDifference_factorial_power_bound
    {q X Y n : ℕ} (hq : q.Prime) (hqodd : Odd q)
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y)
    (heq : X ^ q - Y ^ q = n.factorial) :
    n.factorial ^ (2 * ((2 * q) * (2 * q - 1))) ≤
      q ^ (3 * ((2 * q) * (2 * q - 1))) *
        ((2 * q) * (2 * q + 1)) ^
          (3 * ((2 * q + 1) * modulusLayerExponent (2 * q) n)) := by
  let a := 2 * q
  let A := a * (a - 1)
  let T := factorialPrimeClassPart n a 1
  let E := modulusLayerExponent a n
  have hpowlt : Y ^ q < X ^ q := by
    apply Nat.sub_pos_iff_lt.mp
    rw [heq]
    exact n.factorial_pos
  have hYX : Y < X :=
    (pow_lt_pow_iff_left₀ (Nat.zero_le Y) (Nat.zero_le X) hq.ne_zero).mp hpowlt
  have hfactor := primeCyclotomicFactor_mul_sub (q := q) hYX.le
  have hfacfactor : n.factorial = primeCyclotomicFactor q X Y * (X - Y) := by
    rw [hfactor]
    exact heq.symm
  have hBfac : primeCyclotomicFactor q X Y ∣ n.factorial := by
    rw [hfacfactor]
    exact dvd_mul_right _ _
  have hBdvd : primeCyclotomicFactor q X Y ∣ q * T := by
    simpa [a, T] using
      primeCyclotomicFactor_dvd_prime_mul_factorialPrimeClassPart
        hq hqodd hYX hcop hBfac
  have hqTpos : 0 < q * T := mul_pos hq.pos (factorialPrimeClassPart_pos _ _ _)
  have hBle : primeCyclotomicFactor q X Y ≤ q * T := Nat.le_of_dvd hqTpos hBdvd
  have hsubsq := sub_sq_le_primeCyclotomicFactor hq hqodd hX (X := X) (Y := Y)
  have hfacsq : n.factorial ^ 2 ≤ (q * T) ^ 3 := by
    calc
      n.factorial ^ 2 =
          (primeCyclotomicFactor q X Y * (X - Y)) ^ 2 := by rw [hfacfactor]
      _ = primeCyclotomicFactor q X Y ^ 2 * (X - Y) ^ 2 := by rw [mul_pow]
      _ ≤ primeCyclotomicFactor q X Y ^ 2 * primeCyclotomicFactor q X Y :=
        Nat.mul_le_mul_left _ hsubsq
      _ = primeCyclotomicFactor q X Y ^ 3 := by ring
      _ ≤ (q * T) ^ 3 := Nat.pow_le_pow_left hBle 3
  have ha : 1 < a := by dsimp only [a]; have := hq.two_le; omega
  have hT := factorialPrimeClassPart_modulus_pow_product_le ha n
  change T ^ A ≤ (a * (a + 1)) ^ ((a + 1) * E) at hT
  have hTthree : T ^ (3 * A) ≤
      (a * (a + 1)) ^ (3 * ((a + 1) * E)) := by
    calc
      T ^ (3 * A) = (T ^ A) ^ 3 := by
        rw [← pow_mul]
        congr 1
        omega
      _ ≤ ((a * (a + 1)) ^ ((a + 1) * E)) ^ 3 := Nat.pow_le_pow_left hT 3
      _ = (a * (a + 1)) ^ (3 * ((a + 1) * E)) := by
        rw [← pow_mul]
        congr 1
        omega
  change n.factorial ^ (2 * A) ≤
    q ^ (3 * A) * (a * (a + 1)) ^ (3 * ((a + 1) * E))
  calc
    n.factorial ^ (2 * A) = (n.factorial ^ 2) ^ A := by rw [pow_mul]
    _ ≤ ((q * T) ^ 3) ^ A := Nat.pow_le_pow_left hfacsq A
    _ = q ^ (3 * A) * T ^ (3 * A) := by
      simp only [← pow_mul, mul_pow]
    _ ≤ q ^ (3 * A) *
        (a * (a + 1)) ^ (3 * ((a + 1) * E)) := Nat.mul_le_mul_left _ hTthree

private theorem log_eleven_lt_twelve_fifths :
    Real.log 11 < (12 : ℝ) / 5 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 11)]
  have hs := Real.sum_le_exp_of_nonneg
    (show (0 : ℝ) ≤ 12 / 5 by norm_num) 9
  have hsum : (11 : ℝ) <
      ∑ i ∈ Finset.range 9, ((12 : ℝ) / 5) ^ i / i.factorial := by
    norm_num [Nat.factorial]
  exact hsum.trans_le hs

private theorem log_nat_succ_le_six_twentyfifths {a : ℕ} (ha : 10 ≤ a) :
    Real.log (a + 1 : ℕ) ≤ (6 : ℝ) / 25 * a := by
  have hapos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hratio : (0 : ℝ) < (a + 1 : ℕ) / 11 := by positivity
  have hsplit : Real.log (a + 1 : ℕ) =
      Real.log 11 + Real.log ((a + 1 : ℕ) / 11 : ℝ) := by
    calc
      Real.log (a + 1 : ℕ) =
          Real.log ((11 : ℝ) * ((a + 1 : ℕ) / 11 : ℝ)) := by
        congr 1
        field_simp
      _ = Real.log 11 + Real.log ((a + 1 : ℕ) / 11 : ℝ) := by
        rw [Real.log_mul (by norm_num : (11 : ℝ) ≠ 0) hratio.ne']
  have hlogratio := Real.log_le_sub_one_of_pos hratio
  push_cast at hlogratio hsplit
  push_cast
  rw [hsplit]
  have hacast : (10 : ℝ) ≤ a := by exact_mod_cast ha
  nlinarith [log_eleven_lt_twelve_fifths]

private theorem two_lt_log_nat_succ {a : ℕ} (ha : 10 ≤ a) :
    (2 : ℝ) < Real.log (a + 1 : ℕ) := by
  have hlogten : (2 : ℝ) < Real.log 10 := by
    rw [Real.log_ten_eq]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hcast : (10 : ℝ) ≤ (a + 1 : ℕ) := by exact_mod_cast (by omega : 10 ≤ a + 1)
  exact hlogten.trans_le (Real.log_le_log (by norm_num) hcast)

private theorem twenty_nine_tenths_lt_log_nat {n : ℕ} (hn : 20 ≤ n) :
    (29 : ℝ) / 10 < Real.log n := by
  have hlogtwenty : (29 : ℝ) / 10 < Real.log 20 := by
    have hlog20 : Real.log 20 = 2 * Real.log 2 + Real.log 5 := by
      calc
        Real.log 20 = Real.log ((2 : ℝ) ^ 2 * 5) := by norm_num
        _ = Real.log ((2 : ℝ) ^ 2) + Real.log 5 := by
          rw [Real.log_mul (by norm_num : (2 : ℝ) ^ 2 ≠ 0) (by norm_num)]
        _ = 2 * Real.log 2 + Real.log 5 := by rw [Real.log_pow]; norm_num
    rw [hlog20]
    nlinarith [Real.log_two_gt_d9, Real.log_five_gt_d9]
  have hcast : (20 : ℝ) ≤ n := by exact_mod_cast hn
  exact hlogtwenty.trans_le (Real.log_le_log (by norm_num) hcast)

private theorem erdosOblath_odd_prime_log_inequality {q n : ℕ}
    (hq5 : 5 ≤ q) (hqn : 4 * q ≤ n) :
    3 * ((2 * q) * (2 * q - 1)) * Real.log q +
        3 * (2 * q + 1) * modulusLayerExponent (2 * q) n *
          Real.log ((2 * q) * (2 * q + 1)) <
      2 * ((2 * q) * (2 * q - 1)) * Real.log n.factorial := by
  let a := 2 * q
  let A := a * (a - 1)
  let E := modulusLayerExponent a n
  let m := n / (a + 1)
  have ha10 : 10 ≤ a := by dsimp only [a]; omega
  have hn20 : 20 ≤ n := by omega
  have hn2a : 2 * a ≤ n := by dsimp only [a]; omega
  have haR : (10 : ℝ) ≤ a := by exact_mod_cast ha10
  have hnR : (2 : ℝ) * a ≤ n := by exact_mod_cast hn2a
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have halogn_upper : Real.log (a + 1 : ℕ) ≤ (6 : ℝ) / 25 * a :=
    log_nat_succ_le_six_twentyfifths ha10
  have halogn_lower : (2 : ℝ) < Real.log (a + 1 : ℕ) :=
    two_lt_log_nat_succ ha10
  have hlogn_lower : (29 : ℝ) / 10 < Real.log n :=
    twenty_nine_tenths_lt_log_nat hn20
  have hlogn_pos : 0 < Real.log (n : ℝ) := by linarith
  have hlogn_sub_nonneg : 0 ≤ Real.log (n : ℝ) - 1 := by linarith
  have hloga_pos : (0 : ℝ) < a := by positivity
  have hloga1_pos : (0 : ℝ) < (a + 1 : ℕ) := by positivity
  have hloga_le : Real.log (a : ℝ) ≤ Real.log (a + 1 : ℕ) := by
    apply Real.log_le_log hloga_pos
    exact_mod_cast (Nat.le_succ a)
  have hlogB : Real.log (a * (a + 1) : ℕ) ≤ (12 : ℝ) / 25 * a := by
    calc
      Real.log (a * (a + 1) : ℕ) =
          Real.log (a : ℝ) + Real.log (a + 1 : ℕ) := by
        push_cast
        rw [Real.log_mul hloga_pos.ne' (by positivity : (a : ℝ) + 1 ≠ 0)]
      _ ≤ 2 * Real.log (a + 1 : ℕ) := by linarith
      _ ≤ (12 : ℝ) / 25 * a := by linarith
  have hlogB_nonneg : 0 ≤ Real.log (a * (a + 1) : ℕ) :=
    Real.log_natCast_nonneg _
  have hmpos : 0 < m := by
    dsimp only [m]
    apply Nat.div_pos
    · omega
    · omega
  have hmle : (m : ℝ) ≤ (n : ℝ) / (a + 1 : ℕ) := by
    dsimp only [m]
    exact Nat.cast_div_le
  have hlogm : Real.log (m : ℝ) ≤
      Real.log (n : ℝ) - Real.log (a + 1 : ℕ) := by
    have hmono : Real.log (m : ℝ) ≤
        Real.log ((n : ℝ) / (a + 1 : ℕ)) :=
      Real.log_le_log (Nat.cast_pos.mpr hmpos) hmle
    calc
      Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / (a + 1 : ℕ)) := hmono
      _ = Real.log (n : ℝ) - Real.log (a + 1 : ℕ) := by
        rw [Real.log_div (by positivity) hloga1_pos.ne']
  have hbracket : 1 + Real.log (m : ℝ) ≤ Real.log (n : ℝ) - 1 := by
    linarith
  have hexp := modulusLayerExponent_cast_le a n
  change (E : ℝ) ≤ (n : ℝ) * (1 + Real.log (m : ℝ)) at hexp
  have hEle : (E : ℝ) ≤ (n : ℝ) * (Real.log (n : ℝ) - 1) :=
    hexp.trans (mul_le_mul_of_nonneg_left hbracket hnnonneg)
  have hlayer :
      3 * (a + 1 : ℕ) * (E : ℝ) * Real.log (a * (a + 1) : ℕ) ≤
        (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log (n : ℝ) - 1) := by
    calc
      3 * (a + 1 : ℕ) * (E : ℝ) * Real.log (a * (a + 1) : ℕ) ≤
          3 * (a + 1 : ℕ) *
            ((n : ℝ) * (Real.log (n : ℝ) - 1)) *
              Real.log (a * (a + 1) : ℕ) := by
        gcongr
      _ ≤ 3 * (a + 1 : ℕ) *
            ((n : ℝ) * (Real.log (n : ℝ) - 1)) * ((12 : ℝ) / 25 * a) := by
        gcongr
      _ = (36 : ℝ) / 25 * a * (a + 1) * n *
            (Real.log (n : ℝ) - 1) := by
        push_cast
        ring
  have hqle : q ≤ n := by omega
  have hlogq : Real.log (q : ℝ) ≤ Real.log (n : ℝ) := by
    exact Real.log_le_log (by positivity) (by exact_mod_cast hqle)
  have hfirst : 3 * (A : ℝ) * Real.log q ≤
      3 * (A : ℝ) * Real.log n := by gcongr
  have hscale : (19 : ℝ) / 29 * Real.log n ≤ Real.log n - 1 := by
    nlinarith
  have hnl : (2 : ℝ) * a * ((19 : ℝ) / 29 * Real.log n) ≤
      (n : ℝ) * (Real.log n - 1) := by
    calc
      (2 : ℝ) * a * ((19 : ℝ) / 29 * Real.log n) ≤
          2 * a * (Real.log n - 1) := by gcongr
      _ ≤ (n : ℝ) * (Real.log n - 1) := by gcongr
  have hpoly : 0 <
      (2 : ℝ) / 25 * a * (7 * a - 43) * (2 * a * (19 / 29)) -
        3 * a * (a - 1) := by
    have ha0 : (0 : ℝ) ≤ a := by positivity
    have hprod : 0 ≤ (a : ℝ) * (a - 10) := mul_nonneg ha0 (by linarith)
    nlinarith
  have hcoef0 : 0 ≤ (2 : ℝ) / 25 * a * (7 * a - 43) := by
    have : (0 : ℝ) ≤ 7 * a - 43 := by linarith
    positivity
  have hgap : 3 * a * (a - 1) * Real.log n <
      (2 : ℝ) / 25 * a * (7 * a - 43) *
        ((n : ℝ) * (Real.log n - 1)) := by
    have hh := mul_pos hpoly hlogn_pos
    have hh2 := mul_le_mul_of_nonneg_left hnl hcoef0
    nlinarith
  have hnumeric :
      3 * a * (a - 1) * Real.log n +
          (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1) <
        2 * a * (a - 1) * n * (Real.log n - 1) := by
    calc
      3 * a * (a - 1) * Real.log n +
          (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1) <
          (2 : ℝ) / 25 * a * (7 * a - 43) * (n * (Real.log n - 1)) +
            (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1) := by
        convert add_lt_add_right hgap
          ((36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1)) using 1 <;> ring
      _ = 2 * a * (a - 1) * n * (Real.log n - 1) := by ring
  have hn0 : n ≠ 0 := by omega
  have hstirling := Stirling.le_log_factorial_stirling hn0
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlower : (n : ℝ) * (Real.log (n : ℝ) - 1) ≤ Real.log n.factorial := by
    nlinarith only [hstirling, Real.log_natCast_nonneg n, hlogtwopi_nonneg]
  have haone : 1 ≤ a := by omega
  have hAcast : (A : ℝ) = (a : ℝ) * ((a : ℝ) - 1) := by
    dsimp only [A]
    rw [Nat.cast_mul, Nat.cast_sub haone]
    norm_num
  have hfinal : 3 * (A : ℝ) * Real.log q +
      3 * (a + 1 : ℕ) * (E : ℝ) * Real.log (a * (a + 1) : ℕ) <
        2 * (A : ℝ) * Real.log n.factorial := by
    calc
      3 * (A : ℝ) * Real.log q +
          3 * (a + 1 : ℕ) * (E : ℝ) * Real.log (a * (a + 1) : ℕ) ≤
          3 * (A : ℝ) * Real.log n +
            (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1) :=
        add_le_add hfirst hlayer
      _ = 3 * a * (a - 1) * Real.log n +
            (36 : ℝ) / 25 * a * (a + 1) * n * (Real.log n - 1) := by
        dsimp only [A]
        rw [Nat.cast_mul, Nat.cast_sub haone]
        push_cast
        ring
      _ < 2 * a * (a - 1) * n * (Real.log n - 1) := hnumeric
      _ ≤ 2 * (A : ℝ) * Real.log n.factorial := by
        calc
          2 * (a : ℝ) * (a - 1) * n * (Real.log n - 1) =
              2 * (A : ℝ) * ((n : ℝ) * (Real.log n - 1)) := by
            rw [hAcast]
            ring
          _ ≤ 2 * (A : ℝ) * Real.log n.factorial :=
            mul_le_mul_of_nonneg_left hlower (by positivity)
  simpa [a, A, E, Nat.cast_sub haone] using hfinal

/-- Erdős--Obláth's odd-prime-exponent obstruction in the range used
below.  In Problem 405 the divisibility `2q ∣ n` makes the only smaller
positive range be the separately handled case `n = 2q`. -/
theorem erdosOblath_odd_prime_large {q X Y n : ℕ}
    (hq : q.Prime) (hqodd : Odd q) (hq5 : 5 ≤ q)
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y) (hqn : 4 * q ≤ n) :
    X ^ q - Y ^ q ≠ n.factorial := by
  intro heq
  let a := 2 * q
  let A := a * (a - 1)
  let E := modulusLayerExponent a n
  let B := a * (a + 1)
  have hbound := oddPrimePowerDifference_factorial_power_bound
    hq hqodd hX hY hcop heq
  change n.factorial ^ (2 * A) ≤ q ^ (3 * A) * B ^ (3 * ((a + 1) * E)) at hbound
  have hcast : ((n.factorial ^ (2 * A) : ℕ) : ℝ) ≤
      ((q ^ (3 * A) * B ^ (3 * ((a + 1) * E)) : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hfacpos : (0 : ℝ) < n.factorial := by positivity
  have hqpos : (0 : ℝ) < q := by exact_mod_cast hq.pos
  have hBpos : (0 : ℝ) < B := by
    dsimp only [B, a]
    positivity
  have hleftpos : (0 : ℝ) < ((n.factorial : ℝ) ^ (2 * A)) := by positivity
  have hlogmono : Real.log ((n.factorial : ℝ) ^ (2 * A)) ≤
      Real.log (((q : ℝ) ^ (3 * A)) * ((B : ℝ) ^ (3 * ((a + 1) * E)))) := by
    apply Real.log_le_log hleftpos
    simpa only [Nat.cast_pow, Nat.cast_mul] using hcast
  have hlogle :
      2 * (A : ℝ) * Real.log n.factorial ≤
        3 * (A : ℝ) * Real.log q +
          3 * (a + 1 : ℕ) * (E : ℝ) * Real.log B := by
    calc
      2 * (A : ℝ) * Real.log n.factorial =
          Real.log ((n.factorial : ℝ) ^ (2 * A)) := by
        rw [Real.log_pow]
        push_cast
        ring
      _ ≤ Real.log (((q : ℝ) ^ (3 * A)) *
          ((B : ℝ) ^ (3 * ((a + 1) * E)))) := hlogmono
      _ = 3 * (A : ℝ) * Real.log q +
          3 * (a + 1 : ℕ) * (E : ℝ) * Real.log B := by
        rw [Real.log_mul (pow_ne_zero _ hqpos.ne') (pow_ne_zero _ hBpos.ne'),
          Real.log_pow, Real.log_pow]
        push_cast
        ring
  have hreverse := erdosOblath_odd_prime_log_inequality hq5 hqn
  have haone : 1 ≤ a := by dsimp only [a]; omega
  have hreverse' : 3 * (A : ℝ) * Real.log q +
      3 * (a + 1 : ℕ) * (E : ℝ) * Real.log B <
        2 * (A : ℝ) * Real.log n.factorial := by
    simpa [a, A, E, B, Nat.cast_sub haone] using hreverse
  exact (not_lt_of_ge hlogle) hreverse'

private theorem factorialPrimeClassPart_self_modulus_eq_one {a : ℕ} (ha : 1 < a) :
    factorialPrimeClassPart a a 1 = 1 := by
  unfold factorialPrimeClassPart
  have hfilter : a.factorial.factorization.support.filter
      (fun r ↦ r % a = 1) = ∅ := by
    ext r
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    intro hs
    have hr : r.Prime := Nat.prime_of_mem_primeFactors hs.1
    have hrdvd : r ∣ a.factorial := Nat.dvd_of_mem_primeFactors hs.1
    have hrle : r ≤ a := (hr.dvd_factorial).mp hrdvd
    have hrmin : a + 1 ≤ r := modulus_add_one_le_of_prime_mod_one ha hr hs.2
    omega
  rw [hfilter]
  simp

private theorem erdosOblath_odd_prime_boundary {q X Y : ℕ}
    (hq : q.Prime) (hqodd : Odd q)
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y) :
    X ^ q - Y ^ q ≠ (2 * q).factorial := by
  intro heq
  have hpowlt : Y ^ q < X ^ q := by
    apply Nat.sub_pos_iff_lt.mp
    rw [heq]
    exact (2 * q).factorial_pos
  have hYX : Y < X :=
    (pow_lt_pow_iff_left₀ (Nat.zero_le Y) (Nat.zero_le X) hq.ne_zero).mp hpowlt
  have hfactor := primeCyclotomicFactor_mul_sub (q := q) hYX.le
  have hfacfactor : (2 * q).factorial =
      primeCyclotomicFactor q X Y * (X - Y) := by
    rw [hfactor]
    exact heq.symm
  have hBfac : primeCyclotomicFactor q X Y ∣ (2 * q).factorial := by
    rw [hfacfactor]
    exact dvd_mul_right _ _
  have hBdvd := primeCyclotomicFactor_dvd_prime_mul_factorialPrimeClassPart
    hq hqodd hYX hcop hBfac
  have ha : 1 < 2 * q := by
    have hq2 := hq.two_le
    omega
  rw [factorialPrimeClassPart_self_modulus_eq_one ha, mul_one] at hBdvd
  have hBle : primeCyclotomicFactor q X Y ≤ q := Nat.le_of_dvd hq.pos hBdvd
  have hsubsq := sub_sq_le_primeCyclotomicFactor hq hqodd hX (X := X) (Y := Y)
  have hfacsq : (2 * q).factorial ^ 2 ≤ q ^ 3 := by
    calc
      (2 * q).factorial ^ 2 =
          (primeCyclotomicFactor q X Y * (X - Y)) ^ 2 := by rw [hfacfactor]
      _ = primeCyclotomicFactor q X Y ^ 2 * (X - Y) ^ 2 := by rw [mul_pow]
      _ ≤ primeCyclotomicFactor q X Y ^ 2 * primeCyclotomicFactor q X Y :=
        Nat.mul_le_mul_left _ hsubsq
      _ = primeCyclotomicFactor q X Y ^ 3 := by ring
      _ ≤ q ^ 3 := Nat.pow_le_pow_left hBle 3
  have hqfac : q ≤ q.factorial := Nat.self_le_factorial q
  have hfacprod : q.factorial * q.factorial ≤ (2 * q).factorial := by
    have hdvd := Nat.factorial_mul_factorial_dvd_factorial_add q q
    have hdvd' : q.factorial * q.factorial ∣ (2 * q).factorial := by
      simpa [two_mul] using hdvd
    exact Nat.le_of_dvd (2 * q).factorial_pos hdvd'
  have hqsqfac : q ^ 2 ≤ (2 * q).factorial := by
    calc
      q ^ 2 = q * q := by ring
      _ ≤ q.factorial * q.factorial := Nat.mul_le_mul hqfac hqfac
      _ ≤ (2 * q).factorial := hfacprod
  have hqfour : q ^ 4 ≤ (2 * q).factorial ^ 2 := by
    have hsquare := Nat.pow_le_pow_left hqsqfac 2
    simpa only [← pow_mul] using hsquare
  have hqfour_three : q ^ 4 ≤ q ^ 3 := hqfour.trans hfacsq
  exact (not_lt_of_ge hqfour_three) (Nat.pow_lt_pow_right hq.one_lt (by omega))

/-! ### The sharpened cubic estimate -/

/-- The exact correction for the primes dividing the modulus six. -/
def sixProgressionCorrection (m : ℕ) : ℕ :=
  2 ^ padicValNat 2 m.factorial * 3 ^ padicValNat 3 m.factorial

private theorem factorial_dvd_sixCorrection_mul_progression (m : ℕ) :
    m.factorial ∣ sixProgressionCorrection m * arithmeticProgressionProduct 6 7 m := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  have hjle : j ≤ padicValNat r m.factorial :=
    (padicValNat_dvd_iff_le m.factorial_ne_zero).mp hrj
  by_cases hr2 : r = 2
  · subst r
    have hpow : 2 ^ j ∣ 2 ^ padicValNat 2 m.factorial := pow_dvd_pow 2 hjle
    exact hpow.trans (dvd_mul_right _ _ |>.trans (dvd_mul_right _ _))
  by_cases hr3 : r = 3
  · subst r
    have hpow : 3 ^ j ∣ 3 ^ padicValNat 3 m.factorial := pow_dvd_pow 3 hjle
    exact hpow.trans (dvd_mul_left _ _ |>.trans (dvd_mul_right _ _))
  have hr6 : ¬ r ∣ 6 := by
    intro hr6
    have hrprod : r ∣ 2 * 3 := by simpa using hr6
    rcases (hr.dvd_mul).mp hrprod with h2 | h3
    · rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h2
      · exact hr.ne_one h1
      · exact hr2 h2
    · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).mp h3 with h1 | h3
      · exact hr.ne_one h1
      · exact hr3 h3
  have hval := padicValNat_factorial_le_arithmeticProgressionProduct
    hr hr6 m (b := 7) (by norm_num) (by norm_num)
  have hAP0 : arithmeticProgressionProduct 6 7 m ≠ 0 :=
    arithmeticProgressionProduct_ne_zero (by norm_num)
  have hrjAP : r ^ j ∣ arithmeticProgressionProduct 6 7 m :=
    (padicValNat_dvd_iff_le hAP0).mpr (hjle.trans hval)
  exact hrjAP.trans (dvd_mul_left _ _)

/-- The sharpened integer quotient used only for modulus six. -/
def sixProgressionQuotient (m : ℕ) : ℕ :=
  (sixProgressionCorrection m * arithmeticProgressionProduct 6 7 m) / m.factorial

private theorem factorial_mul_sixProgressionQuotient (m : ℕ) :
    m.factorial * sixProgressionQuotient m =
      sixProgressionCorrection m * arithmeticProgressionProduct 6 7 m := by
  exact Nat.mul_div_cancel' (factorial_dvd_sixCorrection_mul_progression m)

private theorem sixProgressionQuotient_pos (m : ℕ) :
    0 < sixProgressionQuotient m := by
  have hcorrection : 0 < sixProgressionCorrection m := by
    unfold sixProgressionCorrection
    exact Nat.mul_pos (pow_pos (by norm_num) _) (pow_pos (by norm_num) _)
  have hprogression : 0 < arithmeticProgressionProduct 6 7 m :=
    Nat.pos_of_ne_zero (arithmeticProgressionProduct_ne_zero (by norm_num))
  have hright : 0 < sixProgressionCorrection m * arithmeticProgressionProduct 6 7 m :=
    Nat.mul_pos hcorrection hprogression
  have heq := factorial_mul_sixProgressionQuotient m
  by_contra hzero
  have hq0 := Nat.eq_zero_of_not_pos hzero
  rw [hq0, mul_zero] at heq
  omega

private theorem sixCorrection_sq_le (m : ℕ) :
    sixProgressionCorrection m ^ 2 ≤ 12 ^ m := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have h2val : padicValNat 2 m.factorial ≤ m := padicValNat_factorial_le 2 m
  have h3val : 2 * padicValNat 3 m.factorial ≤ m := by
    by_cases hm0 : m = 0
    · subst m
      norm_num [Nat.factorial]
    have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero 3 hm0
    norm_num at hleg ⊢
    omega
  unfold sixProgressionCorrection
  calc
    (2 ^ padicValNat 2 m.factorial * 3 ^ padicValNat 3 m.factorial) ^ 2 =
        4 ^ padicValNat 2 m.factorial * 3 ^ (2 * padicValNat 3 m.factorial) := by
      simp only [mul_pow, ← pow_mul]
      rw [show 4 ^ padicValNat 2 m.factorial =
          2 ^ (2 * padicValNat 2 m.factorial) by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul],
        show padicValNat 2 m.factorial * 2 = 2 * padicValNat 2 m.factorial by omega,
        show padicValNat 3 m.factorial * 2 = 2 * padicValNat 3 m.factorial by omega]
    _ ≤ 4 ^ m * 3 ^ m :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) h2val)
        (Nat.pow_le_pow_right (by norm_num) h3val)
    _ = 12 ^ m := by rw [← mul_pow]; norm_num

private theorem two_pow_mul_six_progression_le (m : ℕ) (hm : 1 ≤ m) :
    2 ^ m * arithmeticProgressionProduct 6 7 m ≤
      14 * 13 ^ (m - 1) * m.factorial := by
  induction m, hm using Nat.le_induction with
  | base => norm_num [arithmeticProgressionProduct, Nat.factorial]
  | succ m hm ih =>
      have hmpos : 0 < m := by omega
      rw [arithmeticProgressionProduct, Finset.prod_range_succ,
        pow_succ, Nat.factorial_succ]
      change 2 ^ m * 2 *
          ((∏ i ∈ Finset.range m, (6 * i + 7)) * (6 * m + 7)) ≤
        14 * 13 ^ (m + 1 - 1) * ((m + 1) * m.factorial)
      have hterm : 2 * (6 * m + 7) ≤ 13 * (m + 1) := by omega
      calc
        2 ^ m * 2 *
            ((∏ i ∈ Finset.range m, (6 * i + 7)) * (6 * m + 7)) =
            (2 ^ m * (∏ i ∈ Finset.range m, (6 * i + 7))) *
              (2 * (6 * m + 7)) := by ring
        _ ≤ (14 * 13 ^ (m - 1) * m.factorial) * (13 * (m + 1)) :=
          Nat.mul_le_mul ih hterm
        _ = 14 * 13 ^ (m + 1 - 1) * ((m + 1) * m.factorial) := by
          have hpow : 13 ^ (m - 1) * 13 = 13 ^ m := by
            rw [← pow_succ]
            congr 1
            omega
          rw [show m + 1 - 1 = m by omega]
          calc
            (14 * 13 ^ (m - 1) * m.factorial) * (13 * (m + 1)) =
                14 * (13 ^ (m - 1) * 13) * ((m + 1) * m.factorial) := by ring
            _ = 14 * 13 ^ m * ((m + 1) * m.factorial) := by rw [hpow]

private theorem correction_progression_sq_le_twentyfour (m : ℕ) :
    (sixProgressionCorrection m * arithmeticProgressionProduct 6 7 m) ^ 2 ≤
      (m.factorial * 24 ^ m) ^ 2 := by
  cases m with
  | zero => norm_num [sixProgressionCorrection, arithmeticProgressionProduct, Nat.factorial]
  | succ m =>
    cases m with
    | zero => norm_num [sixProgressionCorrection, arithmeticProgressionProduct, Nat.factorial]
    | succ m =>
      have hm2 : 2 ≤ m + 2 := by omega
      have hAP := two_pow_mul_six_progression_le (m + 2) (by omega)
      have hC := sixCorrection_sq_le (m + 2)
      have hnumeric :
          12 ^ (m + 2) * (14 * 13 ^ (m + 2 - 1) * (m + 2).factorial) ^ 2 ≤
            (2 ^ (m + 2)) ^ 2 * ((m + 2).factorial * 24 ^ (m + 2)) ^ 2 := by
        have hcore : 196 * 12 ^ (m + 2) * 13 ^ (2 * (m + 2 - 1)) ≤
            4 ^ (m + 2) * 24 ^ (2 * (m + 2)) := by
          clear hm2 hAP hC
          induction m with
          | zero => norm_num
          | succ m ih =>
              calc
                196 * 12 ^ (m + 1 + 2) * 13 ^ (2 * (m + 1 + 2 - 1)) =
                    (196 * 12 ^ (m + 2) * 13 ^ (2 * (m + 2 - 1))) * 2028 := by
                      rw [show m + 1 + 2 = (m + 2) + 1 by omega,
                        show 2 * (m + 1 + 2 - 1) = 2 * (m + 2 - 1) + 2 by omega,
                        pow_succ, pow_add]
                      norm_num
                      ring
                _ ≤ (4 ^ (m + 2) * 24 ^ (2 * (m + 2))) * 2028 :=
                  Nat.mul_le_mul_right 2028 ih
                _ ≤ (4 ^ (m + 2) * 24 ^ (2 * (m + 2))) * 2304 :=
                  Nat.mul_le_mul_left _ (by norm_num)
                _ = 4 ^ (m + 1 + 2) * 24 ^ (2 * (m + 1 + 2)) := by
                  rw [show m + 1 + 2 = (m + 2) + 1 by omega,
                    show 2 * (m + 1 + 2) = 2 * (m + 2) + 2 by omega,
                    pow_succ, pow_add]
                  norm_num
                  ring
        calc
          12 ^ (m + 2) * (14 * 13 ^ (m + 2 - 1) * (m + 2).factorial) ^ 2 =
              (m + 2).factorial ^ 2 *
                (196 * 12 ^ (m + 2) * 13 ^ (2 * (m + 2 - 1))) := by
                  simp only [mul_pow, ← pow_mul]
                  norm_num
                  ring
          _ ≤ (m + 2).factorial ^ 2 *
              (4 ^ (m + 2) * 24 ^ (2 * (m + 2))) :=
            Nat.mul_le_mul_left _ hcore
          _ = (2 ^ (m + 2)) ^ 2 * ((m + 2).factorial * 24 ^ (m + 2)) ^ 2 := by
            simp only [mul_pow, ← pow_mul]
            rw [show 4 ^ (m + 2) = 2 ^ (2 * (m + 2)) by
              rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul],
              show (m + 2) * 2 = 2 * (m + 2) by omega]
            ring
      have hmul : (2 ^ (m + 2)) ^ 2 *
          (sixProgressionCorrection (m + 2) * arithmeticProgressionProduct 6 7 (m + 2)) ^ 2 ≤
          (2 ^ (m + 2)) ^ 2 * ((m + 2).factorial * 24 ^ (m + 2)) ^ 2 := by
        calc
          (2 ^ (m + 2)) ^ 2 *
              (sixProgressionCorrection (m + 2) *
                arithmeticProgressionProduct 6 7 (m + 2)) ^ 2 =
              sixProgressionCorrection (m + 2) ^ 2 *
                (2 ^ (m + 2) * arithmeticProgressionProduct 6 7 (m + 2)) ^ 2 := by ring
          _ ≤ 12 ^ (m + 2) *
              (14 * 13 ^ (m + 2 - 1) * (m + 2).factorial) ^ 2 :=
            Nat.mul_le_mul hC (Nat.pow_le_pow_left hAP 2)
          _ ≤ _ := hnumeric
      exact Nat.le_of_mul_le_mul_left hmul (by positivity : 0 < (2 ^ (m + 2)) ^ 2)

private theorem sixProgressionQuotient_le (m : ℕ) :
    sixProgressionQuotient m ≤ 24 ^ m := by
  have heq := factorial_mul_sixProgressionQuotient m
  have hsquare := correction_progression_sq_le_twentyfour m
  rw [← heq] at hsquare
  have hmul : m.factorial ^ 2 * sixProgressionQuotient m ^ 2 ≤
      m.factorial ^ 2 * (24 ^ m) ^ 2 := by
    simpa [mul_pow] using hsquare
  have hsq : sixProgressionQuotient m ^ 2 ≤ (24 ^ m) ^ 2 :=
    Nat.le_of_mul_le_mul_left hmul (pow_pos m.factorial_pos 2)
  exact (Nat.pow_le_pow_iff_left (by norm_num : 2 ≠ 0)).mp hsq

private theorem primeClassPrimorial_six_dvd_step (n : ℕ) :
    primeClassPrimorial n 6 1 ∣
      primeClassPrimorial ((n - 1) / 6) 6 1 *
        sixProgressionQuotient ((n - 1) / 6) := by
  let m := (n - 1) / 6
  let S := (Finset.range (n + 1)).filter (fun r ↦ r.Prime ∧ r % 6 = 1)
  change S.prod id ∣ primeClassPrimorial m 6 1 * sixProgressionQuotient m
  have htarget_pos : 0 < primeClassPrimorial m 6 1 * sixProgressionQuotient m :=
    Nat.mul_pos (primeClassPrimorial_pos _ _ _) (sixProgressionQuotient_pos _)
  refine (Finset.prod_dvd_prod_of_subset S
    (primeClassPrimorial m 6 1 * sixProgressionQuotient m).primeFactors id ?_).trans
      (Nat.prod_primeFactors_dvd _)
  intro r hrS
  apply Nat.mem_primeFactors.mpr
  have hrmem := Finset.mem_filter.mp hrS
  have hrlt : r < n + 1 := Finset.mem_range.mp hrmem.1
  have hrle : r ≤ n := by omega
  have hrp : r.Prime := hrmem.2.1
  have hrmod : r % 6 = 1 := hrmem.2.2
  refine ⟨hrp, ?_, htarget_pos.ne'⟩
  by_cases hrm : r ≤ m
  · have hrold : r ∈ (Finset.range (m + 1)).filter (fun r ↦ r.Prime ∧ r % 6 = 1) := by
      simp only [Finset.mem_filter, Finset.mem_range]
      exact ⟨by omega, hrp, hrmod⟩
    exact (Finset.dvd_prod_of_mem id hrold).trans (dvd_mul_right _ _)
  · have hmr : m < r := Nat.lt_of_not_ge hrm
    have hrform : r = 6 * (r / 6) + 1 := by
      have hdecomp := Nat.mod_add_div r 6
      omega
    have hri : 0 < r / 6 := by
      by_contra hzero
      have hdiv0 := Nat.eq_zero_of_not_pos hzero
      rw [hdiv0, mul_zero, zero_add] at hrform
      exact hrp.ne_one hrform
    have hrdiv_le : r / 6 ≤ m := by
      apply (Nat.le_div_iff_mul_le (by norm_num : 0 < 6)).mpr
      have hmul : 6 * (r / 6) ≤ n - 1 := by omega
      simpa [Nat.mul_comm] using hmul
    let i := r / 6 - 1
    have hi : i < m := by
      dsimp only [i]
      omega
    have hterm : 6 * i + 7 = r := by
      dsimp only [i]
      have hi_eq : i + 1 = r / 6 := by omega
      calc
        6 * i + 7 = 6 * (i + 1) + 1 := by ring
        _ = 6 * (r / 6) + 1 := by rw [hi_eq]
        _ = r := hrform.symm
    have hrAP : r ∣ arithmeticProgressionProduct 6 7 m := by
      unfold arithmeticProgressionProduct
      have himem : i ∈ Finset.range m := Finset.mem_range.mpr hi
      have hdvdterm : r ∣ 6 * i + 7 := by rw [hterm]
      exact hdvdterm.trans (Finset.dvd_prod_of_mem (fun i ↦ 6 * i + 7) himem)
    have hrfac : r.Coprime m.factorial := hrp.coprime_factorial_of_lt hmr
    have hrmul : r ∣ m.factorial * sixProgressionQuotient m := by
      rw [factorial_mul_sixProgressionQuotient]
      exact hrAP.trans (dvd_mul_left _ _)
    have hrquot : r ∣ sixProgressionQuotient m := hrfac.dvd_mul_left.mp hrmul
    exact hrquot.trans (dvd_mul_left _ _)

private theorem primeClassPrimorial_six_step_le (n : ℕ) :
    primeClassPrimorial n 6 1 ≤
      primeClassPrimorial ((n - 1) / 6) 6 1 *
        sixProgressionQuotient ((n - 1) / 6) :=
  Nat.le_of_dvd
    (Nat.mul_pos (primeClassPrimorial_pos _ _ _) (sixProgressionQuotient_pos _))
    (primeClassPrimorial_six_dvd_step n)

private theorem primeClassPrimorial_six_pow_five_le (n : ℕ) :
    primeClassPrimorial n 6 1 ^ 5 ≤ 24 ^ n := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
      by_cases hn0 : n = 0
      · subst n
        have hfilter : (Finset.range (0 + 1)).filter
            (fun r ↦ r.Prime ∧ r % 6 = 1) = ∅ := by
          ext r
          simp only [Finset.mem_filter, Finset.mem_range, Finset.notMem_empty, iff_false]
          intro hr
          have hr0 : r = 0 := by omega
          subst r
          exact Nat.not_prime_zero hr.2.1
        unfold primeClassPrimorial
        rw [hfilter]
        norm_num
      let m := (n - 1) / 6
      have hm_lt : m < n := by
        change (n - 1) / 6 < n
        calc
          (n - 1) / 6 ≤ n - 1 := Nat.div_le_self _ _
          _ < n := Nat.sub_lt (Nat.pos_of_ne_zero hn0) (by omega)
      have h6m : 6 * m ≤ n := by
        dsimp only [m]
        exact (Nat.mul_div_le (n - 1) 6).trans (Nat.sub_le n 1)
      calc
        primeClassPrimorial n 6 1 ^ 5 ≤
            (primeClassPrimorial m 6 1 * sixProgressionQuotient m) ^ 5 :=
          Nat.pow_le_pow_left (by simpa [m] using primeClassPrimorial_six_step_le n) 5
        _ = primeClassPrimorial m 6 1 ^ 5 * sixProgressionQuotient m ^ 5 :=
          mul_pow _ _ _
        _ ≤ 24 ^ m * (24 ^ m) ^ 5 :=
          Nat.mul_le_mul (ih m hm_lt) (Nat.pow_le_pow_left (sixProgressionQuotient_le m) 5)
        _ = 24 ^ (6 * m) := by rw [← pow_mul, ← pow_add]; congr 1 <;> omega
        _ ≤ 24 ^ n := Nat.pow_le_pow_right (by norm_num) h6m

/-- The part of `n!` supported on primes `1 mod 6` that are at least `31`. -/
def sixLargePrimeClassPart (n : ℕ) : ℕ :=
  (n.factorial.factorization.support.filter
    (fun r ↦ r % 6 = 1 ∧ 31 ≤ r)).prod (fun r ↦ r ^ n.factorial.factorization r)

/-- The squarefree modulus-six layers, starting at the large-prime cutoff `31`. -/
def sixLargePrimeClassLayerProduct (n : ℕ) : ℕ :=
  (Finset.Icc 1 (n / 31)).prod (fun s ↦ primeClassPrimorial (n / s) 6 1)

private theorem sixLargePrimeClassLayerProduct_pos (n : ℕ) :
    0 < sixLargePrimeClassLayerProduct n := by
  exact Finset.prod_pos fun s hs ↦ primeClassPrimorial_pos _ _ _

private theorem prime_pow_divides_sixLargePrimeClassLayerProduct
    {r n : ℕ} (hr : r.Prime) (hrmod : r % 6 = 1) (hr31 : 31 ≤ r) :
    r ^ (n / r) ∣ sixLargePrimeClassLayerProduct n := by
  let u := n / r
  have hu_bound : u ≤ n / 31 := Nat.div_le_div_left hr31 (by norm_num)
  have hsubset : Finset.Icc 1 u ⊆ Finset.Icc 1 (n / 31) := by
    intro s hs
    exact Finset.mem_Icc.mpr ⟨(Finset.mem_Icc.mp hs).1,
      (Finset.mem_Icc.mp hs).2.trans hu_bound⟩
  have hpoint : ∀ s ∈ Finset.Icc 1 u,
      r ∣ primeClassPrimorial (n / s) 6 1 := by
    intro s hs
    have hsdata := Finset.mem_Icc.mp hs
    have hspos : 0 < s := lt_of_lt_of_le zero_lt_one hsdata.1
    have hrsn : r * s ≤ n := by
      have hu_mul : r * u ≤ n := Nat.mul_div_le n r
      exact (Nat.mul_le_mul_left r hsdata.2).trans hu_mul
    have hrle : r ≤ n / s := (Nat.le_div_iff_mul_le hspos).mpr hrsn
    unfold primeClassPrimorial
    apply Finset.dvd_prod_of_mem id
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨by omega, hr, hrmod⟩
  calc
    r ^ u = (Finset.Icc 1 u).prod (fun _ ↦ r) := by simp
    _ ∣ (Finset.Icc 1 u).prod (fun s ↦ primeClassPrimorial (n / s) 6 1) :=
      Finset.prod_dvd_prod_of_dvd _ _ hpoint
    _ ∣ (Finset.Icc 1 (n / 31)).prod
        (fun s ↦ primeClassPrimorial (n / s) 6 1) :=
      Finset.prod_dvd_prod_of_subset _ _ _ hsubset

private theorem thirty_mul_factorialVal_le_thirtyone_mul_div
    {r n : ℕ} (hr : r.Prime) (hr31 : 31 ≤ r) :
    30 * padicValNat r n.factorial ≤ 31 * (n / r) := by
  let _ : Fact r.Prime := ⟨hr⟩
  let u := n / r
  have hvalfac : padicValNat r n.factorial = padicValNat r u.factorial + u := by
    calc
      padicValNat r n.factorial = padicValNat r (r * u).factorial := by
        simpa [u] using (padicValNat_mul_div_factorial (p := r) n).symm
      _ = padicValNat r u.factorial + u := padicValNat_factorial_mul u
  have htail : 30 * padicValNat r u.factorial ≤ u := by
    by_cases hu0 : u = 0
    · have hval0 : padicValNat r u.factorial = 0 := by
        rw [hu0]
        apply padicValNat.eq_zero_of_not_dvd
        simp [Nat.factorial, hr.ne_one]
      rw [hval0]
      omega
    · have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero r hu0
      have hcoef : 30 ≤ r - 1 := by omega
      nlinarith
  rw [hvalfac]
  omega

private theorem sixLargePrimeClassPart_pow_thirty_dvd_layer_pow_thirtyone
    (n : ℕ) :
    sixLargePrimeClassPart n ^ 30 ∣ sixLargePrimeClassLayerProduct n ^ 31 := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrTpow : r ∣ sixLargePrimeClassPart n ^ 30 :=
    (dvd_pow_self r hj0).trans hrj
  have hrT : r ∣ sixLargePrimeClassPart n := hr.dvd_of_dvd_pow hrTpow
  have hrdata : r % 6 = 1 ∧ 31 ≤ r := by
    unfold sixLargePrimeClassPart at hrT
    obtain ⟨s, hs, hrs⟩ := (hr.prime.dvd_finsetProd_iff
      (fun s ↦ s ^ n.factorial.factorization s)).mp hrT
    have hsdata := Finset.mem_filter.mp hs
    have hrsbase : r ∣ s := hr.dvd_of_dvd_pow hrs
    rcases (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hsdata.1)).mp hrsbase with hr1 | hrsEq
    · exact (hr.ne_one hr1).elim
    · simpa [hrsEq] using hsdata.2
  have hTfac : sixLargePrimeClassPart n ^ 30 ∣ n.factorial ^ 30 := by
    apply pow_dvd_pow_of_dvd
    unfold sixLargePrimeClassPart
    have hsub : n.factorial.factorization.support.filter
        (fun r ↦ r % 6 = 1 ∧ 31 ≤ r) ⊆ n.factorial.factorization.support :=
      Finset.filter_subset _ _
    have hprod := Finset.prod_dvd_prod_of_subset
      (n.factorial.factorization.support.filter (fun r ↦ r % 6 = 1 ∧ 31 ≤ r))
      n.factorial.factorization.support (fun r ↦ r ^ n.factorial.factorization r) hsub
    exact hprod.trans (dvd_of_eq (by
      simpa only [Finsupp.prod] using
        n.factorial.prod_factorization_pow_eq_self n.factorial_ne_zero))
  have hrjfacpow : r ^ j ∣ n.factorial ^ 30 := hrj.trans hTfac
  have hfacpow0 : n.factorial ^ 30 ≠ 0 := pow_ne_zero _ n.factorial_ne_zero
  have hjle : j ≤ 30 * padicValNat r n.factorial := by
    have hval := (padicValNat_dvd_iff_le hfacpow0).mp hrjfacpow
    simpa [padicValNat.pow] using hval
  have hvalbound := thirty_mul_factorialVal_le_thirtyone_mul_div hr hrdata.2 (n := n)
  have hjdiv : j ≤ 31 * (n / r) := hjle.trans hvalbound
  have hrlayer : r ^ (n / r) ∣ sixLargePrimeClassLayerProduct n :=
    prime_pow_divides_sixLargePrimeClassLayerProduct hr hrdata.1 hrdata.2
  have hrbig : r ^ (31 * (n / r)) ∣ sixLargePrimeClassLayerProduct n ^ 31 := by
    calc
      r ^ (31 * (n / r)) = r ^ ((n / r) * 31) := by rw [mul_comm]
      _ = (r ^ (n / r)) ^ 31 := by rw [pow_mul]
      _ ∣ sixLargePrimeClassLayerProduct n ^ 31 := pow_dvd_pow_of_dvd hrlayer 31
  exact (pow_dvd_pow r hjdiv).trans hrbig

/-- The harmonic exponent for the modulus-six layers above the cutoff `31`. -/
def sixLargeLayerExponent (n : ℕ) : ℕ :=
  ∑ s ∈ Finset.Icc 1 (n / 31), n / s

private theorem sixLargePrimeClassLayerProduct_pow_five_le (n : ℕ) :
    sixLargePrimeClassLayerProduct n ^ 5 ≤ 24 ^ sixLargeLayerExponent n := by
  unfold sixLargePrimeClassLayerProduct sixLargeLayerExponent
  calc
    ((Finset.Icc 1 (n / 31)).prod
        (fun s ↦ primeClassPrimorial (n / s) 6 1)) ^ 5 =
        (Finset.Icc 1 (n / 31)).prod
          (fun s ↦ primeClassPrimorial (n / s) 6 1 ^ 5) := by
      rw [Finset.prod_pow]
    _ ≤ (Finset.Icc 1 (n / 31)).prod (fun s ↦ 24 ^ (n / s)) := by
      apply Finset.prod_le_prod
      · intro s hs
        positivity
      · intro s hs
        exact primeClassPrimorial_six_pow_five_le (n / s)
    _ = 24 ^ ∑ s ∈ Finset.Icc 1 (n / 31), n / s :=
      Finset.prod_pow_eq_pow_sum _ _ _

private theorem sixLargePrimeClassPart_pow_one_hundred_fifty_le (n : ℕ) :
    sixLargePrimeClassPart n ^ 150 ≤ 24 ^ (31 * sixLargeLayerExponent n) := by
  have hdiv := sixLargePrimeClassPart_pow_thirty_dvd_layer_pow_thirtyone n
  have hbase : sixLargePrimeClassPart n ^ 30 ≤
      sixLargePrimeClassLayerProduct n ^ 31 :=
    Nat.le_of_dvd (pow_pos (sixLargePrimeClassLayerProduct_pos n) 31) hdiv
  calc
    sixLargePrimeClassPart n ^ 150 = (sixLargePrimeClassPart n ^ 30) ^ 5 := by
      norm_num [← pow_mul]
    _ ≤ (sixLargePrimeClassLayerProduct n ^ 31) ^ 5 := Nat.pow_le_pow_left hbase 5
    _ = (sixLargePrimeClassLayerProduct n ^ 5) ^ 31 := by simp only [← pow_mul]
    _ ≤ (24 ^ sixLargeLayerExponent n) ^ 31 :=
      Nat.pow_le_pow_left (sixLargePrimeClassLayerProduct_pow_five_le n) 31
    _ = 24 ^ (31 * sixLargeLayerExponent n) := by
      rw [← pow_mul]
      congr 1
      omega

private theorem sixLargeLayerExponent_cast_le (n : ℕ) :
    (sixLargeLayerExponent n : ℝ) ≤ n * (1 + Real.log (n / 31 : ℕ)) := by
  unfold sixLargeLayerExponent
  calc
    ((∑ s ∈ Finset.Icc 1 (n / 31), n / s : ℕ) : ℝ) =
        ∑ s ∈ Finset.Icc 1 (n / 31), ((n / s : ℕ) : ℝ) := by norm_cast
    _ ≤ ∑ s ∈ Finset.Icc 1 (n / 31), (n : ℝ) / s := by
      exact Finset.sum_le_sum fun s hs ↦ Nat.cast_div_le
    _ = (n : ℝ) * ∑ s ∈ Finset.Icc 1 (n / 31), ((s : ℝ)⁻¹) := by
      simp only [div_eq_mul_inv, Finset.mul_sum]
    _ = (n : ℝ) * (harmonic (n / 31) : ℝ) := by
      simp only [harmonic_eq_sum_Icc, Rat.cast_sum, Rat.cast_inv, Rat.cast_natCast]
    _ ≤ (n : ℝ) * (1 + Real.log (n / 31 : ℕ)) := by
      exact mul_le_mul_of_nonneg_left (harmonic_le_one_add_log (n / 31))
        (Nat.cast_nonneg n)

/-- The three prime factors below `31` that are `1 mod 6`. -/
def sixSmallPrimeClassPart (n : ℕ) : ℕ :=
  7 ^ n.factorial.factorization 7 *
    13 ^ n.factorial.factorization 13 *
      19 ^ n.factorial.factorization 19

private theorem prime_mod_six_one_lt_thirtyone {r : ℕ}
    (hr : r.Prime) (hrmod : r % 6 = 1) (hr31 : r < 31) :
    r = 7 ∨ r = 13 ∨ r = 19 := by
  interval_cases r <;> norm_num at *

private theorem factorialPrimeClassPart_six_dvd_small_mul_large (n : ℕ) :
    factorialPrimeClassPart n 6 1 ∣
      sixSmallPrimeClassPart n * sixLargePrimeClassPart n := by
  rw [Nat.dvd_iff_prime_pow_dvd_dvd]
  intro r j hr hrj
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hj0 : j = 0
  · subst j
    simp
  have hrTpow : r ∣ factorialPrimeClassPart n 6 1 := by
    exact (dvd_pow_self r hj0).trans hrj
  have hrmod : r % 6 = 1 := by
    unfold factorialPrimeClassPart at hrTpow
    obtain ⟨s, hs, hrs⟩ := (hr.prime.dvd_finsetProd_iff
      (fun s ↦ s ^ n.factorial.factorization s)).mp hrTpow
    have hsdata := Finset.mem_filter.mp hs
    have hrsbase : r ∣ s := hr.dvd_of_dvd_pow hrs
    rcases (Nat.dvd_prime (Nat.prime_of_mem_primeFactors hsdata.1)).mp hrsbase with hr1 | hrsEq
    · exact (hr.ne_one hr1).elim
    · simpa [hrsEq] using hsdata.2
  have hTfac : factorialPrimeClassPart n 6 1 ∣ n.factorial :=
    factorialPrimeClassPart_dvd_factorial n 6 1
  have hrjfac : r ^ j ∣ n.factorial := hrj.trans hTfac
  have hjle : j ≤ n.factorial.factorization r := by
    rw [n.factorial.factorization_def hr]
    exact (padicValNat_dvd_iff_le n.factorial_ne_zero).mp hrjfac
  by_cases hr31 : 31 ≤ r
  · have hrmem : r ∈ n.factorial.factorization.support.filter
        (fun r ↦ r % 6 = 1 ∧ 31 ≤ r) := by
      simp only [Finset.mem_filter, Finsupp.mem_support_iff]
      refine ⟨?_, hrmod, hr31⟩
      intro hzero
      rw [hzero] at hjle
      omega
    have hrpow : r ^ j ∣ r ^ n.factorial.factorization r := pow_dvd_pow r hjle
    have hrlarge : r ^ j ∣ sixLargePrimeClassPart n := by
      unfold sixLargePrimeClassPart
      exact hrpow.trans (Finset.dvd_prod_of_mem
        (fun r ↦ r ^ n.factorial.factorization r) hrmem)
    exact hrlarge.trans (dvd_mul_left _ _)
  · have hsmall := prime_mod_six_one_lt_thirtyone hr hrmod (by omega)
    rcases hsmall with rfl | rfl | rfl
    · unfold sixSmallPrimeClassPart
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_left (pow_dvd_pow 7 hjle) _) _) _
    · unfold sixSmallPrimeClassPart
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_left
          (dvd_mul_of_dvd_right (pow_dvd_pow 13 hjle) _) _) _
    · unfold sixSmallPrimeClassPart
      exact dvd_mul_of_dvd_left
        (dvd_mul_of_dvd_right (pow_dvd_pow 19 hjle) _) _

private theorem sub_one_mul_factorialVal_le (r n : ℕ) (hr : r.Prime) :
    (r - 1) * n.factorial.factorization r ≤ n := by
  let _ : Fact r.Prime := ⟨hr⟩
  by_cases hn0 : n = 0
  · subst n
    have hz : (1 : ℕ).factorization r = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by simp [hr.ne_one])
    norm_num [Nat.factorial, hz]
  · have hleg := sub_one_mul_padicValNat_factorial_lt_of_ne_zero r hn0
    rw [n.factorial.factorization_def hr]
    exact hleg.le

private theorem sixSmallPrimeClassPart_pow_thirtysix_le (n : ℕ) :
    sixSmallPrimeClassPart n ^ 36 ≤ 2 ^ (40 * n) := by
  have h7 : 6 * n.factorial.factorization 7 ≤ n := by
    simpa using sub_one_mul_factorialVal_le 7 n (by norm_num)
  have h13 : 12 * n.factorial.factorization 13 ≤ n := by
    simpa using sub_one_mul_factorialVal_le 13 n (by norm_num)
  have h19 : 18 * n.factorial.factorization 19 ≤ n := by
    simpa using sub_one_mul_factorialVal_le 19 n (by norm_num)
  have h7e : n.factorial.factorization 7 * 36 ≤ 6 * n := by nlinarith
  have h13e : n.factorial.factorization 13 * 36 ≤ 3 * n := by nlinarith
  have h19e : n.factorial.factorization 19 * 36 ≤ 2 * n := by nlinarith
  unfold sixSmallPrimeClassPart
  calc
    (7 ^ n.factorial.factorization 7 * 13 ^ n.factorial.factorization 13 *
        19 ^ n.factorial.factorization 19) ^ 36 =
        7 ^ (n.factorial.factorization 7 * 36) *
          13 ^ (n.factorial.factorization 13 * 36) *
            19 ^ (n.factorial.factorization 19 * 36) := by
      simp only [mul_pow, ← pow_mul]
    _ ≤ 7 ^ (6 * n) * 13 ^ (3 * n) * 19 ^ (2 * n) :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.pow_le_pow_right (by norm_num) h7e)
        (Nat.pow_le_pow_right (by norm_num) h13e))
        (Nat.pow_le_pow_right (by norm_num) h19e)
    _ ≤ 8 ^ (6 * n) * 16 ^ (3 * n) * 32 ^ (2 * n) :=
      Nat.mul_le_mul (Nat.mul_le_mul
        (Nat.pow_le_pow_left (by norm_num) _)
        (Nat.pow_le_pow_left (by norm_num) _))
        (Nat.pow_le_pow_left (by norm_num) _)
    _ = 2 ^ (40 * n) := by
      rw [show (8 : ℕ) = 2 ^ 3 by norm_num,
        show (16 : ℕ) = 2 ^ 4 by norm_num,
        show (32 : ℕ) = 2 ^ 5 by norm_num,
        ← pow_mul, ← pow_mul, ← pow_mul, ← pow_add, ← pow_add]
      congr 1
      omega

private theorem factorialPrimeClassPart_six_pow_nine_hundred_le (n : ℕ) :
    factorialPrimeClassPart n 6 1 ^ 900 ≤
      2 ^ (1000 * n) * 24 ^ (186 * sixLargeLayerExponent n) := by
  have hfactor := Nat.le_of_dvd
    (Nat.mul_pos (by
      unfold sixSmallPrimeClassPart
      positivity) (by
      unfold sixLargePrimeClassPart
      exact Finset.prod_pos fun r hr ↦ pow_pos (Nat.pos_of_mem_primeFactors
        (Finset.mem_filter.mp hr).1) _))
    (factorialPrimeClassPart_six_dvd_small_mul_large n)
  have hsmall := sixSmallPrimeClassPart_pow_thirtysix_le n
  have hlarge := sixLargePrimeClassPart_pow_one_hundred_fifty_le n
  calc
    factorialPrimeClassPart n 6 1 ^ 900 ≤
        (sixSmallPrimeClassPart n * sixLargePrimeClassPart n) ^ 900 :=
      Nat.pow_le_pow_left hfactor 900
    _ = (sixSmallPrimeClassPart n ^ 36) ^ 25 *
        (sixLargePrimeClassPart n ^ 150) ^ 6 := by
      simp only [mul_pow, ← pow_mul]
    _ ≤ (2 ^ (40 * n)) ^ 25 *
        (24 ^ (31 * sixLargeLayerExponent n)) ^ 6 :=
      Nat.mul_le_mul (Nat.pow_le_pow_left hsmall 25) (Nat.pow_le_pow_left hlarge 6)
    _ = 2 ^ (1000 * n) * 24 ^ (186 * sixLargeLayerExponent n) := by
      simp only [← pow_mul]
      congr 2 <;> omega

private theorem erdosOblath_cubic_log_inequality {n : ℕ} (hn : 31 ≤ n) :
    900 * Real.log 3 + 1000 * n * Real.log 2 +
        186 * sixLargeLayerExponent n * Real.log 24 <
      600 * Real.log n.factorial := by
  let E := sixLargeLayerExponent n
  let m := n / 31
  have hn0 : n ≠ 0 := by omega
  have hnR : (31 : ℝ) ≤ n := by exact_mod_cast hn
  have hnnonneg : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hlogtwo_hi : Real.log 2 < (7 : ℝ) / 10 := by
    nlinarith [Real.log_two_lt_d9]
  have hlogthree_hi : Real.log 3 < (11 : ℝ) / 10 := by
    nlinarith [Real.log_three_lt_d9]
  have hlogtwentyfour : Real.log 24 < (16 : ℝ) / 5 := by
    have hlog24 : Real.log 24 = Real.log 3 + 3 * Real.log 2 := by
      calc
        Real.log 24 = Real.log ((3 : ℝ) * 2 ^ 3) := by norm_num
        _ = Real.log 3 + Real.log (2 ^ 3) := by
          rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num)]
        _ = Real.log 3 + 3 * Real.log 2 := by rw [Real.log_pow]; norm_num
    rw [hlog24]
    linarith
  have hlogthirtyone : (17 : ℝ) / 5 < Real.log 31 := by
    have hlogthirty : (17 : ℝ) / 5 < Real.log 30 := by
      have hlog30 : Real.log 30 = Real.log 3 + Real.log 10 := by
        calc
          Real.log 30 = Real.log ((3 : ℝ) * 10) := by norm_num
          _ = Real.log 3 + Real.log 10 := by
            rw [Real.log_mul (by norm_num : (3 : ℝ) ≠ 0) (by norm_num)]
      rw [hlog30, Real.log_ten_eq]
      nlinarith [Real.log_three_gt_d9, Real.log_two_gt_d9, Real.log_five_gt_d9]
    exact hlogthirty.trans_le (Real.log_le_log (by norm_num) (by norm_num))
  have hmpos : 0 < m := by
    dsimp only [m]
    exact Nat.div_pos hn (by norm_num)
  have hmle : (m : ℝ) ≤ (n : ℝ) / 31 := by
    dsimp only [m]
    exact Nat.cast_div_le
  have hlogm : Real.log (m : ℝ) ≤ Real.log (n : ℝ) - Real.log 31 := by
    have hmono : Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / 31) :=
      Real.log_le_log (Nat.cast_pos.mpr hmpos) hmle
    calc
      Real.log (m : ℝ) ≤ Real.log ((n : ℝ) / 31) := hmono
      _ = Real.log (n : ℝ) - Real.log 31 := by
        rw [Real.log_div (by positivity) (by norm_num)]
  have hbracket : 1 + Real.log (m : ℝ) ≤ Real.log (n : ℝ) - 12 / 5 := by
    linarith
  have hlogn_lower : (17 : ℝ) / 5 < Real.log n := by
    have hcast : (31 : ℝ) ≤ n := by exact_mod_cast hn
    exact hlogthirtyone.trans_le (Real.log_le_log (by norm_num) hcast)
  have hbracket_nonneg : 0 ≤ Real.log (n : ℝ) - 12 / 5 := by linarith
  have hexp := sixLargeLayerExponent_cast_le n
  change (E : ℝ) ≤ (n : ℝ) * (1 + Real.log (m : ℝ)) at hexp
  have hEle : (E : ℝ) ≤ (n : ℝ) * (Real.log (n : ℝ) - 12 / 5) :=
    hexp.trans (mul_le_mul_of_nonneg_left hbracket hnnonneg)
  have hlayer : 186 * (E : ℝ) * Real.log 24 ≤
      (2976 : ℝ) / 5 * n * (Real.log (n : ℝ) - 12 / 5) := by
    calc
      186 * (E : ℝ) * Real.log 24 ≤
          186 * ((n : ℝ) * (Real.log (n : ℝ) - 12 / 5)) * Real.log 24 := by
        gcongr
      _ ≤ 186 * ((n : ℝ) * (Real.log (n : ℝ) - 12 / 5)) * (16 / 5) := by
        gcongr
      _ = (2976 : ℝ) / 5 * n * (Real.log (n : ℝ) - 12 / 5) := by ring
  have hstirling := Stirling.le_log_factorial_stirling hn0
  have hlogtwopi_nonneg : 0 ≤ Real.log (2 * Real.pi) :=
    Real.log_nonneg (by nlinarith [Real.pi_gt_three])
  have hlower : (n : ℝ) * (Real.log (n : ℝ) - 1) ≤ Real.log n.factorial := by
    nlinarith only [hstirling, Real.log_natCast_nonneg n, hlogtwopi_nonneg]
  have hnlog : (17 : ℝ) / 5 * n ≤ n * Real.log n := by
    simpa [mul_comm] using mul_le_mul_of_nonneg_left hlogn_lower.le hnnonneg
  calc
    900 * Real.log 3 + 1000 * n * Real.log 2 + 186 * (E : ℝ) * Real.log 24 <
        990 + 700 * n +
          (2976 : ℝ) / 5 * n * (Real.log (n : ℝ) - 12 / 5) := by
      nlinarith
    _ < 600 * n * (Real.log (n : ℝ) - 1) := by
      nlinarith
    _ ≤ 600 * Real.log n.factorial := by nlinarith

/-- Erdős--Obláth's cubic obstruction above the explicit cutoff. -/
theorem erdosOblath_cubic_large {X Y n : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y) (hn : 31 ≤ n) :
    X ^ 3 - Y ^ 3 ≠ n.factorial := by
  intro heq
  let T := factorialPrimeClassPart n 6 1
  let E := sixLargeLayerExponent n
  have hpowlt : Y ^ 3 < X ^ 3 := by
    apply Nat.sub_pos_iff_lt.mp
    rw [heq]
    exact n.factorial_pos
  have hYX : Y < X :=
    (pow_lt_pow_iff_left₀ (Nat.zero_le Y) (Nat.zero_le X) (by norm_num : 3 ≠ 0)).mp hpowlt
  have hfactor := primeCyclotomicFactor_mul_sub (q := 3) hYX.le
  have hfacfactor : n.factorial = primeCyclotomicFactor 3 X Y * (X - Y) := by
    rw [hfactor]
    exact heq.symm
  have hBfac : primeCyclotomicFactor 3 X Y ∣ n.factorial := by
    rw [hfacfactor]
    exact dvd_mul_right _ _
  have hBdvd : primeCyclotomicFactor 3 X Y ∣ 3 * T := by
    simpa [T] using primeCyclotomicFactor_dvd_prime_mul_factorialPrimeClassPart
      (by norm_num : Nat.Prime 3) (by norm_num : Odd 3) hYX hcop hBfac
  have hBle : primeCyclotomicFactor 3 X Y ≤ 3 * T :=
    Nat.le_of_dvd (Nat.mul_pos (by norm_num) (factorialPrimeClassPart_pos _ _ _)) hBdvd
  have hsubsq := sub_sq_le_primeCyclotomicFactor
    (by norm_num : Nat.Prime 3) (by norm_num : Odd 3) hX (X := X) (Y := Y)
  have hfacsq : n.factorial ^ 2 ≤ (3 * T) ^ 3 := by
    calc
      n.factorial ^ 2 = (primeCyclotomicFactor 3 X Y * (X - Y)) ^ 2 := by rw [hfacfactor]
      _ = primeCyclotomicFactor 3 X Y ^ 2 * (X - Y) ^ 2 := by rw [mul_pow]
      _ ≤ primeCyclotomicFactor 3 X Y ^ 2 * primeCyclotomicFactor 3 X Y :=
        Nat.mul_le_mul_left _ hsubsq
      _ = primeCyclotomicFactor 3 X Y ^ 3 := by ring
      _ ≤ (3 * T) ^ 3 := Nat.pow_le_pow_left hBle 3
  have hT := factorialPrimeClassPart_six_pow_nine_hundred_le n
  change T ^ 900 ≤ 2 ^ (1000 * n) * 24 ^ (186 * E) at hT
  have hbound : n.factorial ^ 600 ≤
      3 ^ 900 * (2 ^ (1000 * n) * 24 ^ (186 * E)) := by
    calc
      n.factorial ^ 600 = (n.factorial ^ 2) ^ 300 := by rw [← pow_mul]
      _ ≤ ((3 * T) ^ 3) ^ 300 := Nat.pow_le_pow_left hfacsq 300
      _ = 3 ^ 900 * T ^ 900 := by simp only [← pow_mul, mul_pow]
      _ ≤ 3 ^ 900 * (2 ^ (1000 * n) * 24 ^ (186 * E)) := Nat.mul_le_mul_left _ hT
  have hcast : (((n.factorial : ℕ) ^ 600 : ℕ) : ℝ) ≤
      ((3 ^ 900 * (2 ^ (1000 * n) * 24 ^ (186 * E)) : ℕ) : ℝ) := by
    exact_mod_cast hbound
  have hlogmono : Real.log ((n.factorial : ℝ) ^ 600) ≤
      Real.log (((3 : ℝ) ^ 900) *
        (((2 : ℝ) ^ (1000 * n)) * ((24 : ℝ) ^ (186 * E)))) := by
    apply Real.log_le_log (by positivity)
    simpa only [Nat.cast_pow, Nat.cast_mul, Nat.cast_ofNat] using hcast
  have hlogle : 600 * Real.log n.factorial ≤
      900 * Real.log 3 + 1000 * n * Real.log 2 + 186 * E * Real.log 24 := by
    calc
      600 * Real.log n.factorial = Real.log ((n.factorial : ℝ) ^ 600) := by
        rw [Real.log_pow]
        norm_num
      _ ≤ Real.log (((3 : ℝ) ^ 900) *
          (((2 : ℝ) ^ (1000 * n)) * ((24 : ℝ) ^ (186 * E)))) := hlogmono
      _ = 900 * Real.log 3 + 1000 * n * Real.log 2 + 186 * E * Real.log 24 := by
        rw [Real.log_mul (by positivity) (by positivity),
          Real.log_mul (by positivity) (by positivity), Real.log_pow, Real.log_pow, Real.log_pow]
        push_cast
        ring
  have hreverse := erdosOblath_cubic_log_inequality hn
  change 900 * Real.log 3 + 1000 * n * Real.log 2 + 186 * E * Real.log 24 <
    600 * Real.log n.factorial at hreverse
  exact (not_lt_of_ge hlogle) hreverse

private theorem sixLargePrimeClassPart_eq_one_of_lt_thirtyone
    {n : ℕ} (hn : n < 31) : sixLargePrimeClassPart n = 1 := by
  unfold sixLargePrimeClassPart
  have hfilter : n.factorial.factorization.support.filter
      (fun r ↦ r % 6 = 1 ∧ 31 ≤ r) = ∅ := by
    ext r
    simp only [Finset.mem_filter, Finset.notMem_empty, iff_false]
    rintro ⟨hrsupp, hrmod, hr31⟩
    have hrp : r.Prime := Nat.prime_of_mem_primeFactors hrsupp
    have hrdvd : r ∣ n.factorial := Nat.dvd_of_mem_primeFactors hrsupp
    have hrle : r ≤ n := (hrp.dvd_factorial).mp hrdvd
    omega
  rw [hfilter]
  simp

private theorem four_pow_le_factorial_of_twelve_le {n : ℕ} (hn : 12 ≤ n) :
    4 ^ n ≤ n.factorial := by
  induction n, hn using Nat.le_induction with
  | base => norm_num [Nat.factorial]
  | succ n hn ih =>
      rw [pow_succ, Nat.factorial_succ]
      calc
        4 ^ n * 4 ≤ n.factorial * 4 := Nat.mul_le_mul_right 4 ih
        _ ≤ n.factorial * (n + 1) := Nat.mul_le_mul_left _ (by omega)
        _ = (n + 1) * n.factorial := by rw [mul_comm]

/-- The cubic obstruction in the exact divisibility range needed below. -/
theorem erdosOblath_cubic {X Y n : ℕ}
    (hX : 0 < X) (hY : 0 < Y) (hcop : X.Coprime Y)
    (hnpos : 0 < n) (h6 : 6 ∣ n) :
    X ^ 3 - Y ^ 3 ≠ n.factorial := by
  by_cases hn31 : 31 ≤ n
  · exact erdosOblath_cubic_large hX hY hcop hn31
  · intro heq
    let T := factorialPrimeClassPart n 6 1
    have hpowlt : Y ^ 3 < X ^ 3 := by
      apply Nat.sub_pos_iff_lt.mp
      rw [heq]
      exact n.factorial_pos
    have hYX : Y < X :=
      (pow_lt_pow_iff_left₀ (Nat.zero_le Y) (Nat.zero_le X) (by norm_num : 3 ≠ 0)).mp hpowlt
    have hfactor := primeCyclotomicFactor_mul_sub (q := 3) hYX.le
    have hfacfactor : n.factorial = primeCyclotomicFactor 3 X Y * (X - Y) := by
      rw [hfactor]
      exact heq.symm
    have hBfac : primeCyclotomicFactor 3 X Y ∣ n.factorial := by
      rw [hfacfactor]
      exact dvd_mul_right _ _
    have hBdvd : primeCyclotomicFactor 3 X Y ∣ 3 * T := by
      simpa [T] using primeCyclotomicFactor_dvd_prime_mul_factorialPrimeClassPart
        (by norm_num : Nat.Prime 3) (by norm_num : Odd 3) hYX hcop hBfac
    have hBle : primeCyclotomicFactor 3 X Y ≤ 3 * T :=
      Nat.le_of_dvd (Nat.mul_pos (by norm_num) (factorialPrimeClassPart_pos _ _ _)) hBdvd
    have hsubsq := sub_sq_le_primeCyclotomicFactor
      (by norm_num : Nat.Prime 3) (by norm_num : Odd 3) hX (X := X) (Y := Y)
    have hfacsq : n.factorial ^ 2 ≤ (3 * T) ^ 3 := by
      calc
        n.factorial ^ 2 = (primeCyclotomicFactor 3 X Y * (X - Y)) ^ 2 := by
          rw [hfacfactor]
        _ = primeCyclotomicFactor 3 X Y ^ 2 * (X - Y) ^ 2 := by rw [mul_pow]
        _ ≤ primeCyclotomicFactor 3 X Y ^ 2 * primeCyclotomicFactor 3 X Y :=
          Nat.mul_le_mul_left _ hsubsq
        _ = primeCyclotomicFactor 3 X Y ^ 3 := by ring
        _ ≤ (3 * T) ^ 3 := Nat.pow_le_pow_left hBle 3
    by_cases hn6 : n = 6
    · subst n
      exact (erdosOblath_odd_prime_boundary
        (by norm_num : Nat.Prime 3) (by norm_num : Odd 3) hX hY hcop) heq
    · have hn12 : 12 ≤ n := by
        rcases h6 with ⟨c, hc⟩
        have hcpos : 0 < c := by
          by_contra hc0
          have : c = 0 := Nat.eq_zero_of_not_pos hc0
          rw [this, mul_zero] at hc
          omega
        have hcne1 : c ≠ 1 := by
          intro hc1
          subst c
          apply hn6
          simpa using hc
        have hc2 : 2 ≤ c := by omega
        calc
          12 = 6 * 2 := by norm_num
          _ ≤ 6 * c := Nat.mul_le_mul_left 6 hc2
          _ = n := hc.symm
      have hlarge : sixLargePrimeClassPart n = 1 :=
        sixLargePrimeClassPart_eq_one_of_lt_thirtyone (by omega)
      have hTdiv := factorialPrimeClassPart_six_dvd_small_mul_large n
      change T ∣ sixSmallPrimeClassPart n * sixLargePrimeClassPart n at hTdiv
      rw [hlarge, mul_one] at hTdiv
      have hsmallpos : 0 < sixSmallPrimeClassPart n := by
        unfold sixSmallPrimeClassPart
        positivity
      have hTle : T ≤ sixSmallPrimeClassPart n := Nat.le_of_dvd hsmallpos hTdiv
      have hsmall := sixSmallPrimeClassPart_pow_thirtysix_le n
      have hTpow : T ^ 36 ≤ 2 ^ (40 * n) :=
        (Nat.pow_le_pow_left hTle 36).trans hsmall
      have hupper : n.factorial ^ 24 ≤ 3 ^ 36 * 2 ^ (40 * n) := by
        calc
          n.factorial ^ 24 = (n.factorial ^ 2) ^ 12 := by rw [← pow_mul]
          _ ≤ ((3 * T) ^ 3) ^ 12 := Nat.pow_le_pow_left hfacsq 12
          _ = 3 ^ 36 * T ^ 36 := by simp only [← pow_mul, mul_pow]
          _ ≤ 3 ^ 36 * 2 ^ (40 * n) := Nat.mul_le_mul_left _ hTpow
      have hfour := four_pow_le_factorial_of_twelve_le hn12
      have hlower : 4 ^ (24 * n) ≤ n.factorial ^ 24 := by
        have hp := Nat.pow_le_pow_left hfour 24
        simpa only [← pow_mul, Nat.mul_comm] using hp
      have hnumeric : 3 ^ 36 * 2 ^ (40 * n) < 4 ^ (24 * n) := by
        calc
          3 ^ 36 * 2 ^ (40 * n) < 4 ^ 36 * 2 ^ (40 * n) := by
            exact Nat.mul_lt_mul_of_pos_right
              (Nat.pow_lt_pow_left (by norm_num : 3 < 4) (by norm_num : 36 ≠ 0))
              (pow_pos (by norm_num) _)
          _ = 2 ^ (72 + 40 * n) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_add]
          _ < 2 ^ (48 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
          _ = 4 ^ (24 * n) := by
            rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_mul]
            congr 1
            omega
      exact (not_lt_of_ge (hlower.trans hupper)) hnumeric

end ErdosOblath

/-! ## Assembly of the exact classification -/

/-- Every positive-integer solution is one of the three exceptional triples. -/
theorem IsSolution.eq_exceptional {p a k : ℕ} (h : IsSolution p a k) :
    (p = 3 ∧ a = 1 ∧ k = 1) ∨
      (p = 3 ∧ a = 5 ∧ k = 3) ∨
      (p = 5 ∧ a = 1 ∧ k = 2) := by
  by_cases ha1 : a = 1
  · rcases h.eq_small_of_a_eq_one ha1 with h3 | h5
    · exact Or.inl ⟨h3.1, ha1, h3.2⟩
    · exact Or.inr (Or.inr ⟨h5.1, ha1, h5.2⟩)
  by_cases hp3 : p = 3
  · rcases h.eq_of_p_eq_three hp3 with h1 | h5
    · exact Or.inl ⟨hp3, h1.1, h1.2⟩
    · exact Or.inr (Or.inl ⟨hp3, h5.1, h5.2⟩)
  by_cases hp5 : p = 5
  · have h5 := h.eq_of_p_eq_five hp5
    exact Or.inr (Or.inr ⟨hp5, h5.1, h5.2⟩)
  by_cases hp17 : p = 17
  · have h17 : IsSolution 17 a k := by simpa [hp17] using h
    exact (not_isSolution_seventeen_of_ne_one h17 ha1).elim
  have hpredpos : 0 < p - 1 := by have := h.prime.two_le; omega
  have h2pred : 2 ∣ p - 1 := by
    rcases h.p_odd with ⟨s, hs⟩
    refine ⟨s, ?_⟩
    omega
  by_cases hodd : ∃ q : ℕ, q.Prime ∧ Odd q ∧ q ∣ p - 1
  · obtain ⟨q, hq, hqodd, hqpred⟩ := hodd
    obtain ⟨X, Y, hX, hY, hcop, hdiff⟩ :=
      h.exists_factorial_odd_prime_power_difference ha1 hq hqodd hqpred
    have h2q : 2 * q ∣ p - 1 :=
      hqodd.coprime_two_left.mul_dvd_of_dvd_of_dvd h2pred hqpred
    by_cases hq3 : q = 3
    · subst q
      have h6 : 6 ∣ p - 1 := by simpa using h2q
      exact ((erdosOblath_cubic hX hY hcop hpredpos h6) hdiff).elim
    · have hq5 : 5 ≤ q := by
        have hq3le : 3 ≤ q := hq.odd_iff.mp hqodd
        rcases hqodd with ⟨s, hs⟩
        omega
      by_cases hboundary : p - 1 = 2 * q
      · exact ((erdosOblath_odd_prime_boundary hq hqodd hX hY hcop)
          (by simpa [hboundary] using hdiff)).elim
      · rcases h2q with ⟨c, hc⟩
        have hcpos : 0 < c := by
          by_contra hc0
          have : c = 0 := Nat.eq_zero_of_not_pos hc0
          rw [this, mul_zero] at hc
          omega
        have hcne1 : c ≠ 1 := by
          intro hc1
          subst c
          apply hboundary
          simpa using hc
        have hc2 : 2 ≤ c := by omega
        have h4q : 4 * q ≤ p - 1 := by
          calc
            4 * q = (2 * q) * 2 := by ring
            _ ≤ (2 * q) * c := Nat.mul_le_mul_left _ hc2
            _ = p - 1 := hc.symm
        exact ((erdosOblath_odd_prime_large hq hqodd hq5 hX hY hcop h4q) hdiff).elim
  · have hno : ∀ q : ℕ, q.Prime → Odd q → ¬ q ∣ p - 1 := by
      intro q hq hqodd hqpred
      exact hodd ⟨q, hq, hqodd, hqpred⟩
    obtain ⟨m, hpm⟩ := h.eq_fermatNumber_of_no_odd_prime_dvd hno
    have hm3 : 3 ≤ m := by
      by_contra hm3
      have hm2 : m ≤ 2 := by omega
      interval_cases m
      · apply hp3
        norm_num [Nat.fermatNumber] at hpm ⊢
        exact hpm
      · apply hp5
        norm_num [Nat.fermatNumber] at hpm ⊢
        exact hpm
      · apply hp17
        norm_num [Nat.fermatNumber] at hpm ⊢
        exact hpm
    obtain ⟨X, Y, hX, hY, hcop, hdiff⟩ :=
      h.exists_factorial_eighth_power_difference hm3 hpm
    have hp257 : 257 ≤ Nat.fermatNumber m := by
      have hmono := Nat.fermatNumber_mono hm3
      norm_num at hmono ⊢
      exact hmono
    have hn256 : 256 ≤ p - 1 := by rw [hpm]; omega
    exact ((erdosOblath_eighth_large hX hY hcop hn256) hdiff).elim

/-- Exact resolution of Erdős Problem 405 for odd primes. -/
theorem erdos_405 {p a k : ℕ} :
    IsSolution p a k ↔
      (p = 3 ∧ a = 1 ∧ k = 1) ∨
      (p = 3 ∧ a = 5 ∧ k = 3) ∨
      (p = 5 ∧ a = 1 ∧ k = 2) :=
  ⟨IsSolution.eq_exceptional, isSolution_of_eq_exceptional⟩

/-- Equivalently, the solution set is exactly the advertised three-element finset. -/
theorem solution_set_eq_exceptional :
    {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2} =
      (exceptionalSolutions : Set (ℕ × ℕ × ℕ)) := by
  ext t
  rcases t with ⟨p, a, k⟩
  simp [erdos_405, exceptionalSolutions]

/-- In particular, Erdős and Graham's finiteness question has an affirmative answer. -/
theorem erdos405_finite :
    Set.Finite {t : ℕ × ℕ × ℕ | IsSolution t.1 t.2.1 t.2.2} := by
  rw [solution_set_eq_exceptional]
  exact exceptionalSolutions.finite_toSet

#print axioms erdos_405

end Erdos405

alias _root_.Erdos405.erdos405_iff := _root_.Erdos405.erdos_405
