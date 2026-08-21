import ErdosProblems.Erdos228.Assembly
import ErdosProblems.Erdos228.RudinShapiro

/-!
# The even-frequency part of the BBMST construction

This file formalizes equations (3), (6), and (7), and Lemma 3.3, of
Balister--Bollobás--Morris--Sahasrabudhe--Tiba.  Frequencies are first described
in the auxiliary variable `w = exp (2 i theta)`.  Doubling their supports gives
the even frequencies of the final centered Laurent polynomial.
-/

namespace Erdos228

open scoped BigOperators ComplexConjugate

noncomputable section

/-- The large frequency shift `T = 2^(t+10)` used by BBMST. -/
def evenT (t : ℕ) : ℕ := 2 ^ (t + 10)

/-- The integer on the right side of BBMST equation (3). -/
def evenGammaNumerator (t : ℕ) : ℕ :=
  2 ^ (t + 11) + 2 ^ t - 1

/-- The arithmetic data chosen in Section 2.2 of BBMST.  Oddness is used by
the later dangerous-interval argument, while this file only needs the upper
bound on `gamma` and the exact parameter equation. -/
structure EvenParameters (n t : ℕ) (gamma : ℝ) : Prop where
  t_odd : Odd t
  gamma_pos : 0 < gamma
  gamma_le : gamma ≤ 1 / 2 ^ 40
  equation : gamma * n = evenGammaNumerator t

/-- The two blocks of frequencies before the substitution `w = exp(2 i theta)`. -/
def evenCPrime (t : ℕ) : Finset ℕ :=
  (Finset.range (2 ^ t)).image (fun j => evenT t + j) ∪
    (Finset.range (2 ^ t)).image (fun j => 2 * evenT t + j)

/-- The cosine frequencies in the original angular variable. -/
def evenC (t : ℕ) : Finset ℕ :=
  (evenCPrime t).image (fun j => 2 * j)

/-- The even frequencies not reserved for the cosine polynomial. -/
def evenSPrime (n t : ℕ) : Finset ℕ :=
  (Finset.Icc 1 n) \ evenCPrime t

/-- The remaining even frequencies in the original angular variable. -/
def evenS (n t : ℕ) : Finset ℕ :=
  (evenSPrime n t).image (fun j => 2 * j)

/-- The polynomial whose real part supplies the cosine coordinate. -/
def cosineBlockPolynomial (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroQ t

/-- The two blocks deleted from the stable Rudin--Shapiro prefix when defining
the remaining even sine coordinate.  Both blocks use `P_t`; this is the
asymmetry between equations (6) and (7) in BBMST. -/
def deletedEvenBlockPolynomial (t : ℕ) : Polynomial ℂ :=
  Polynomial.X ^ evenT t * rudinShapiroP t +
    Polynomial.X ^ (2 * evenT t) * rudinShapiroP t

/-- The stable prefix after deleting the two blocks assigned to `c`. -/
def evenRemainderPolynomial (n t u : ℕ) : Polynomial ℂ :=
  polynomialPrefix (rudinShapiroP u) (n + 1) - deletedEvenBlockPolynomial t

/-- BBMST's cosine polynomial `c(theta)`. -/
def evenCosine (t : ℕ) (theta : ℝ) : ℝ :=
  (cosineBlockPolynomial t).eval (unitPoint (2 * theta)) |>.re

/-- BBMST's remaining even sine polynomial `s_e(theta)`.  The level `u` is
any Rudin--Shapiro recursion level whose first `n+1` coefficients have
stabilized and which contains the two deleted blocks. -/
def evenSine (n t u : ℕ) (theta : ℝ) : ℝ :=
  (evenRemainderPolynomial n t u).eval (unitPoint (2 * theta)) |>.im

lemma evenT_eq_pow_mul (t : ℕ) : evenT t = 2 ^ t * 2 ^ 10 := by
  simp [evenT, pow_add]

lemma two_mul_evenT (t : ℕ) : 2 * evenT t = 2 ^ (t + 11) := by
  simp [evenT, pow_succ']

lemma evenT_add_pow_le_two_mul_evenT (t : ℕ) :
    evenT t + 2 ^ t ≤ 2 * evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma pow_le_evenT (t : ℕ) : 2 ^ t ≤ evenT t := by
  rw [evenT_eq_pow_mul]
  have hpos : 0 < 2 ^ t := by positivity
  nlinarith [show (2 ^ 10 : ℕ) = 1024 by norm_num]

lemma evenGammaNumerator_add_one (t : ℕ) :
    evenGammaNumerator t + 1 = 2 * evenT t + 2 ^ t := by
  have hp : 0 < 2 ^ (t + 11) := by positivity
  have hone : 1 ≤ 2 ^ (t + 11) := hp
  have hsum : 1 ≤ 2 ^ (t + 11) + 2 ^ t :=
    hone.trans (Nat.le_add_right _ _)
  rw [evenGammaNumerator, Nat.sub_add_cancel hsum, two_mul_evenT]

lemma EvenParameters.gamma_le_one {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : gamma ≤ 1 := by
  calc
    gamma ≤ 1 / (2 : ℝ) ^ 40 := h.gamma_le
    _ ≤ 1 := by norm_num

lemma EvenParameters.numerator_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : evenGammaNumerator t ≤ n := by
  have hnonneg : 0 ≤ (n : ℝ) := by positivity
  have hreal : (evenGammaNumerator t : ℝ) ≤ n := by
    rw [← h.equation]
    nlinarith [h.gamma_le_one]
  exact_mod_cast hreal

lemma EvenParameters.pow_t_add_eleven_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 2 ^ (t + 11) ≤ n := by
  apply le_trans _ h.numerator_le_n
  rw [evenGammaNumerator]
  have hpos : 0 < 2 ^ t := by positivity
  omega

lemma EvenParameters.five_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 5 ≤ n := by
  have hp := h.pow_t_add_eleven_le_n
  have hbase : 2 ^ 11 ≤ 2 ^ (t + 11) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  norm_num at hbase
  omega

lemma EvenParameters.pow_t_add_five_le_n {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) : 2 ^ (t + 5) ≤ n := by
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans h.pow_t_add_eleven_le_n

lemma EvenParameters.blocks_fit {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) :
    2 * evenT t + 2 ^ t ≤ n + 1 := by
  rw [← evenGammaNumerator_add_one]
  exact Nat.add_le_add_right h.numerator_le_n 1

@[simp] lemma mem_evenCPrime (t k : ℕ) :
    k ∈ evenCPrime t ↔
      (∃ j < 2 ^ t, k = evenT t + j) ∨
      ∃ j < 2 ^ t, k = 2 * evenT t + j := by
  simp [evenCPrime, eq_comm]

@[simp] lemma mem_evenC (t k : ℕ) :
    k ∈ evenC t ↔ ∃ j ∈ evenCPrime t, k = 2 * j := by
  simp [evenC, eq_comm]

@[simp] lemma mem_evenSPrime (n t k : ℕ) :
    k ∈ evenSPrime n t ↔ 1 ≤ k ∧ k ≤ n ∧ k ∉ evenCPrime t := by
  simp [evenSPrime, and_assoc]

@[simp] lemma mem_evenS (n t k : ℕ) :
    k ∈ evenS n t ↔ ∃ j ∈ evenSPrime n t, k = 2 * j := by
  simp [evenS, eq_comm]

lemma evenCPrime_subset_range {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenCPrime t ⊆ Finset.range (n + 1) := by
  intro k hk
  rw [mem_evenCPrime] at hk
  simp only [Finset.mem_range]
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  · omega

lemma evenC_subset_Icc {n t : ℕ}
    (hblock : 2 * evenT t + 2 ^ t ≤ n + 1) :
    evenC t ⊆ Finset.Icc 1 (2 * n) := by
  intro k hk
  rw [mem_evenC] at hk
  obtain ⟨j, hj, rfl⟩ := hk
  have hj' := evenCPrime_subset_range hblock hj
  simp only [Finset.mem_range] at hj'
  have hT : 0 < evenT t := by simp [evenT]
  have hjpos : 1 ≤ j := by
    rw [mem_evenCPrime] at hj
    rcases hj with ⟨r, hr, rfl⟩ | ⟨r, hr, rfl⟩ <;> omega
  simp only [Finset.mem_Icc]
  omega

lemma evenC_disjoint_evenS (n t : ℕ) : Disjoint (evenC t) (evenS n t) := by
  rw [Finset.disjoint_left]
  intro k hkC hkS
  rw [mem_evenC] at hkC
  rw [mem_evenS] at hkS
  obtain ⟨a, ha, rfl⟩ := hkC
  obtain ⟨b, hb, hab⟩ := hkS
  have : a = b := by omega
  subst b
  exact (mem_evenSPrime n t a).mp hb |>.2.2 ha

/-! ## Exact block supports -/

lemma coeff_cosineBlockPolynomial_first (t j : ℕ) (hj : j < 2 ^ t) :
    (cosineBlockPolynomial t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_cosineBlockPolynomial_second (t j : ℕ) (hj : j < 2 ^ t) :
    (cosineBlockPolynomial t).coeff (2 * evenT t + j) =
      (rudinShapiroQ t).coeff j := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rudinShapiroP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_cosineBlockPolynomial_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (cosineBlockPolynomial t).coeff k = 0 := by
  rw [cosineBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hq : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hq
        have hq' : k - 2 * evenT t < 2 ^ t := Nat.lt_of_not_ge hq
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, hq', (Nat.add_sub_of_le h2T).symm⟩
      have hp : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rudinShapiroP_eq_zero hp, coeff_rudinShapiroQ_eq_zero hq,
        zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rudinShapiroP_eq_zero
      by_contra hp
      have hp' : k - evenT t < 2 ^ t := Nat.lt_of_not_ge hp
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, hp', (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

theorem support_cosineBlockPolynomial (t : ℕ) :
    (cosineBlockPolynomial t).support = evenCPrime t := by
  ext k
  simp only [Polynomial.mem_support_iff, ne_eq, mem_evenCPrime]
  constructor
  · intro hk
    by_contra hout
    apply hk
    apply coeff_cosineBlockPolynomial_eq_zero_of_outside t k
    rwa [mem_evenCPrime]
  · intro hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_cosineBlockPolynomial_first t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num
    · rw [coeff_cosineBlockPolynomial_second t j hj]
      rcases coeff_rudinShapiroQ_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num

lemma coeff_deletedEvenBlockPolynomial_first (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlockPolynomial t).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hnot : ¬2 * evenT t ≤ evenT t + j := by
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  rw [if_pos (Nat.le_add_right _ _), if_neg hnot]
  simp

lemma coeff_deletedEvenBlockPolynomial_second (t j : ℕ) (hj : j < 2 ^ t) :
    (deletedEvenBlockPolynomial t).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  have hfirst : evenT t ≤ 2 * evenT t + j := by omega
  rw [if_pos hfirst, if_pos (Nat.le_add_right _ _)]
  have hsub : 2 * evenT t + j - evenT t = evenT t + j := by omega
  rw [hsub, coeff_rudinShapiroP_eq_zero]
  · simp
  · exact (pow_le_evenT t).trans (Nat.le_add_right _ _)

lemma coeff_deletedEvenBlockPolynomial_eq_zero_of_outside (t k : ℕ)
    (hk : k ∉ evenCPrime t) :
    (deletedEvenBlockPolynomial t).coeff k = 0 := by
  rw [deletedEvenBlockPolynomial, Polynomial.coeff_add,
    Polynomial.coeff_X_pow_mul', Polynomial.coeff_X_pow_mul']
  by_cases hT : evenT t ≤ k
  · rw [if_pos hT]
    by_cases h2T : 2 * evenT t ≤ k
    · rw [if_pos h2T]
      have hsecond : 2 ^ t ≤ k - 2 * evenT t := by
        by_contra hsecond
        apply hk
        rw [mem_evenCPrime]
        right
        exact ⟨k - 2 * evenT t, Nat.lt_of_not_ge hsecond,
          (Nat.add_sub_of_le h2T).symm⟩
      have hfirst : 2 ^ t ≤ k - evenT t := by omega
      rw [coeff_rudinShapiroP_eq_zero hfirst,
        coeff_rudinShapiroP_eq_zero hsecond, zero_add]
    · rw [if_neg h2T, add_zero]
      apply coeff_rudinShapiroP_eq_zero
      by_contra hfirst
      apply hk
      rw [mem_evenCPrime]
      left
      exact ⟨k - evenT t, Nat.lt_of_not_ge hfirst,
        (Nat.add_sub_of_le hT).symm⟩
  · rw [if_neg hT]
    have h2T : ¬2 * evenT t ≤ k := by omega
    rw [if_neg h2T, zero_add]

theorem support_deletedEvenBlockPolynomial (t : ℕ) :
    (deletedEvenBlockPolynomial t).support = evenCPrime t := by
  ext k
  simp only [Polynomial.mem_support_iff, ne_eq, mem_evenCPrime]
  constructor
  · intro hk
    by_contra hout
    apply hk
    apply coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t k
    rwa [mem_evenCPrime]
  · intro hk
    rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
    · rw [coeff_deletedEvenBlockPolynomial_first t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num
    · rw [coeff_deletedEvenBlockPolynomial_second t j hj]
      rcases coeff_rudinShapiroP_eq_one_or_neg_one hj with h | h <;>
        rw [h] <;> norm_num

/-! ## Stability of the two deleted blocks -/

/-- Once a coefficient of `P` has appeared, later Rudin--Shapiro recursion
levels leave it unchanged. -/
lemma coeff_rudinShapiroP_stable {a b k : ℕ} (hab : a ≤ b) (hk : k < 2 ^ a) :
    (rudinShapiroP b).coeff k = (rudinShapiroP a).coeff k := by
  induction b, hab using Nat.le_induction with
  | base => rfl
  | succ b hab ih =>
      have hpow : 2 ^ a ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) hab
      rw [coeff_rudinShapiroP_succ_of_lt (hk.trans_le hpow), ih]

lemma coeff_rudinShapiroQ_add_ten (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 10)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 9) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 10 = (t + 9) + 1 by omega,
    coeff_rudinShapiroQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rudinShapiroP_stable (by omega) hj

lemma coeff_rudinShapiroQ_add_eleven (t j : ℕ) (hj : j < 2 ^ t) :
    (rudinShapiroQ (t + 11)).coeff j = (rudinShapiroP t).coeff j := by
  have hpow : 2 ^ t ≤ 2 ^ (t + 10) :=
    Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [show t + 11 = (t + 10) + 1 by omega,
    coeff_rudinShapiroQ_succ_of_lt (hj.trans_le hpow)]
  exact coeff_rudinShapiroP_stable (by omega) hj

/-- At every sufficiently late recursion level, the first distinguished block
of the stable prefix is a copy of `P_t`. -/
lemma coeff_rudinShapiroP_late_first_block {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : evenT t + j < 2 ^ (t + 11) := by
    rw [← two_mul_evenT]
    have hsep := evenT_add_pow_le_two_mul_evenT t
    omega
  calc
    (rudinShapiroP u).coeff (evenT t + j) =
        (rudinShapiroP (t + 11)).coeff (evenT t + j) :=
      coeff_rudinShapiroP_stable (by omega) hindex
    _ = (rudinShapiroQ (t + 10)).coeff j := by
      simpa [evenT] using coeff_rudinShapiroP_succ_add (t + 10) j
    _ = (rudinShapiroP t).coeff j := coeff_rudinShapiroQ_add_ten t j hj

/-- The second distinguished block of the stable prefix is another copy of
`P_t`. -/
lemma coeff_rudinShapiroP_late_second_block {t u j : ℕ}
    (hu : t + 12 ≤ u) (hj : j < 2 ^ t) :
    (rudinShapiroP u).coeff (2 * evenT t + j) =
      (rudinShapiroP t).coeff j := by
  have hindex : 2 * evenT t + j < 2 ^ (t + 12) := by
    have hsmall := pow_le_evenT t
    rw [show 2 ^ (t + 12) = 2 * evenT t + 2 * evenT t by
      simp [evenT, pow_add]
      ring]
    omega
  calc
    (rudinShapiroP u).coeff (2 * evenT t + j) =
        (rudinShapiroP (t + 12)).coeff (2 * evenT t + j) :=
      coeff_rudinShapiroP_stable hu hindex
    _ = (rudinShapiroQ (t + 11)).coeff j := by
      simpa [two_mul_evenT] using coeff_rudinShapiroP_succ_add (t + 11) j
    _ = (rudinShapiroP t).coeff j := coeff_rudinShapiroQ_add_eleven t j hj

lemma coeff_rudinShapiroP_late_eq_deleted {t u k : ℕ}
    (hu : t + 12 ≤ u) (hk : k ∈ evenCPrime t) :
    (rudinShapiroP u).coeff k = (deletedEvenBlockPolynomial t).coeff k := by
  rw [mem_evenCPrime] at hk
  rcases hk with ⟨j, hj, rfl⟩ | ⟨j, hj, rfl⟩
  · rw [coeff_rudinShapiroP_late_first_block hu hj,
      coeff_deletedEvenBlockPolynomial_first t j hj]
  · rw [coeff_rudinShapiroP_late_second_block hu hj,
      coeff_deletedEvenBlockPolynomial_second t j hj]

lemma coeff_evenRemainderPolynomial_of_mem_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 0 := by
  have hkrange := evenCPrime_subset_range hblock hk
  simp only [Finset.mem_range] at hkrange
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos hkrange,
    coeff_rudinShapiroP_late_eq_deleted hu hk, sub_self]

lemma coeff_evenRemainderPolynomial_sign_of_outside {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k < n + 1)
    (hkC : k ∉ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 1 ∨
      (evenRemainderPolynomial n t u).coeff k = -1 := by
  rw [evenRemainderPolynomial, Polynomial.coeff_sub,
    coeff_polynomialPrefix, if_pos hk,
    coeff_deletedEvenBlockPolynomial_eq_zero_of_outside t k hkC, sub_zero]
  exact coeff_rudinShapiroP_eq_one_or_neg_one (hk.trans_le hprefix)

/-- Every positive frequency of the remaining even sine coordinate is a sign
exactly when it belongs to `S'_e`. -/
theorem coeff_evenRemainderPolynomial_sign_of_mem_evenSPrime {n t u k : ℕ}
    (hprefix : n + 1 ≤ 2 ^ u) (hk : k ∈ evenSPrime n t) :
    (evenRemainderPolynomial n t u).coeff k = 1 ∨
      (evenRemainderPolynomial n t u).coeff k = -1 := by
  rw [mem_evenSPrime] at hk
  exact coeff_evenRemainderPolynomial_sign_of_outside hprefix (by omega) hk.2.2

/-- On the two reserved blocks the remaining sine coefficient vanishes. -/
theorem coeff_evenRemainderPolynomial_eq_zero_on_CPrime {n t u k : ℕ}
    (hu : t + 12 ≤ u) (hblock : 2 * evenT t + 2 ^ t ≤ n + 1)
    (hk : k ∈ evenCPrime t) :
    (evenRemainderPolynomial n t u).coeff k = 0 :=
  coeff_evenRemainderPolynomial_of_mem_CPrime hu hblock hk

/-! ## Evaluation formulae -/

theorem evenCosine_eq (t : ℕ) (theta : ℝ) :
    evenCosine t theta =
      ((unitPoint (2 * theta)) ^ evenT t *
          (rudinShapiroP t).eval (unitPoint (2 * theta)) +
        (unitPoint (2 * theta)) ^ (2 * evenT t) *
          (rudinShapiroQ t).eval (unitPoint (2 * theta))).re := by
  simp [evenCosine, cosineBlockPolynomial]

theorem evenSine_eq (n t u : ℕ) (theta : ℝ) :
    evenSine n t u theta =
      ((polynomialPrefix (rudinShapiroP u) (n + 1)).eval
          (unitPoint (2 * theta)) -
        (unitPoint (2 * theta)) ^ evenT t *
          (rudinShapiroP t).eval (unitPoint (2 * theta)) -
        (unitPoint (2 * theta)) ^ (2 * evenT t) *
          (rudinShapiroP t).eval (unitPoint (2 * theta))).im := by
  simp [evenSine, evenRemainderPolynomial, deletedEvenBlockPolynomial]
  ring

/-! ## The global estimates (BBMST Lemma 3.3) -/

private lemma two_mul_sqrt_pow_le_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 3) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ Real.sqrt n := by
  have hcast : (2 ^ (t + 3) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 3) : ℝ) = 4 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 3 = (t + 1) + 2 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

/-- The cosine coordinate has the paper's `sqrt n` global bound. -/
theorem abs_evenCosine_le_sqrt (n t : ℕ)
    (hscale : 2 ^ (t + 3) ≤ n) (theta : ℝ) :
    |evenCosine t theta| ≤ Real.sqrt n := by
  let z := unitPoint (2 * theta)
  have hz : ‖z‖ = 1 := norm_unitPoint _
  have hP := norm_eval_rudinShapiroP_le t hz
  have hQ := norm_eval_rudinShapiroQ_le t hz
  rw [evenCosine_eq]
  change |(z ^ evenT t * (rudinShapiroP t).eval z +
      z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤ _
  calc
    |(z ^ evenT t * (rudinShapiroP t).eval z +
        z ^ (2 * evenT t) * (rudinShapiroQ t).eval z).re| ≤
        ‖z ^ evenT t * (rudinShapiroP t).eval z +
          z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ :=
      Complex.abs_re_le_norm _
    _ ≤ ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
        ‖z ^ (2 * evenT t) * (rudinShapiroQ t).eval z‖ := norm_add_le _ _
    _ = ‖(rudinShapiroP t).eval z‖ + ‖(rudinShapiroQ t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
    _ ≤ 2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by linarith
    _ ≤ Real.sqrt n := two_mul_sqrt_pow_le_sqrt_nat hscale

private lemma sqrt_succ_le_eleven_tenths_sqrt {n : ℕ} (hn : 5 ≤ n) :
    Real.sqrt ((n + 1 : ℕ) : ℝ) ≤ (11 / 10 : ℝ) * Real.sqrt n := by
  have hn0 : 0 ≤ (n : ℝ) := by positivity
  have hn1 : 0 ≤ ((n + 1 : ℕ) : ℝ) := by positivity
  have hs0 := Real.sq_sqrt hn0
  have hs1 := Real.sq_sqrt hn1
  have hs0n := Real.sqrt_nonneg (n : ℝ)
  have hs1n := Real.sqrt_nonneg ((n + 1 : ℕ) : ℝ)
  have hncast : (5 : ℝ) ≤ n := by exact_mod_cast hn
  norm_num only [Nat.cast_add, Nat.cast_one] at hs1
  by_contra hnot
  have hlt : ((11 / 10 : ℝ) * Real.sqrt n) ^ 2 <
      Real.sqrt ((n + 1 : ℕ) : ℝ) ^ 2 :=
    (sq_lt_sq₀ (by positivity) hs1n).2 (lt_of_not_ge hnot)
  norm_num only [Nat.cast_add, Nat.cast_one] at hlt
  have hlt' : (121 / 100 : ℝ) * n < n + 1 := by
    nlinarith [hlt, hs0, hs1]
  nlinarith

private lemma two_mul_sqrt_pow_le_half_sqrt_nat {n t : ℕ}
    (hscale : 2 ^ (t + 5) ≤ n) :
    2 * Real.sqrt (2 ^ (t + 1) : ℝ) ≤ (1 / 2 : ℝ) * Real.sqrt n := by
  have hcast : (2 ^ (t + 5) : ℝ) ≤ (n : ℝ) := by exact_mod_cast hscale
  have hpow : (2 ^ (t + 5) : ℝ) = 16 * (2 ^ (t + 1) : ℝ) := by
    rw [show t + 5 = (t + 1) + 4 by omega, pow_add]
    ring
  have hA : 0 ≤ (2 ^ (t + 1) : ℝ) := by positivity
  have hn : 0 ≤ (n : ℝ) := by positivity
  have hsA := Real.sq_sqrt hA
  have hsn := Real.sq_sqrt hn
  have hsAn := Real.sqrt_nonneg (2 ^ (t + 1) : ℝ)
  have hsnn := Real.sqrt_nonneg (n : ℝ)
  rw [hpow] at hcast
  nlinarith

/-- The remaining even sine coordinate has the paper's `6 sqrt n` global
bound.  The hypotheses are the two elementary numerical consequences of
BBMST's parameter equation and `gamma ≤ 2^-40`. -/
theorem abs_evenSine_le_six_sqrt (n t u : ℕ)
    (hprefix : n + 1 ≤ 2 ^ u) (hn : 5 ≤ n)
    (hscale : 2 ^ (t + 5) ≤ n) (theta : ℝ) :
    |evenSine n t u theta| ≤ 6 * Real.sqrt n := by
  let z := unitPoint (2 * theta)
  have hz : ‖z‖ = 1 := norm_unitPoint _
  have hpref := norm_eval_polynomialPrefix_rudinShapiroP_le u (n + 1) hprefix hz
  have hP := norm_eval_rudinShapiroP_le t hz
  rw [evenSine_eq]
  change |((polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
      z ^ evenT t * (rudinShapiroP t).eval z -
      z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤ _
  calc
    |((polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
        z ^ evenT t * (rudinShapiroP t).eval z -
        z ^ (2 * evenT t) * (rudinShapiroP t).eval z).im| ≤
        ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
          z ^ evenT t * (rudinShapiroP t).eval z -
          z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ :=
      Complex.abs_im_le_norm _
    _ ≤ ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          ‖z ^ evenT t * (rudinShapiroP t).eval z‖ +
          ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := by
      calc
        _ ≤ ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z -
              z ^ evenT t * (rudinShapiroP t).eval z‖ +
              ‖z ^ (2 * evenT t) * (rudinShapiroP t).eval z‖ := norm_sub_le _ _
        _ ≤ _ := by
          gcongr
          exact norm_sub_le _ _
    _ = ‖(polynomialPrefix (rudinShapiroP u) (n + 1)).eval z‖ +
          2 * ‖(rudinShapiroP t).eval z‖ := by
      simp [norm_mul, norm_pow, hz]
      ring
    _ ≤ 5 * Real.sqrt ((n + 1 : ℕ) : ℝ) +
          2 * Real.sqrt (2 ^ (t + 1) : ℝ) := by
      exact add_le_add hpref (mul_le_mul_of_nonneg_left hP (by norm_num))
    _ ≤ 5 * ((11 / 10 : ℝ) * Real.sqrt n) +
          (1 / 2 : ℝ) * Real.sqrt n := by
      exact add_le_add
        (mul_le_mul_of_nonneg_left (sqrt_succ_le_eleven_tenths_sqrt hn) (by norm_num))
        (two_mul_sqrt_pow_le_half_sqrt_nat hscale)
    _ = 6 * Real.sqrt n := by ring

/-- The cosine bound with all numerical input discharged by BBMST's parameter
package. -/
theorem abs_evenCosine_le_sqrt_of_parameters {n t : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) (theta : ℝ) :
    |evenCosine t theta| ≤ Real.sqrt n := by
  apply abs_evenCosine_le_sqrt n t
  exact (Nat.pow_le_pow_right (by norm_num) (by omega)).trans
    h.pow_t_add_five_le_n

/-- The even-sine bound with all BBMST numerical hypotheses discharged. -/
theorem abs_evenSine_le_six_sqrt_of_parameters {n t u : ℕ} {gamma : ℝ}
    (h : EvenParameters n t gamma) (hprefix : n + 1 ≤ 2 ^ u)
    (theta : ℝ) :
    |evenSine n t u theta| ≤ 6 * Real.sqrt n :=
  abs_evenSine_le_six_sqrt n t u hprefix h.five_le_n
    h.pow_t_add_five_le_n theta

end

end Erdos228
